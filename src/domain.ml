module F = Format

module type SET = sig
  type t

  val compare : t -> t -> int

  val pp : Format.formatter -> t -> unit
end

module type LATTICE = sig
  include SET

  val bottom : t

  val top : t

  val order : t -> t -> bool

  val join : t -> t -> t

  val meet : t -> t -> t
end

module type VALUE_DOMAIN = sig
  include LATTICE

  val of_int : int -> t

  val of_src : t

  val of_sanitizer : t

  val add : t -> t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val div : t -> t -> t

  val cmp : Llvm.Icmp.t -> t -> t -> t

  val filter : Llvm.Icmp.t -> t -> t -> t
end

module Variable : SET with type t = Llvm.llvalue = struct
  type t = Llvm.llvalue

  let compare = compare

  let pp fmt v = Utils.string_of_lhs v |> Format.fprintf fmt "%s"
end

module type MEMORY_DOMAIN = sig
  include LATTICE

  module Value : VALUE_DOMAIN

  val add : Variable.t -> Value.t -> t -> t

  val find : Variable.t -> t -> Value.t
end

module Graph = struct
  module Node = struct
    type t =
      | Atomic of Llvm.llvalue
      | Phi of Llvm.llvalue list
      | CondBranch of Llvm.llvalue * bool

    let compare = compare

    let pp fmt = function
      | Atomic instr -> Utils.string_of_instr instr |> Format.fprintf fmt "%s"
      | Phi instrs ->
          List.iter
            (fun instr ->
              Format.fprintf fmt "%s\n" (Utils.string_of_instr instr))
            instrs
      | CondBranch (instr, b) ->
          Format.fprintf fmt "%s (%s)"
            (Utils.string_of_instr instr)
            (Bool.to_string b)
  end

  let last_node current_block =
    Llvm.fold_left_blocks
      (fun labels b ->
        match Llvm.instr_end b with
        | Llvm.After instr -> (
            match Llvm.instr_opcode instr with
            | Llvm.Opcode.Br -> (
                match Llvm.get_branch instr with
                | Some (`Conditional (_, b1, b2)) ->
                    if b1 = current_block then
                      Node.CondBranch (instr, true) :: labels
                    else if b2 = current_block then
                      Node.CondBranch (instr, false) :: labels
                    else labels
                | Some (`Unconditional b) ->
                    if b = current_block then Node.Atomic instr :: labels
                    else labels
                | _ -> labels)
            | _ -> labels)
        | _ -> labels)
      []
      (Llvm.block_parent current_block)

  let rec all_prev_phi instr =
    match Llvm.instr_pred instr with
    | Llvm.After p -> all_prev_phi p @ [ instr ]
    | Llvm.At_start _ -> [ instr ]

  let rec pred node =
    match node with
    | Node.Atomic l | Node.CondBranch (l, _) -> (
        match Llvm.instr_pred l with
        | Llvm.At_start _ ->
            let current_block = Llvm.instr_parent l in
            last_node current_block
        | Llvm.After prev_instr -> (
            match Llvm.instr_opcode prev_instr with
            | Llvm.Opcode.PHI -> [ Node.Phi (all_prev_phi prev_instr) ]
            | _ -> [ Node.Atomic prev_instr ]))
    | Node.Phi (l :: _) -> pred (Node.Atomic l)
    | _ -> []
end

module type SIGN = sig
  type t = Bot | Pos | Neg | Zero | Top

  include VALUE_DOMAIN with type t := t
end

module Sign : SIGN = struct
  type t = Bot | Pos | Neg | Zero | Top

  let compare = compare

  let bottom = Bot

  let top = Top

  let of_src = failwith "Not implemented"

  let of_sanitizer = failwith "Not implemented"

  let order x y = failwith "Not implemented"

  let join x y = failwith "Not implemented"

  let meet x y = failwith "Not implemented"

  let of_int i = failwith "Not implemented"

  let add v1 v2 = failwith "Not implemented"

  let sub v1 v2 = failwith "Not implemented"

  let mul v1 v2 = failwith "Not implemented"

  let div v1 v2 = failwith "Not implemented"

  let cmp pred v1 v2 = failwith "Not implemented"

  let filter pred v1 v2 = failwith "Not implemented"

  let pp fmt = function
    | Bot -> Format.fprintf fmt "Bot"
    | Pos -> Format.fprintf fmt "Pos"
    | Neg -> Format.fprintf fmt "Neg"
    | Zero -> Format.fprintf fmt "Zero"
    | Top -> Format.fprintf fmt "Top"
end

module Taint : VALUE_DOMAIN = struct
  type t = None | Taint

  let compare = compare

  let bottom = None

  let top = Taint

  let of_int _ = failwith "Not implemented"

  let of_src = failwith "Not implemented"

  let of_sanitizer = failwith "Not implemented"

  let order x y = failwith "Not implemented"

  let join x y = failwith "Not implemented"

  let meet x y = failwith "Not implemented"

  let add x y = failwith "Not implemented"

  let sub = failwith "Not implemented"

  let mul = failwith "Not implemented"

  let div = failwith "Not implemented"

  let cmp _ = failwith "Not implemented"

  let filter pred v1 v2 = failwith "Not implemented"

  let pp fmt = function
    | None -> Format.fprintf fmt "Bot"
    | Taint -> Format.fprintf fmt "Taint"
end

module Memory (Value : VALUE_DOMAIN) :
  MEMORY_DOMAIN with type Value.t = Value.t = struct
  module M = Map.Make (Variable)
  module Value = Value

  type t = Value.t M.t

  let bottom = M.empty

  let top = M.empty (* NOTE: We do not use top *)

  let add = M.add

  let compare = compare

  let find x m = try M.find x m with Not_found -> Value.bottom

  let order m1 m2 = failwith "Not implemented"

  let join m1 m2 = failwith "Not implemented"

  let meet _ _ = failwith "NOTE: We do not use meet"

  let pp fmt m =
    M.iter (fun k v -> F.fprintf fmt "%a -> %a\n" Variable.pp k Value.pp v) m
end

module Table (M : MEMORY_DOMAIN) = struct
  include Map.Make (Graph.Node)

  let last_phi instr =
    match Llvm.instr_succ instr with
    | Llvm.Before next -> (
        match Llvm.instr_opcode next with Llvm.Opcode.PHI -> false | _ -> true)
    | _ -> true

  let init llm =
    Utils.fold_left_all_instr
      (fun table instr ->
        match Llvm.instr_opcode instr with
        | Llvm.Opcode.Br -> (
            match Llvm.get_branch instr with
            | Some (`Conditional _) ->
                table
                |> add (Graph.Node.CondBranch (instr, true)) M.bottom
                |> add (Graph.Node.CondBranch (instr, false)) M.bottom
            | _ -> add (Graph.Node.Atomic instr) M.bottom table)
        | Llvm.Opcode.PHI ->
            if last_phi instr then
              add (Graph.Node.Phi (Graph.all_prev_phi instr)) M.bottom table
            else table
        | _ -> add (Graph.Node.Atomic instr) M.bottom table)
      empty llm

  let find label tbl = try find label tbl with Not_found -> M.bottom

  let pp fmt tbl =
    iter (fun k v -> F.fprintf fmt "%a -> %a\n" Graph.Node.pp k M.pp v) tbl
end
