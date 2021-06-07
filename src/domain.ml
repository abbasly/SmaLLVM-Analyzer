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

  let of_src = Top

  let of_sanitizer = Top

  let order x y = match (x, y) with
    | Zero, Zero -> true
    | Pos, Pos -> true
    | Neg, Neg -> true
    | Bot, _ -> true
    | _, Top -> true
    | _, Bot -> false
    | Top, _ -> false
    | _ -> false

  let join x y = match (x, y) with
    | _ -> Top
    | Zero, Zero -> Zero
    | Bot, Pos -> Pos
    | Pos, Bot -> Pos
    | Pos, Pos -> Pos
    | Neg, Neg -> Neg
    | Bot, Zero -> Zero
    | Zero, Bot -> Zero
    | Neg, Bot -> Neg
    | Bot, Neg -> Neg
    | _, Top -> Top
    | Top, _ -> Top
    

  let meet x y = match (x, y) with
    | _ -> Bot
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | Pos, Pos -> Pos
    | Neg, Neg -> Neg
    | Zero, Zero -> Zero
    | Top, n -> n
    | n, Top -> n
    

  let of_int i = if i < 0 then Neg
    else if i > 0 then Pos
    else Zero

  let add v1 v2 = match (v1, v2) with
    | Zero, Zero -> Zero
    | Neg, Zero -> Neg
    | Zero, Neg -> Neg
    | Pos, Pos -> Pos
    | Neg, Neg -> Neg
    | Pos, Zero -> Pos
    | Zero, Pos -> Pos
    | _, Bot -> Bot
    | Bot, _ -> Bot
    | _ -> Top

  let sub v1 v2 = match (v1, v2) with
    | Zero, Zero -> Zero
    | Neg, Zero -> Neg
    | Zero, Neg -> Pos
    | Pos, Neg -> Pos
    | Neg, Pos -> Neg
    | Pos, Zero -> Pos
    | Zero, Pos -> Neg
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | _ -> Top

  let mul v1 v2 = match (v1, v2) with
    | _, Bot -> Bot
    | Bot, _ -> Bot
    | Zero, _ -> Zero
    | _, Zero -> Zero
    | Neg, Neg -> Pos
    | Pos, Pos -> Pos
    | Neg, Pos -> Neg
    | Pos, Neg -> Neg
    | _ -> Top

  let div v1 v2 = match (v1, v2) with
    | Neg, Neg -> Neg
    | Pos, Pos -> Pos
    | Neg, Pos -> Neg
    | Pos, Neg -> Neg
    | _, Bot -> Bot
    | Bot, _ ->  Bot
    | Zero, _ -> Zero
    | _, Zero -> Bot
    | _ -> Top

  let cmp pred v1 v2 = match pred with
    | Llvm.Icmp.Eq ->
      (match (v1, v2) with
      | Zero, Zero -> Pos
      | Pos, Pos -> Top
      | Neg, Neg -> Top
      | _, Top -> Top
      | Top, _ -> Top
      | Bot, _ -> Bot
      | _, Bot -> Bot
      | _ -> Zero)
    | Llvm.Icmp.Ne ->
      (match (v1, v2) with
      | Zero, Zero -> Zero
      | Pos, Pos -> Top
      | Neg, Neg -> Top
      | Bot, _ -> Bot
      | _, Bot -> Bot
      | Top, _ -> Top
      | _, Top -> Top
      | _ -> Pos)
    | Llvm.Icmp.Ult | Llvm.Icmp.Slt ->
      (match (v1, v2) with
      | Top, _ -> Top
      | _, Top -> Top
      | Bot, _ -> Bot
      | _, Bot -> Bot
      | Neg, Pos -> Pos
      | Neg, Neg -> Top
      | Zero, Neg -> Zero
      | Neg, Zero -> Pos
      | Zero, Zero -> Zero
      | Pos, Neg -> Zero
      | Zero, Pos -> Pos
      | Pos, Zero -> Zero
      | Pos, Pos -> Top)
    | Llvm.Icmp.Sgt ->
      (match (v1, v2) with
      | Neg, Neg -> Top
      | Pos, Pos -> Top
      | Zero, Zero -> Zero
      | Bot, _ -> Bot
      | _, Bot -> Bot
      | Top, _ -> Top
      | _, Top -> Top
      | _, Pos -> Zero
      | Zero, _ -> Pos
      | Pos, _ -> Pos
      | _, Zero -> Zero)
    | Llvm.Icmp.Ugt  ->
      (match (v1, v2) with
      | Neg, Neg -> Top
      | Pos, Pos -> Top
      | Zero, Zero -> Zero
      | Bot, _ -> Bot
      | _, Bot -> Bot
      | Top, _ -> Top
      | _, Top -> Top
      | _, Pos -> Zero
      | Zero, _ -> Pos
      | Pos, _ -> Pos
      | _, Zero -> Zero)
    | Llvm.Icmp.Uge | Llvm.Icmp.Sge ->
      (match (v1, v2) with
      | Bot, _ -> Bot
      | _, Bot -> Bot
      | Top, _ -> Top
      | _, Top -> Top
      | Neg, Pos -> Zero
      | Neg, Neg -> Top
      | Neg, Zero -> Zero
      | Zero, Pos -> Zero
      | Zero, Neg -> Pos
      | Pos, Zero -> Pos
      | Zero, Zero -> Pos
      | Pos, Pos -> Top
      | Pos, Neg -> Pos)
    
    | Llvm.Icmp.Ule | Llvm.Icmp.Sle ->
      (match (v1, v2) with
      | Top, _ -> Top
      | _, Top -> Top
      | Bot, _ -> Bot
      | _, Bot -> Bot 
      | Neg, Neg -> Top
      | Zero, Zero -> Pos
      | Zero, Pos -> Pos
      | Neg, Zero -> Pos
      | Neg, Pos -> Pos
      | Zero, Neg -> Zero
      | Pos, Zero -> Zero
      | Pos, Neg -> Zero
      | Pos, Pos -> Top)

  let filter pred v1 v2 = match pred with
    | Llvm.Icmp.Eq ->
      (match (v1, v2) with
      | Bot, _ -> Bot
      | _, Bot -> Bot
      | Neg, Pos -> Bot
      | Neg, Neg -> Neg
      | Neg, Zero -> Bot
      | Pos, Zero -> Bot
      | Neg, Top -> Neg
      | Pos, Pos -> Pos
      | Pos, Top -> Pos
      | Zero, Neg -> Bot
      | Pos, Neg -> Bot
      | Top, Pos -> Pos
      | Zero, Zero -> Zero
      | Zero, Top -> Zero
      | Zero, Pos -> Bot
      | Top, Zero -> Zero 
      | Top, Neg -> Neg
      | Top, Top -> Top
      )
    | Llvm.Icmp.Ugt | Llvm.Icmp.Sgt ->
      (match (v1, v2) with
      | _, Bot -> Bot
      | Bot, _ -> Bot
      | Neg, Pos -> Bot
      | Neg, Zero -> Bot
      
      | Neg, Neg -> Neg
      | Pos, Neg -> Pos
      | Pos, Pos -> Pos
      | Neg, Top -> Neg
      | Pos, Zero -> Pos
      | Zero, Top -> Zero
      | Top, Zero -> Pos
      | Top, Pos -> Pos
      | Pos, Top -> Pos
      | Zero, Neg -> Zero
      | Zero, Pos -> Bot
      | Zero, Zero -> Bot
      | Top, Neg -> Top
      | Top, Top -> Top
      )
    | Llvm.Icmp.Ne ->
      (match (v1, v2) with
      | Bot, _ -> Bot
      | _, Bot -> Bot
      | Neg, Pos -> Neg
      | Zero, Top -> Zero
      | Pos, Pos -> Pos
      | Pos, Top -> Pos
      | Neg, Neg -> Neg
      | Neg, Top -> Neg
      | Pos, Zero -> Pos
      | Pos, Neg -> Pos
      | Neg, Zero -> Neg
      | Zero, Neg -> Zero
      | Zero, Pos -> Zero
      | Zero, Zero -> Bot
      | Top, Neg -> Neg
      | Top, Zero -> Zero
      | Top, Pos -> Pos 
      | Top, Top -> Top
      )
    | Llvm.Icmp.Ult | Llvm.Icmp.Slt ->
      (match (v1, v2) with
      | Bot, _ -> Bot
      | _, Bot -> Bot
      | Neg, Zero -> Neg
      | Neg, Pos -> Neg
      | Zero, Zero -> Bot
      | Zero, Top -> Zero
      | Neg, Neg -> Neg
      | Pos, Zero -> Bot
      | Neg, Top -> Neg
      | Pos, Neg -> Bot
      | Pos, Pos -> Pos
      | Top, Pos -> Top
      | Top, Neg -> Neg
      | Pos, Top -> Pos
      | Zero, Neg -> Bot
      | Zero, Pos -> Zero
      | Top, Zero -> Neg
      | Top, Top -> Top
      )
    | Llvm.Icmp.Uge | Llvm.Icmp.Sge ->
      (match (v1, v2) with
      | Bot, _ -> Bot
      | _, Bot -> Bot 
      | Neg, Pos -> Bot
      | Neg, Neg -> Neg
      | Pos, Top -> Pos
      | Neg, Top -> Neg
      | Neg, Zero -> Bot
      | Pos, Pos -> Pos
      | Pos, Zero -> Pos
      | Pos, Neg -> Pos
      | Zero, Neg -> Zero
      | Zero, Pos -> Bot
      | Zero, Zero -> Zero
      | Zero, Top -> Zero
      | Top, Zero -> Top
      | Top, Pos -> Pos
      | Top, Neg -> Top
      | Top, Top -> Top
      )
    | Llvm.Icmp.Ule | Llvm.Icmp.Sle ->
      (match (v1, v2) with
      | Bot, _ -> Bot
      | _, Bot -> Bot
      | Neg, Zero -> Neg
      | Neg, Pos -> Neg
      | Neg, Neg -> Neg
      | Pos, Pos -> Pos
      | Pos, Top -> Pos
      | Neg, Top -> Neg
      | Pos, Zero -> Bot
      | Pos, Neg -> Bot
      | Top, Pos -> Top
      | Zero, Neg -> Bot
      | Zero, Zero -> Zero
      | Zero, Top -> Zero
      | Zero, Pos -> Zero
      | Top, Zero -> Top
      | Top, Neg -> Neg
      | Top, Top -> Top
      )

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

  let of_int _ = None

  let of_src = Taint

  let of_sanitizer = None

  let order x y = match (x, y) with
    | Taint, Taint -> true
    | None, None -> true
    | _ -> false

  let join x y = match (x, y) with
    | None, None -> None
    | _ -> Taint

  let meet x y = match (x, y) with
    | Taint, Taint -> Taint
    | _ -> None

  let add x y = match (x, y) with
    | None, None -> None
    | _ -> Taint

  let sub x y = match (x, y) with
    | None, None -> None
    | _ -> Taint

  let mul x y = match (x, y) with
    | None, None -> None
    | _ -> Taint

  let div x y = match (x, y) with
    | None, None -> None
    | _ -> Taint

  let cmp _ x y = match (x, y) with
    | None, None -> None
    | _ -> Taint

  let filter pred v1 v2 = v1

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

  let order m1 m2 = let bayraq = 1 in
    let neyse = M.fold (fun ky vall cntt ->
                        if Value.order vall (find ky m2) then (1*cntt)
                        else (0*cntt)
                        ) m1 bayraq in
    if neyse = 0 then false
    else 
      true

  let join m1 m2 = 
    if M.is_empty m1 then m2
      else if M.is_empty m2 then m1
      else
        let fst = M.fold (fun ky vall cntt ->
                              M.add ky (Value.join vall (find ky m2)) cntt) m1 (M.empty) in
        M.fold (fun ky vall cntt ->
                  if find ky cntt = Value.bottom then
                    M.add ky vall cntt
                  else
                    cntt) m2 fst

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
