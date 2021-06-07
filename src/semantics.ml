module D = Domain
module F = Format

module type S = sig
  module Memory : D.MEMORY_DOMAIN

  module Value : D.VALUE_DOMAIN with type t = Memory.Value.t

  val eval : Llvm.llvalue -> Memory.t -> Value.t

  val filter : Llvm.llvalue -> bool -> Memory.t -> Memory.t

  val transfer_node : Llvm.llcontext -> D.Graph.Node.t -> Memory.t -> Memory.t

  val transfer_atomic : Llvm.llcontext -> Llvm.llvalue -> Memory.t -> Memory.t

  val transfer_cond :
    Llvm.llcontext -> Llvm.llvalue -> bool -> Memory.t -> Memory.t

  val transfer_phi : Llvm.llcontext -> Llvm.llvalue list -> Memory.t -> Memory.t
end

module Make (Memory : D.MEMORY_DOMAIN) : S = struct
  exception Unsupported

  module Memory = Memory
  module Value = Memory.Value

  let eval e mem = let typee = Llvm.classify_value e in
    match typee with
    | Llvm.ValueKind.Instruction _ -> (Memory.find e mem)
    | Llvm.ValueKind.ConstantInt -> 
      let rs = Llvm.int64_of_const e in
      (match rs with
      | None -> raise Unsupported
      | Some smt -> Value.of_int (Int64.to_int smt)
      )
    | _ -> raise Unsupported

  let filter cond truth memory = let pred = Llvm.icmp_predicate cond in
    let val0 = Llvm.operand cond 0 in
    let val1 = Llvm.operand cond 1 in
    if truth then
      let a = Memory.add val0 (Value.filter (Option.get pred) (eval val0 memory) (eval val1 memory)) memory in
      Memory.add val1 (Value.filter (Utils.neg_pred (Option.get pred)) (eval val1 memory) (eval val0 memory)) a

    else
      let a = Memory.add val0 (Value.filter (Utils.neg_pred (Option.get pred)) (eval val0 memory) (eval val1 memory)) memory in
      Memory.add val1 (Value.filter (Option.get pred) (eval val1 memory) (eval val0 memory)) a

  let transfer_atomic _ instr memory = match Llvm.instr_opcode instr with
    | Llvm.Opcode.Ret -> memory
    | Llvm.Opcode.Call when Utils.is_sink instr -> memory
    | Llvm.Opcode.Call when Utils.is_print instr -> memory
    | Llvm.Opcode.Call when Utils.is_source instr -> 
      Memory.add instr (Value.of_src) memory
    | Llvm.Opcode.Call when Utils.is_llvm_intrinsic instr -> memory
    | Llvm.Opcode.Call when Utils.is_sanitizer instr -> 
      Memory.add instr (Value.of_sanitizer) memory
    | Llvm.Opcode.Sub -> 
      let first = eval (Llvm.operand instr 0) memory in
      let second = eval (Llvm.operand instr 1) memory in
      Memory.add instr (Value.sub first second) memory
    | Llvm.Opcode.Add -> 
      let first = eval (Llvm.operand instr 0) memory in
      let second = eval (Llvm.operand instr 1) memory in
      Memory.add instr (Value.add first second) memory
    | Llvm.Opcode.SDiv -> 
      let first = eval (Llvm.operand instr 0) memory in
      let second = eval (Llvm.operand instr 1) memory in
      Memory.add instr (Value.div first second) memory
    | Llvm.Opcode.UDiv -> 
      let first = eval (Llvm.operand instr 0) memory in
      let second = eval (Llvm.operand instr 1) memory in
      Memory.add instr (Value.div first second) memory
    | Llvm.Opcode.Mul -> 
      let first = eval (Llvm.operand instr 0) memory in
      let second = eval (Llvm.operand instr 1) memory in
      Memory.add instr (Value.mul first second) memory
    | Llvm.Opcode.ICmp -> 
      let cond = Llvm.icmp_predicate instr in
      (match cond with
      | Some value ->
        let left = eval (Llvm.operand instr 0) memory in
        let right = eval (Llvm.operand instr 1) memory in
        Memory.add instr (Value.cmp value left right) memory)
    | Llvm.Opcode.Br -> (
        match Llvm.get_branch instr with
        | Some (`Unconditional b) -> memory
        | _ -> raise Unsupported )
    
    | _ -> raise Unsupported

  let transfer_cond _ instr b memory = match Llvm.instr_opcode instr with
    | Llvm.Opcode.Br -> (
        match Llvm.get_branch instr with
        | Some (`Conditional (cond, b1, b2)) -> 
          let fst = filter cond b memory in
          fst)

  let transfer_phi _ instrs memory = List.fold_left (fun acc instr ->
                let inn = Llvm.incoming instr in
                let vall = List.fold_left (fun acc1 (instr, blk) ->
                                              Value.join acc1 (eval instr memory)) Value.bottom inn in
                let memo = Memory.add instr vall memory in
                Memory.join acc memo) Memory.bottom instrs

  let transfer_node llctx node memory =
    match node with
    | Domain.Graph.Node.Atomic instr -> transfer_atomic llctx instr memory
    | Domain.Graph.Node.CondBranch (instr, b) ->
        transfer_cond llctx instr b memory
    | Domain.Graph.Node.Phi instrs -> transfer_phi llctx instrs memory
end
