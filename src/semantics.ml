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

  let eval e mem = failwith "Not implemented"

  let filter cond truth memory = failwith "Not implemented"

  let transfer_atomic _ instr memory = failwith "Not implemented"

  let transfer_cond _ instr b memory = failwith "Not implemented"

  let transfer_phi _ instrs memory = failwith "Not implemented"

  let transfer_node llctx node memory =
    match node with
    | Domain.Graph.Node.Atomic instr -> transfer_atomic llctx instr memory
    | Domain.Graph.Node.CondBranch (instr, b) ->
        transfer_cond llctx instr b memory
    | Domain.Graph.Node.Phi instrs -> transfer_phi llctx instrs memory
end
