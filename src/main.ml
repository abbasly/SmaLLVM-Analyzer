module SignMemory = Domain.Memory (Domain.Sign)
module SignAnalysis = Analysis.Make (SignMemory)
module TaintMemory = Domain.Memory (Domain.Taint)
module TaintAnalysis = Analysis.Make (TaintMemory)

let usage = "Usage: analyzer [ sign | taint ] [ LLVM IR file ]"

let main argv =
  if Array.length argv <> 3 then (
    prerr_endline "analyzer: You must specify one analysis and one LLVM IR file";
    prerr_endline usage;
    exit 1);
  let llctx = Llvm.create_context () in
  let llmem = Llvm.MemoryBuffer.of_file argv.(2) in
  let llm = Llvm_irreader.parse_ir llctx llmem in
  match argv.(1) with
  | "sign" ->
      SignAnalysis.Table.init llm
      |> SignAnalysis.run llctx |> SignAnalysis.check llctx
  | "taint" ->
      TaintAnalysis.Table.init llm
      |> TaintAnalysis.run llctx |> TaintAnalysis.check llctx
  | x ->
      prerr_endline (x ^ " is not a valid analysis");
      prerr_endline usage;
      exit 1

let _ = main Sys.argv
