open OUnit2
open Domain

let print_sign x =
  match x with
  | Sign.Bot -> "Bot"
  | Sign.Top -> "Top"
  | Sign.Pos -> "Pos"
  | Sign.Neg -> "Neg"
  | Sign.Zero -> "Zero"

let join_1 =
  "join_1" >:: fun _ ->
  assert_equal ~msg:"join_1" ~printer:print_sign Sign.Pos
    (Sign.join Sign.Bot Sign.Pos)

let join_2 =
  "join_2" >:: fun _ ->
  assert_equal ~msg:"join_2" ~printer:print_sign Sign.Neg
    (Sign.join Sign.Neg Sign.Bot)

let join_3 =
  "join_3" >:: fun _ ->
  assert_equal ~msg:"join_3" ~printer:print_sign Sign.Top
    (Sign.join Sign.Pos Sign.Top)

let join_4 =
  "join_4" >:: fun _ ->
  assert_equal ~msg:"join_4" ~printer:print_sign Sign.Pos
    (Sign.join Sign.Pos Sign.Pos)

let join_5 =
  "join_5" >:: fun _ ->
  assert_equal ~msg:"join_5" ~printer:print_sign Sign.Top
    (Sign.join Sign.Pos Sign.Neg)

let add_1 =
  "add_1" >:: fun _ ->
  assert_equal ~msg:"add_1" ~printer:print_sign Sign.Pos
    (Sign.add Sign.Pos Sign.Zero)

let add_2 =
  "add_2" >:: fun _ ->
  assert_equal ~msg:"add_2" ~printer:print_sign Sign.Neg
    (Sign.add Sign.Neg Sign.Neg)

let add_3 =
  "add_3" >:: fun _ ->
  assert_equal ~msg:"add_3" ~printer:print_sign Sign.Top
    (Sign.add Sign.Pos Sign.Neg)

let add_4 =
  "add_4" >:: fun _ ->
  assert_equal ~msg:"add_4" ~printer:print_sign Sign.Bot
    (Sign.add Sign.Pos Sign.Bot)

let sub_1 =
  "sub_1" >:: fun _ ->
  assert_equal ~msg:"sub_1" ~printer:print_sign Sign.Pos
    (Sign.sub Sign.Pos Sign.Neg)

let sub_2 =
  "sub_2" >:: fun _ ->
  assert_equal ~msg:"sub_2" ~printer:print_sign Sign.Neg
    (Sign.sub Sign.Neg Sign.Pos)

let sub_3 =
  "sub_3" >:: fun _ ->
  assert_equal ~msg:"sub_3" ~printer:print_sign Sign.Top
    (Sign.sub Sign.Neg Sign.Neg)

let mul_1 =
  "mul_1" >:: fun _ ->
  assert_equal ~msg:"mul_1" ~printer:print_sign Sign.Bot
    (Sign.mul Sign.Bot Sign.Pos)

let mul_2 =
  "mul_2" >:: fun _ ->
  assert_equal ~msg:"mul_2" ~printer:print_sign Sign.Pos
    (Sign.mul Sign.Neg Sign.Neg)

let mul_3 =
  "mul_3" >:: fun _ ->
  assert_equal ~msg:"mul_3" ~printer:print_sign Sign.Neg
    (Sign.mul Sign.Neg Sign.Pos)

let div_1 =
  "div_1" >:: fun _ ->
  assert_equal ~msg:"div_1" ~printer:print_sign Sign.Pos
    (Sign.div Sign.Pos Sign.Pos)

let div_2 =
  "div_2" >:: fun _ ->
  assert_equal ~msg:"div_2" ~printer:print_sign Sign.Neg
    (Sign.div Sign.Neg Sign.Pos)

let div_3 =
  "div_3" >:: fun _ ->
  assert_equal ~msg:"div_3" ~printer:print_sign Sign.Top
    (Sign.div Sign.Top Sign.Pos)

let cmp_slt =
  "cmp_slt" >:: fun _ ->
  assert_equal ~msg:"cmp_slt" ~printer:print_sign Sign.Pos
    (Sign.cmp Llvm.Icmp.Slt Sign.Neg Sign.Zero)

let cmp_slt_zero_1 =
  "cmp_slt_1" >:: fun _ ->
  assert_equal ~msg:"cmp_slt_zero_1" ~printer:print_sign Sign.Zero
    (Sign.cmp Llvm.Icmp.Slt Sign.Zero Sign.Zero)

let cmp_slt_zero_2 =
  "cmp_slt_zero_2" >:: fun _ ->
  assert_equal ~msg:"cmp_slt_zero_2" ~printer:print_sign Sign.Zero
    (Sign.cmp Llvm.Icmp.Slt Sign.Pos Sign.Neg)

let cmp_sle_bot =
  "cmp_sle_bot" >:: fun _ ->
  assert_equal ~msg:"cmp_sle_bot" ~printer:print_sign Sign.Bot
    (Sign.cmp Llvm.Icmp.Sle Sign.Bot Sign.Pos)

let cmp_sle_zero =
  "cmp_sle_zero" >:: fun _ ->
  assert_equal ~msg:"cmp_sle_zero" ~printer:print_sign Sign.Zero
    (Sign.cmp Llvm.Icmp.Sle Sign.Pos Sign.Zero)

let cmp_sle_pos =
  "cmp_sle_pos" >:: fun _ ->
  assert_equal ~msg:"cmp_sle_pos" ~printer:print_sign Sign.Pos
    (Sign.cmp Llvm.Icmp.Sle Sign.Zero Sign.Pos)

let cmp_eq_zero =
  "cmp_eq_zero" >:: fun _ ->
  assert_equal ~msg:"cmp_eq_zero" ~printer:print_sign Sign.Pos
    (Sign.cmp Llvm.Icmp.Eq Sign.Zero Sign.Zero)

let cmp_eq_pos =
  "cmp_eq_pos" >:: fun _ ->
  assert_equal ~msg:"cmp_eq_pos" ~printer:print_sign Sign.Top
    (Sign.cmp Llvm.Icmp.Eq Sign.Pos Sign.Pos)

let cmp_ne_1 =
  "cmp_ne_1" >:: fun _ ->
  assert_equal ~msg:"cmp_ne_1" ~printer:print_sign Sign.Pos
    (Sign.cmp Llvm.Icmp.Ne Sign.Pos Sign.Zero)

let cmp_ne_2 =
  "cmp_ne_2" >:: fun _ ->
  assert_equal ~msg:"cmp_ne_2" ~printer:print_sign Sign.Zero
    (Sign.cmp Llvm.Icmp.Ne Sign.Zero Sign.Zero)

let cmp_ne_3 =
  "cmp_ne_3" >:: fun _ ->
  assert_equal ~msg:"cmp_ne_3" ~printer:print_sign Sign.Pos
    (Sign.cmp Llvm.Icmp.Ne Sign.Pos Sign.Neg)

let cmp_sgt_1 =
  "cmp_sgt_1" >:: fun _ ->
  assert_equal ~msg:"cmp_sgt_1" ~printer:print_sign Sign.Pos
    (Sign.cmp Llvm.Icmp.Sgt Sign.Zero Sign.Neg)

let cmp_sgt_2 =
  "cmp_sgt_2" >:: fun _ ->
  assert_equal ~msg:"cmp_sgt_2" ~printer:print_sign Sign.Pos
    (Sign.cmp Llvm.Icmp.Sgt Sign.Pos Sign.Neg)

let cmp_sgt_3 =
  "cmp_sgt_3" >:: fun _ ->
  assert_equal ~msg:"cmp_sgt_3" ~printer:print_sign Sign.Top
    (Sign.cmp Llvm.Icmp.Sgt Sign.Zero Sign.Top)

let filter_1 =
  "filter_1" >:: fun _ ->
  assert_equal ~msg:"filter_1" ~printer:print_sign Sign.Pos
    (Sign.filter Llvm.Icmp.Sgt Sign.Top Sign.Zero)

let filter_2 =
  "filter_2" >:: fun _ ->
  assert_equal ~msg:"filter_2" ~printer:print_sign Sign.Neg
    (Sign.filter Llvm.Icmp.Slt Sign.Neg Sign.Pos)

let filter_3 =
  "filter_3" >:: fun _ ->
  assert_equal ~msg:"filter_3" ~printer:print_sign Sign.Neg
    (Sign.filter Llvm.Icmp.Ne Sign.Neg Sign.Pos)

let filter_4 =
  "filter_4" >:: fun _ ->
  assert_equal ~msg:"filter_4" ~printer:print_sign Sign.Pos
    (Sign.filter Llvm.Icmp.Eq Sign.Top Sign.Pos)

let suite =
  "suite"
  >::: [
         join_1;
         join_2;
         join_3;
         join_4;
         join_5;
         add_1;
         add_2;
         add_3;
         add_4;
         sub_1;
         sub_2;
         sub_3;
         mul_1;
         mul_2;
         mul_3;
         div_1;
         div_2;
         div_3;
         cmp_slt;
         cmp_slt_zero_1;
         cmp_slt_zero_2;
         cmp_sle_bot;
         cmp_sle_pos;
         cmp_sle_zero;
         cmp_eq_zero;
         cmp_eq_pos;
         cmp_ne_1;
         cmp_ne_2;
         cmp_ne_3;
         cmp_sgt_1;
         cmp_sgt_2;
         cmp_sgt_3;
         filter_1;
         filter_2;
         filter_3;
         filter_4;
       ]

let _ = OUnit2.run_test_tt_main suite
