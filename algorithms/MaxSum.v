Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From MonadLib.SetMonad Require Import SetBasic SetHoare FixpointLib.
From MaxMinLib Require Import MaxMin Interface.
Require Import Algorithms.MapLib.
From ListLib.Base Require Import Inductive Positional.
From ListLib.General Require Import Forall IndexedElements Length Presuffix.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad.
Local Open Scope Z.

(* ========================================================================== *)
(* 1. 原算法定义 *)
(* ========================================================================== *)

Definition max_sum (l: list Z): program (Z * list Z) :=
  '(max1, ans1, _, _) <- list_iter
                           (fun n =>
                              fun '(max1, ans1, max2, ans2) =>
                                choice
                                  (assume (max1 <= max2 + n);;
                                   ret (max2 + n, ans2 ++ [n], max1, ans1))
                                  (assume (max1 >= max2 + n);;
                                   ret (max1, ans1, max1, ans1)))
                           l
                           (0, [], 0, []);;
  ret (max1, ans1).

(* ========================================================================== *)
(* 2. 基础定义 *)
(* ========================================================================== *)

Definition non_adjacent_in (il: list Z): Prop :=
  sincr il /\ forall i j, In i il -> In j il -> i + 1 <> j.

Definition non_adjacent_subseq (s l : list Z): Prop :=
  exists il, is_indexed_elements l il s /\ non_adjacent_in il.

Definition sum (l: list Z) : Z := fold_right Z.add 0 l.

Definition feasible_set (l : list Z) (s : list Z) := non_adjacent_subseq s l.

(* ========================================================================== *)
(* 3. 规范定义 *)
(* ========================================================================== *)

Definition max_value_spec (l: list Z) (m: Z) : Prop :=
  (exists s,
      feasible_set l s /\
      sum s = m /\
      forall t, feasible_set l t -> sum t <= m)
  \/
  ((forall s, feasible_set l s -> sum s <= 0%Z) /\ m = 0%Z).

Definition max_sum_full_spec (l: list Z) (m: Z) (s: list Z) : Prop :=
  max_value_spec l m /\
  feasible_set l s /\
  sum s = m.

Lemma Zlength_nonneg_list : forall (l: list Z), 0 <= Zlength l.
Proof. 
  intros. 
  apply Zlength_nonneg.
Qed.

(* ========================================================================== *)
(* 4. 难度任务 - 定理声明 *)
(* ========================================================================== *)

(* 第二档难度 *)
Theorem max_sum_value_correct :
  forall l,
    Hoare (max_sum l)
      (fun '(m, _) => max_value_spec l m).
Proof.
Admitted.

(* 第三档难度 *)
Theorem max_sum_full_correct :
  forall l,
    Hoare (max_sum l)
      (fun '(m, s) => max_sum_full_spec l m s).
Proof.
Admitted.

(* ========================================================================== *)
(* 5. 第四档难度 - 字典序最小 *)
(* ========================================================================== *)

(* 字典序比较 *)
Fixpoint index_lex_lt (il1 il2: list Z) : Prop :=
  match il1, il2 with
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | i1 :: il1', i2 :: il2' =>
      i1 < i2 \/ (i1 = i2 /\ index_lex_lt il1' il2')
  end.

(* 字典序最小规范 *)
Definition lex_min_spec (l: list Z) (m: Z) (s: list Z) (il: list Z) : Prop :=
  max_sum_full_spec l m s /\
  is_indexed_elements l il s /\
  non_adjacent_in il /\
  (forall s' il', 
     feasible_set l s' -> 
     is_indexed_elements l il' s' -> 
     non_adjacent_in il' ->
     sum s' = m -> 
     index_lex_lt il il' \/ il = il').

(* 
   修改后的算法：max_sum_lex
   状态元组: (max1, ans1, il1, max2, ans2, il2, idx)
   max1/ans1/il1: 当前最优解（和，序列，索引）
   max2/ans2/il2: 不选前一个元素的最优解（和，序列，索引）
   idx: 当前处理元素的索引
*)
Definition max_sum_lex (l: list Z): program (Z * list Z * list Z) :=
  '(max1, ans1, il1, _, _, _, _) <- 
    list_iter
      (fun n =>
         fun '(max1, ans1, il1, max2, ans2, il2, idx) =>
           (* 方案1: 包含当前元素 n (前提是不包含前一个) -> 基础是从 (max2, ans2, il2) 转移而来 *)
           let cand_inc_sum := max2 + n in
           let cand_inc_ans := ans2 ++ [n] in
           let cand_inc_il  := il2 ++ [idx] in
           
           (* 方案2: 不包含当前元素 n -> 基础是从 (max1, ans1, il1) 转移而来 *)
           let cand_exc_sum := max1 in
           let cand_exc_ans := ans1 in
           let cand_exc_il  := il1 in

           (* 新的 max2/ans2/il2 将会变成当前的 max1/ans1/il1 (为了下一次迭代做准备) *)
           let next_max2 := max1 in
           let next_ans2 := ans1 in
           let next_il2  := il1 in
           let next_idx  := idx + 1 in

           (* 修复：嵌套 choice 以处理三个分支 *)
           choice
             (* Case 1: 包含当前元素使得和严格更大 *)
             (assume (cand_inc_sum > cand_exc_sum);; 
              ret (cand_inc_sum, cand_inc_ans, cand_inc_il, next_max2, next_ans2, next_il2, next_idx))
             
             (choice
                (* Case 2: 不包含当前元素使得和严格更大 *)
                (assume (cand_inc_sum < cand_exc_sum);;
                 ret (cand_exc_sum, cand_exc_ans, cand_exc_il, next_max2, next_ans2, next_il2, next_idx))
                
                (* Case 3: 和相等，比较字典序 *)
                (assume (cand_inc_sum = cand_exc_sum);;
                  choice 
                    (* 包含当前元素的索引序列字典序 更小 *)
                    (assume (index_lex_lt cand_inc_il cand_exc_il);;
                     ret (cand_inc_sum, cand_inc_ans, cand_inc_il, next_max2, next_ans2, next_il2, next_idx))
                    
                    (* 不包含当前元素的索引序列字典序 更小 或 相等 *)
                    (* 如果字典序相等，通常优先选不包含的（因为较短），或者保持原样 *)
                    (assume (~ index_lex_lt cand_inc_il cand_exc_il);;
                     ret (cand_exc_sum, cand_exc_ans, cand_exc_il, next_max2, next_ans2, next_il2, next_idx))
                )
             )
      )
      l
      (0, [], [], 0, [], [], 0);; (* 初始状态，索引从 0 开始 *)
  ret (max1, ans1, il1).

(* 第四档难度定理 *)
Theorem max_sum_lex_correct :
  forall l,
    Hoare (max_sum_lex l)
      (fun '(m, s, il) => lex_min_spec l m s il).
Proof.
Admitted.