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

(** Definition of non-adjacent indices: indices are strictly increasing and no two indices are adjacent *)
Definition non_adjacent_in (il: list Z): Prop :=
  sincr il /\ forall i j, In i il -> In j il -> i + 1 <> j.

(** s is a non-adjacent subsequence of l with index list il *)
Definition non_adjacent_subseq (s l : list Z): Prop :=
  exists il, is_indexed_elements l il s /\ non_adjacent_in il.

(** Definition of sum of a list *)
Definition sum (l: list Z) : Z := fold_right Z.add 0 l.

(** Definition of the feasible set: s is feasible if it is a non-adjacent subsequence of l *)
Definition feasible_set (l : list Z) (s : list Z) := non_adjacent_subseq s l.

(** Specification for the maximum value: m is the maximum sum among all feasible subsequences *)
Definition max_value_spec (l: list Z) (m: Z) : Prop :=
  (exists s,
      feasible_set l s /\
      sum s = m /\
      forall t, feasible_set l t -> sum t <= m)
  \/
  ((forall s, feasible_set l s -> sum s <= 0%Z) /\ m = 0%Z).

(** Full specification: (m, s) is correct if m is the max sum and s is a feasible subsequence with sum m *)
Definition max_sum_full_spec (l: list Z) (m: Z) (s: list Z) : Prop :=
  max_value_spec l m /\
  feasible_set l s /\
  sum s = m.

(** Level 2: Prove that the algorithm returns the correct maximum value *)
Theorem max_sum_value_correct :
  forall l,
    Hoare (max_sum l)
      (fun '(m, _) => max_value_spec l m).
Proof.
Admitted.

(** Level 3: Prove that the algorithm returns a correct feasible subsequence achieving the maximum value *)
Theorem max_sum_full_correct :
  forall l,
    Hoare (max_sum l)
      (fun '(m, s) => max_sum_full_spec l m s).
Proof.
Admitted.

(** Lexicographical comparison of index lists *)
Fixpoint index_lex_lt (il1 il2: list Z) : Prop :=
  match il1, il2 with
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | i1 :: il1', i2 :: il2' =>
      i1 < i2 \/ (i1 = i2 /\ index_lex_lt il1' il2')
  end.

(** Specification for lexicographically minimal optimal solution *)
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

(** Modified algorithm to find the lexicographically minimal solution *)
Definition max_sum_lex (l: list Z): program (Z * list Z * list Z) :=
  '(max1, ans1, il1, _, _, _, _) <- 
    list_iter
      (fun n =>
         fun '(max1, ans1, il1, max2, ans2, il2, idx) =>
           choice
             (assume (max2 + n > max1);; 
              ret (max2 + n, ans2 ++ [n], il2 ++ [idx], max1, ans1, il1, idx + 1))
             (choice
                (assume (max2 + n < max1);;
                 ret (max1, ans1, il1, max1, ans1, il1, idx + 1))
                (assume (max2 + n = max1);;
                  choice 
                    (assume (index_lex_lt (il2 ++ [idx]) il1);;
                     ret (max2 + n, ans2 ++ [n], il2 ++ [idx], max1, ans1, il1, idx + 1))
                    (assume (~ index_lex_lt (il2 ++ [idx]) il1);;
                     ret (max1, ans1, il1, max1, ans1, il1, idx + 1))
                )
             )
      )
      l
      (0, [], [], 0, [], [], 0);; 
  ret (max1, ans1, il1).

(** Level 4: Prove that the modified algorithm returns the lexicographically minimal optimal solution *)
Theorem max_sum_lex_correct :
  forall l,
    Hoare (max_sum_lex l)
      (fun '(m, s, il) => lex_min_spec l m s il).
Proof.
Admitted.