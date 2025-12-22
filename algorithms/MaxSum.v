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

Lemma sum_app: forall l1 l2, sum (l1 ++ l2) = sum l1 + sum l2.
Proof.
  intros. induction l1; simpl; auto.
  rewrite IHl1. apply Z.add_assoc.
Qed.

Lemma feasible_set_nil: forall s, feasible_set [] s -> s = [].
Admitted.

Lemma feasible_set_nil_intro: feasible_set [] [].
Proof.
  exists []. split.
  - apply is_indexed_elements_nil.
  - split; simpl; auto.
Qed.

Lemma max_value_spec_nil: max_value_spec [] 0.
Proof.
  left. exists []. split; [| split].
  - apply feasible_set_nil_intro.
  - reflexivity.
  - intros t H. apply feasible_set_nil in H. subst. simpl. lia.
Qed.

Lemma Znth_error_app_l: forall {A} (l1 l2: list A) i,
  0 <= i < Zlength l1 ->
  Znth_error (l1 ++ l2) i = Znth_error l1 i.
Proof.
  intros.
  unfold Znth_error.
  destruct H as [Hge Hlt]. 
  destruct (Z_le_gt_dec 0 i); try lia.
  rewrite nth_error_app1.
  - reflexivity.
  - unfold Zlength in Hlt.
    apply Z2Nat.inj_lt in Hlt; try lia.
Qed.

Lemma Znth_error_app_r: forall {A} (l1 l2: list A) i,
  Zlength l1 <= i ->
  Znth_error (l1 ++ l2) i = Znth_error l2 (i - Zlength l1).
Proof.
  intros.
  unfold Znth_error.
  destruct (Z_le_gt_dec 0 i).
  - 
    destruct (Z_le_gt_dec 0 (i - Zlength l1)).
    + 
      rewrite nth_error_app2.
      * f_equal.
        rewrite Z2Nat.inj_sub; try lia.
        -- unfold Zlength. rewrite Nat2Z.id. reflexivity.
        -- unfold Zlength. lia.
      * unfold Zlength in H. apply Z2Nat.inj_le in H; try lia.
    +
      lia.
  - 
    pose proof (Zlength_nonneg l1).
    lia.
Qed.

Lemma feasible_set_app_x_l: forall l x s,
  feasible_set l s -> feasible_set (l ++ [x]) s.
Proof.
  intros l x s [il [Hidx [Hsincr Hgap]]].
  exists il. split; [| split; auto].
  - apply is_indexed_elements_range in Hidx as Hrange.
    eapply Forall2_congr; [| eauto].
    intros i a Hin1 Hin2 Hnth.
    rewrite Forall_forall in Hrange.
    specialize (Hrange _ Hin1).
    rewrite Znth_error_app_l; auto.
Qed.

Lemma Znth_error_snoc_last: forall {A} (l: list A) x,
  Znth_error (l ++ [x]) (Zlength l) = Some x.
Proof.
  intros.
  rewrite Znth_error_app_r; [| lia].
  replace (Zlength l - Zlength l) with 0 by lia.
  apply Znth_error_cons_0.
Qed.

Lemma is_indexed_elements_extend: forall (l: list Z) x s (il: list Z),
  is_indexed_elements (removelast l) il s ->
  is_indexed_elements (l ++ [x]) il s.
Admitted.

Lemma sincr_extend_last: forall (il: list Z) (last_idx: Z),
  sincr il ->
  (il = [] \/ last il 0 < last_idx) ->
  sincr (il ++ [last_idx]).
Admitted.

Lemma feasible_set_app_x_r: forall l x s,
  feasible_set (removelast l) s -> feasible_set (l ++ [x]) (s ++ [x]).
Admitted.

Lemma feasible_set_app_x_inv: forall l x s,
  feasible_set (l ++ [x]) s ->
  feasible_set l s \/
  (exists s', s = s' ++ [x] /\ feasible_set (removelast l) s').
Admitted.

Lemma max_value_spec_app:
  forall l x m1 m2,
    max_value_spec l m1 ->
    max_value_spec (removelast l) m2 ->
    max_value_spec (l ++ [x]) (Z.max m1 (m2 + x)).
Admitted.

Lemma removelast_app_x: forall {A} (l: list A) x,
  removelast (l ++ [x]) = l.
Proof.
  intros.
  rewrite removelast_app.
  - simpl. rewrite app_nil_r. reflexivity.
  - discriminate.
Qed.

Lemma Hoare_list_iter {A B: Type}: 
  forall (body: A -> B -> program B)
         (l: list A)
         (default: B)
         (I: list A -> B -> Prop),
    I [] default ->
    (forall x l_done b, 
      I l_done b -> 
      Hoare (body x b) 
            (fun b' => I (l_done ++ [x]) b')) ->
    Hoare (list_iter body l default)
          (fun b => I l b).
Admitted.

(** Level 2: Prove that the algorithm returns the correct maximum value *)
Theorem max_sum_value_correct :
  forall l,
    Hoare (max_sum l)
      (fun '(m, _) => max_value_spec l m).
Proof.
  intros l.
  unfold max_sum.
  eapply Hoare_bind. 
  - eapply Hoare_list_iter with 
      (I := fun done st => 
              match st with 
              | (m1, ans1, m2, ans2) => 
                  max_value_spec done m1 /\ 
                  max_value_spec (removelast done) m2
              end).
    + 
      simpl. split; apply max_value_spec_nil.
    + 
      intros x done st.
      destruct st as [[[m1 ans1] m2] ans2].
      intros [Hm1 Hm2]. 
      apply Hoare_choice.
      * 
        eapply Hoare_assume_bind.
        intros H_le.
        apply Hoare_ret. 
        split. 
        --
           assert (Hmax:  max_value_spec (done ++ [x]) (Z.max m1 (m2 + x))).
           { apply max_value_spec_app; auto. }
           replace (Z.max m1 (m2 + x)) with (m2 + x) in Hmax.
           ++ exact Hmax.
           ++ symmetry. apply Z.max_r.  lia.
        -- 
           rewrite removelast_app_x.
           auto.
        eapply Hoare_assume_bind.
        intros H_ge.
        apply Hoare_ret. 
        split.  
        -- 
           assert (Hmax: max_value_spec (done ++ [x]) (Z.max m1 (m2 + x))).
           { apply max_value_spec_app; auto. }
           replace (Z.max m1 (m2 + x)) with m1 in Hmax. 
           ++ exact Hmax. 
           ++ symmetry. apply Z.max_l. lia.
        -- 
           rewrite removelast_app_x.  
           auto.  
  - 
    intros st.  destruct st as [[[m1 ans1] m2] ans2].
    intros [Hm1 _].  
    apply Hoare_ret.  
    exact Hm1.
Qed. 

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
(** We require that for any other optimal solution (s', il'), our il is lexicographically <= il' *)
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