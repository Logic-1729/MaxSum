Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
(* From RecordUpdate Require Import RecordUpdate. *)
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

(* 索引列表不相邻的定义,il是一个索引列表 *)
Definition non_adjacent_in (il: list Z): Prop:=
  sincr il /\ forall i j, In i il -> In j il -> i + 1 <> j.

(* s 是 l 的一个不相邻子序列, 索引列表是 il *)
Definition non_adjacent_subseq (s l : list Z): Prop:=
  exists il, is_indexed_elements l il s /\ non_adjacent_in il.

(* list 求和的定义 *)
Definition sum (l: list Z) : Z := fold_right Z.add 0 l.

(* 可行集合的定义 *)
Definition feasible_set (l : list Z) (s : list Z) := non_adjacent_subseq s l.

(* Definition max_value_spec (l: list Z) (m: Z) : Prop :=
  max_value_of_subset_with_default
    (fun s => feasible_set l s)
    (fun s => sum s)
    0
    m. *)

(* 集合最大值 *)
Definition max_value_spec (l: list Z) (m: Z) : Prop :=
  (exists s,
      (* s 是可行子序列，且它的和等于 m *)
      feasible_set l s /\
      sum s = m /\
      (* m 是可行集合上的上界 *)
      forall t, feasible_set l t -> sum t <= m)
  \/
  (* 可行集合为空或所有和都不超过 0，默认值为 0 *)
  ((forall s, feasible_set l s -> sum s <= 0%Z) /\ m = 0%Z).

(* “排末元素”集合的最大值 *)
Definition max_value_spec_excl_last (prefix: list Z) (m: Z) : Prop :=
  (exists s il,
     is_indexed_elements prefix il s /\ non_adjacent_in il
     /\ Forall (fun i => i < Zlength prefix - 1) il
     /\ sum s = m
     /\ forall t il', is_indexed_elements prefix il' t /\ non_adjacent_in il'
                      /\ Forall (fun i => i < Zlength prefix - 1) il'
                      -> sum t <= m)
  \/
  ((forall s il, is_indexed_elements prefix il s /\ non_adjacent_in il
                 /\ Forall (fun i => i < Zlength prefix - 1) il
                 -> sum s <= 0%Z)
   /\ m = 0%Z).

(* 不变式 *)
Definition P (prefix: list Z) (st: Z * list Z * Z * list Z) : Prop :=
  let '(max1, ans1, max2, ans2) := st in
  (exists il1, is_indexed_elements prefix il1 ans1 /\ non_adjacent_in il1)
  /\ (exists il2, is_indexed_elements prefix il2 ans2 /\ non_adjacent_in il2
                  /\ Forall (fun i => i < Zlength prefix - 1) il2)
  /\ max_value_spec prefix max1
  /\ max_value_spec_excl_last prefix max2.


Lemma Znth_error_app_left :
  forall (l l' : list Z) (i : Z),
    0 <= i < Zlength l ->
    Znth_error (l ++ l') i = Znth_error l i.
Proof.
  intros l l' i Hrange.
  assert (i < Zlength (l ++ l')) as Hlt_app.
  { rewrite Zlength_app. unfold Zlength in *. lia. }
  unfold Znth_error.
  repeat (destruct (Z_le_gt_dec _ _); [| congruence]).
  assert (Z.to_nat i < length l)%nat as Hnat.
  { unfold Zlength in Hrange.
    lia. (* This works in Coq 8.15+ with ZArith *)
  }
  apply nth_error_app1; auto.
Qed.

Lemma nth_error_app_r :
  forall (A : Type) (l : list A) (x : A),
    nth_error (l ++ [x]) (length l) = Some x.
Proof.
  intros A l x.
  induction l as [|y ys IH]; simpl.
  - reflexivity.
  - tauto.
Qed.


Lemma extend_last_feasible :
  forall (prefix : list Z) (ans2 : list Z) (il2 : list Z) (n : Z),
    is_indexed_elements prefix il2 ans2 ->
    non_adjacent_in il2 ->
    Forall (fun i => i < Zlength prefix - 1) il2 ->
    let last := Zlength prefix in
    is_indexed_elements (prefix ++ [n]) (il2 ++ [last]) (ans2 ++ [n])
    /\ non_adjacent_in (il2 ++ [last]).
Proof.
  intros prefix ans2 il2 n Hindexed Hnonadj Hbound.
  set (last := Zlength prefix).

  (* ---------- Part 1: is_indexed_elements ---------- *)
  assert (H1 : is_indexed_elements (prefix ++ [n]) il2 ans2).
  { unfold is_indexed_elements in *.
    induction Hindexed as [| i a il l Hnth Hrest IH]; simpl.
    - apply Forall2_nil.
    - constructor.
      + pose proof (Znth_error_range _ _ _ Hnth) as Hrange.
        rewrite (Znth_error_app_left prefix [n] i Hrange).
        exact Hnth.
      + (* Prove: is_indexed_elements (prefix ++ [n]) il l *)
      (* Need: non_adjacent_in il and Hbound for il *)
        assert (Hnonadj_il : non_adjacent_in il).
        { destruct Hnonadj as [Hsincr_cons Hnoadj_cons].
          (* sincr (i :: il) implies sincr il *)
          assert (Hsincr_il : sincr il).
          { destruct il as [|j js].
            - unfold sincr; constructor.
            - pose proof sincr_app_cons_inv2 [i] j js.
              simpl in *.
              pose proof H Hsincr_cons.
              tauto.
              (* unfold sincr in Hsincr_cons.
              simpl in Hsincr_cons.
              unfold sincr.
              destruct Hsincr_cons as [Hij Hsincr_js].
              exact Hsincr_js. *)
          }
          (* no adjacent in tail *)
          assert (Hnoadj_il : forall x y, In x il -> In y il -> x + 1 <> y).
          { intros x y Hx Hy.
            apply Hnoadj_cons.
            - apply in_cons; tauto.
            - apply in_cons; tauto.
          }
          split; auto.
        }
      
        assert (Hbound_il : Forall (fun i0 => i0 < Zlength prefix - 1) il).
        { replace (i :: il) with ([i] ++ il) in Hbound by reflexivity.
          apply Forall_app in Hbound.
          destruct Hbound as [H1 H2].
          exact H2.
        }
        apply IH; auto.
  }

  assert (H2 : is_indexed_elements (prefix ++ [n]) [last] [n]).
  { unfold is_indexed_elements.
    constructor.
    - (* Show: Znth_error (prefix ++ [n]) last = Some n *)
      assert (0 <= last < Zlength (prefix ++ [n])) as Hrange_last.
      {
        rewrite Zlength_app.
        unfold Zlength in *.
        simpl.
        split.
        + apply Zlength_nonneg.
        + lia.
      }
      unfold Znth_error.
      destruct (Z_le_gt_dec 0 last) as [Hle|Hgt].
      + (* 0 <= last *)
        destruct (Z_lt_ge_dec last (Zlength (prefix ++ [n]))) as [Hlt|Hge].
        * (* last < Zlength (prefix ++ [n]) — good *)
          f_equal.
          assert (Z.to_nat last = length prefix) as Heq.
          { unfold last, Zlength.
            apply Nat2Z.id.
          }
          rewrite Heq.
          (* Now goal: nth_error (prefix ++ [n]) (length prefix) = Some n *)
          apply nth_error_app_r.
        * (* last >= Zlength (prefix ++ [n]) — contradiction *)
          exfalso; lia.
      + (* last < 0 — contradiction *)
        exfalso; lia.
    - apply Forall2_nil.
  }

  assert (Hindexed_new : is_indexed_elements (prefix ++ [n]) (il2 ++ [last]) (ans2 ++ [n])).
  { apply is_indexed_elements_app; auto. }

  (* ---------- Part 2: non_adjacent_in ---------- *)
  destruct Hnonadj as [Hsincr Hnoadj].

  (* (a) sincr (il2 ++ [last]) *)
  assert (Hsincr_new : sincr (il2 ++ [last])).
  { (* Step 1: Show all elements in il2 are < last *)
    assert (Hlt_all : Forall (fun i => i < last) il2).
    { apply Forall_forall.
      intros i Hin.
      rewrite Forall_forall in Hbound.
      pose proof Hbound i Hin.
      lia.
    }
        

  (* generalize dependent ans2; generalize dependent prefix; generalize dependent n.
  induction il2 as [|x xs IH]; simpl.
  - tauto. (* il2 = nil *)
  - intros.
    apply sincr_cons.
    + apply Forall_app; split.
      * apply sincr_cons_tail_Forall_lt in Hsincr; auto.
      * apply Forall_cons_iff in Hlt_all; destruct Hlt_all as [Hx_last _]; auto.
    + simpl in Hsincr; apply Forall_cons_iff in Hlt_all; destruct Hlt_all as [_ Hxs_last].
      apply IH; auto. *)

    

  (* Step 2: Prove sincr (il2 ++ [last]) by induction *)
  (* induction il2 as [|x xs IH]; simpl.
  - tauto.
  - destruct xs as [|y ys].
    + (* xs = [] *)
      split.
      * rewrite Forall_forall in Hbound.
        assert (In x [x]). { simpl. tauto. }
        pose proof Hbound x H.
        lia.
      * constructor.
    + (* xs = y :: ys *)
      split.
      * (* x < y from Hsincr *)
        unfold sincr in Hsincr; simpl in Hsincr.
        destruct Hsincr as [Hxy _]; exact Hxy.
      * (* sincr (y :: ys ++ [last]) *)
        apply IH; auto.
        (* Extract Forall for xs = y :: ys *)
        inversion Hlt_all.
        ++  
        assumption. *)
  }

  (* (b) no two indices are consecutive *)
  assert (Hnoadj_new : forall i j,
      In i (il2 ++ [last]) -> In j (il2 ++ [last]) -> i + 1 <> j).
  { intros i j Hi Hj.
    apply in_app_or in Hi; apply in_app_or in Hj.
    destruct Hi as [Hi1 | ->]; destruct Hj as [Hj1 | ->]; try (apply Hnoadj; auto).
    - (* i ∈ il2, j = last *) intro H; apply Hbound in Hi1; unfold last in *; lia.
    - (* i = last, j ∈ il2 *) intro H; apply Hbound in Hj1; unfold last in *; lia.
    - (* i = j = last *) intro H; unfold last in *; lia.
  }

  split.
  - exact Hindexed_new.
  - split.
    + exact Hsincr_new.
    + exact Hnoadj_new.
Qed.



Lemma max_sum_value_optimal :
  forall l,
    Hoare (max_sum l)
      (fun '(m, s) =>
         max_value_spec l m /\ feasible_set l s).





(* Theorem max_sum_value_opt_maxmin :
  forall (l : list Z),
    Hoare (max_sum l)
      (fun '(v, _) =>
        v is-the-max-of sum s in-which s satisfies feasible_set l s).

(* 定理:证明max1是满足条件的子序列中子序列和的最大值 *)
Theorem max_sum_correct_ineq :
  forall (l : list Z),
    Hoare (max_sum l)
      (fun '(v, s) =>
        feasible_set l s /\
        sum s = v /\
        forall s', feasible_set l s' -> sum s' <= v).
Proof.
Admitted. *)

