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
Proof. 
  intros s H.
  unfold feasible_set, non_adjacent_subseq in H.  
  destruct H as [il [Hidx _]].  
  destruct s as [| a s'].
  - reflexivity. 
  - exfalso. 
    apply is_indexed_elements_cons_inv_r in Hidx. 
    destruct Hidx as [i [il' [_ [Hnth _]]]].
    unfold Znth_error in Hnth.
    destruct (Z_le_gt_dec 0 i).
    + 
      assert (nth_error (@nil Z) (Z.to_nat i) = None) by (destruct (Z.to_nat i); reflexivity).
      congruence.
    + 
      discriminate Hnth. 
Qed.

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
Proof.
  intros.
  destruct l.
  - (* Case l = [] *)
    simpl in H.
    unfold is_indexed_elements in *.
    destruct il.
    + inversion H; subst. apply Forall2_nil.
    + inversion H; subst.
      unfold Znth_error in H2.
      destruct (Z_le_gt_dec 0 z).
      * destruct (Z.to_nat z); simpl in H2; discriminate.
      * discriminate.
  - 
    unfold is_indexed_elements in *.
    eapply Forall2_congr; [| eauto].
    intros i a0 Hin_i Hin_s Hnth.
    assert (Hneq: z :: l <> []) by congruence.
    destruct (exists_last Hneq) as [l' [a Heq]].
    rewrite Heq in Hnth.
    rewrite Heq.
    
    rewrite removelast_app in Hnth; [| discriminate].
    simpl in Hnth.
    rewrite app_nil_r in Hnth.
    rewrite <- app_assoc.
    rewrite Znth_error_app_l.
    + 
      assumption.
    + 
      apply Znth_error_range in Hnth.
      assumption.
Qed.

Lemma sincr_extend_last: forall (il: list Z) (last_idx: Z),
  sincr il ->
  (il = [] \/ last il 0 < last_idx) ->
  sincr (il ++ [last_idx]).
Proof.
  intros il last_idx Hsincr Hlast.
  destruct il as [| i0 il']. 
  - 
    simpl.  auto.
  - 
    simpl in *.
    destruct Hlast as [Heq | Hlt].
    + 
      discriminate Heq.
    + 
      revert i0 Hsincr Hlt.
      induction il' as [| i1 il'' IH]; intros i0 Hsincr Hlt.
      * 
        simpl in *.
        simpl in Hlt.
        split; auto.
      * 
        simpl in Hsincr.
        destruct Hsincr as [Hi0_i1 Hrest]. 
        simpl. 
        split; [exact Hi0_i1 | ].
        apply IH; auto.
Qed.

Lemma sincr_app_singleton_inv: forall l1 x,
  sincr (l1 ++ [x]) ->
  forall i, In i l1 -> i < x.
Proof.
  induction l1 as [| a l1' IH]; intros x Hsincr i Hin.
  - inversion Hin.
  - simpl in Hsincr.
    simpl in Hin. 
    destruct Hin as [Heq | Hin']. 
    + subst i.
      destruct l1' as [| b l1''].
      * 
        simpl in Hsincr. 
        lia.
      * 
        simpl in Hsincr. 
        destruct Hsincr as [Hab Hrest].
        assert (Hbx: b < x).
        { apply (IH x); auto. left; reflexivity. }
        lia.
    + apply IH; auto.
      destruct l1' as [| b l1'']; simpl in *; tauto.
Qed. 

Lemma last_in_list:  forall {A} (l:  list A) (d: A),
  l <> [] -> In (last l d) l.
Proof.
  intros A l d Hneq.
  induction l as [| a l' IH].
  - contradiction.
  - destruct l' as [| b l'']. 
    + simpl.  left. reflexivity.
    + simpl. right. apply IH.  discriminate.
Qed. 

Lemma feasible_set_app_x_r:  forall l x s,
  feasible_set (removelast l) s -> feasible_set (l ++ [x]) (s ++ [x]).
Proof.
  intros l x s H.
  unfold feasible_set, non_adjacent_subseq in *.
  destruct H as [il [Hidx [Hsincr Hgap]]].  
  exists (il ++ [Zlength l]).
  split; [| split]. 
  
  - 
    apply is_indexed_elements_app. 
    + 
      apply is_indexed_elements_extend. 
      exact Hidx. 
    + 
      apply is_indexed_elements_cons.
      * 
        apply Znth_error_snoc_last.
      *
        apply is_indexed_elements_nil. 
  
  - 
    apply sincr_extend_last. 
    + exact Hsincr.
    + destruct il as [| i0 il']. 
      * left. reflexivity. 
      * right. 
        apply is_indexed_elements_range in Hidx. 
        rewrite Forall_forall in Hidx.
        assert (Hin_last: In (last (i0 :: il') 0) (i0 :: il')).
        { apply last_in_list.  discriminate. }
        specialize (Hidx _ Hin_last).
        destruct (list_snoc_destruct l) as [Heq_l | [a [l0 Heq_l]]].
        -- 
           subst l.  simpl in Hidx.  unfold Zlength in *. simpl in *. lia.
        -- 
           subst l. 
           rewrite removelast_app in Hidx by discriminate.
           simpl in Hidx. rewrite app_nil_r in Hidx. 
           rewrite Zlength_app.  unfold Zlength in *. simpl in *.  lia.
  
  - 
    intros i j Hi Hj.
    apply in_app_or in Hi. 
    apply in_app_or in Hj.
    destruct Hi as [Hi_il | Hi_last];
    destruct Hj as [Hj_il | Hj_last].   
    + 
      apply Hgap; auto.
    + 
      simpl in Hj_last. 
      destruct Hj_last as [Heq | Hf]; [| contradiction]. 
      subst j.
      apply is_indexed_elements_range in Hidx.
      rewrite Forall_forall in Hidx.
      specialize (Hidx _ Hi_il).
      destruct (list_snoc_destruct l) as [Heq_l | [a [l0 Heq_l]]]. 
      * subst l.  simpl in Hidx. unfold Zlength in *. simpl in *. lia.  
      * subst l. 
        rewrite removelast_app in Hidx by discriminate.  
        simpl in Hidx.   rewrite app_nil_r in Hidx.
        rewrite Zlength_app. unfold Zlength in *. simpl in *.
        lia.  
    + 
      simpl in Hi_last.
      destruct Hi_last as [Heq | Hf]; [| contradiction].  
      subst i. 
      apply is_indexed_elements_range in Hidx. 
      rewrite Forall_forall in Hidx.
      specialize (Hidx _ Hj_il).
      destruct (list_snoc_destruct l) as [Heq_l | [a [l0 Heq_l]]].  
      * subst l.  simpl in Hidx. unfold Zlength in *. simpl in *.  lia.
      * subst l.
        rewrite removelast_app in Hidx by discriminate.
        simpl in Hidx. rewrite app_nil_r in Hidx. 
        rewrite Zlength_app. unfold Zlength in *. simpl in *. 
        lia. 
    + 
      simpl in Hi_last, Hj_last.
      destruct Hi_last as [Heq_i | Hf]; [| contradiction].
      destruct Hj_last as [Heq_j | Hf]; [| contradiction].
      subst i j.
      lia. 
Qed. 

Lemma feasible_set_app_x_inv_empty_il: forall l x s,
  is_indexed_elements (l ++ [x]) [] s ->
  feasible_set l s. 
Proof.
  intros l x s Hidx.
  apply is_indexed_elements_nil_inv_l in Hidx. 
  subst s.
  exists [].
  split. 
  - apply is_indexed_elements_nil.
  - split; simpl; auto.
Qed. 

Lemma feasible_set_app_x_inv_l_empty:   forall (x:   Z) il' s1,
  sincr (il' ++ [0]) ->
  is_indexed_elements ([] ++ [x]) il' s1 ->
  il' = [] /\ s1 = [].  
Proof.
  intros x il' s1 Hsincr Hidx1.
  simpl in Hidx1.
  destruct il' as [| i0 il''].   
  - split; auto.
    apply is_indexed_elements_nil_inv_l in Hidx1.  auto.
  - exfalso.  
    apply is_indexed_elements_cons_inv_l in Hidx1.
    destruct Hidx1 as [a1 [s1' [Hnth0 _]]].  
    unfold Znth_error in Hnth0.
    destruct (Z_le_gt_dec 0 i0).
    + simpl in Hsincr.   
      destruct il'' as [| i1 il'''].  
      * simpl in Hsincr. 
        destruct Hsincr as [Hi0_lt_0 _].   
        lia.
      * simpl in Hsincr. 
        destruct Hsincr as [Hi0_lt_i1 Hrest].  
        assert (Hi1_lt_0: i1 < 0).
        {
          clear -Hrest. 
          assert (Haux: forall il y,
                     sincr_aux il y ->
                     forall j, In j il -> y < j).
          {
            clear.  
            induction il as [| a il' IH]; intros y Hsaux j Hin.
            - inversion Hin. 
            - simpl in Hsaux. destruct Hsaux as [Hya Hrest'].    
              simpl in Hin.  destruct Hin as [Heq | Hin'].  
              + subst.  exact Hya. 
              + assert (Ha_lt_j:   a < j) by (apply IH; auto). lia.
          }
          apply (Haux (il''' ++ [0]) i1 Hrest 0).
          apply in_app_iff.    right.  simpl. left.  reflexivity. 
        }
        lia. 
    + discriminate Hnth0.
Qed. 

Lemma feasible_set_app_x_inv_idx_bound: forall (l0 :   list Z) (a0 x : Z) il' i,
  sincr (il' ++ [Zlength (l0 ++ [a0])]) ->
  (forall i j, In i (il' ++ [Zlength (l0 ++ [a0])]) -> 
               In j (il' ++ [Zlength (l0 ++ [a0])]) -> 
               i + 1 <> j) ->
  In i il' ->
  (exists s1, is_indexed_elements ((l0 ++ [a0]) ++ [x]) il' s1) ->
  (exists a, Znth_error ((l0 ++ [a0]) ++ [x]) i = Some a) ->
  i < Zlength l0.
Proof. 
  intros l0 a0 x il' i Hsincr Hgap Hin_i [s1 Hidx] _. 
  assert (Hi_lt:  i < Zlength (l0 ++ [a0])).
  { apply sincr_app_singleton_inv with (l1 := il'); auto. }
  apply is_indexed_elements_range in Hidx.
  rewrite Forall_forall in Hidx.
  specialize (Hidx i Hin_i) as [Hi_ge _].
  assert (Hneq: i + 1 <> Zlength (l0 ++ [a0])).
  {
    apply Hgap.
    - apply in_app_iff. left. exact Hin_i.
    - apply in_app_iff. right. simpl. left.  reflexivity. 
  }
  unfold Zlength in *.
  rewrite length_app in Hi_lt, Hneq. 
  simpl in Hi_lt, Hneq. 
  lia.
Qed. 

Lemma sincr_app_cons_inv1:  forall l1 x,
  sincr (l1 ++ [x]) ->
  sincr l1.
Proof.
  intros l1 x Hsincr.
  destruct l1 as [| a l1']. 
  - simpl.  auto.
  - simpl in Hsincr |- *.
    revert a Hsincr.
    induction l1' as [| b l1'' IH]; intros a Hsincr. 
    + simpl in *. auto.
    + simpl in Hsincr |- *.
      destruct Hsincr as [Hab Hrest].
      split; [exact Hab |].
      apply IH.  exact Hrest.
Qed. 

Lemma feasible_set_app_x_inv_i_last_eq:  forall l x s il' i_last,
  i_last = Zlength l ->
  sincr (il' ++ [i_last]) ->
  (forall i j, In i (il' ++ [i_last]) -> In j (il' ++ [i_last]) -> i + 1 <> j) ->
  is_indexed_elements (l ++ [x]) (il' ++ [i_last]) s ->
  exists s', s = s' ++ [x] /\ feasible_set (removelast l) s'.
Proof.
  intros l x s il' i_last Heq_idx Hsincr Hgap Hidx.
  apply is_indexed_elements_app_inv_l in Hidx.
  destruct Hidx as [s1 [s2 [Hidx1 [Hidx2 Heq_s]]]].   
  subst s. 
  apply is_indexed_elements_cons_inv_l in Hidx2.
  destruct Hidx2 as [a [s2' [Hnth_last [Hidx2' Heq_s2]]]]. 
  apply is_indexed_elements_nil_inv_l in Hidx2'.  
  subst s2 s2'. 
  rewrite Heq_idx in Hnth_last. 
  rewrite Znth_error_snoc_last in Hnth_last.  
  injection Hnth_last as Heq_a. 
  subst a. 
  exists s1.
  split; [reflexivity |].  
  unfold feasible_set, non_adjacent_subseq.   
  exists il'. 
  split; [| split]. 
  -
    destruct (list_snoc_destruct l) as [Heq_l | [a0 [l0 Heq_l]]].  
    + 
      subst l.
      simpl in Heq_idx. 
      unfold Zlength in Heq_idx.  
      simpl in Heq_idx.  
      subst i_last. 
      apply feasible_set_app_x_inv_l_empty in Hidx1 as [Hil' Hs1]; auto. 
      subst il' s1.
      simpl. 
      apply is_indexed_elements_nil.  
    + 
      subst l.
      rewrite removelast_app by discriminate. 
      simpl.  rewrite app_nil_r. 
      assert (Hidx1_saved:  is_indexed_elements ((l0 ++ [a0]) ++ [x]) il' s1) by exact Hidx1.
      eapply Forall2_congr; [| exact Hidx1].   
      intros i a Hin_i Hin_s Hnth. 
      assert (Hlt:  i < Zlength l0).
      {
        eapply feasible_set_app_x_inv_idx_bound with (a0 := a0) (x := x) (il' := il').
        - 
          assert (Heq_i_last: i_last = Zlength (l0 ++ [a0])).
          { rewrite <- Heq_idx.  reflexivity.  }
          rewrite <- Heq_i_last.
          exact Hsincr.
        - 
          intros i' j' Hi' Hj'.  
          assert (Heq_i_last:   i_last = Zlength (l0 ++ [a0])).
          { rewrite <- Heq_idx. reflexivity. }
          rewrite <- Heq_i_last in Hi', Hj'.
          apply Hgap; auto.  
        - exact Hin_i.  
        - exists s1. exact Hidx1_saved.  
        - exists a.   exact Hnth. 
      }
      symmetry. 
      assert (Hnth_range:  0 <= i < Zlength ((l0 ++ [a0]) ++ [x])).
      { apply Znth_error_range in Hnth.  exact Hnth. }
      replace ((l0 ++ [a0]) ++ [x]) with (l0 ++ ([a0] ++ [x])) in Hnth by (rewrite app_assoc; reflexivity).
      rewrite Znth_error_app_l in Hnth. 
      * symmetry.  exact Hnth.
      * split. 
        -- destruct Hnth_range.  lia.
        -- exact Hlt.
  - 
    apply sincr_app_cons_inv1 with (x := i_last).
    exact Hsincr.
  - 
    intros i j Hi Hj. 
    apply Hgap. 
    + apply in_app_iff.   left.  exact Hi. 
    + apply in_app_iff. left.  exact Hj. 
Qed.  

Lemma feasible_set_app_x_inv_i_last_neq: forall l x s il' i_last,
  i_last <> Zlength l ->
  sincr (il' ++ [i_last]) ->
  (forall i j, In i (il' ++ [i_last]) -> In j (il' ++ [i_last]) -> i + 1 <> j) ->
  is_indexed_elements (l ++ [x]) (il' ++ [i_last]) s ->
  feasible_set l s.
Proof.
  intros l x s il' i_last Hneq Hsincr Hgap Hidx. 
  apply is_indexed_elements_app_inv_l in Hidx.
  destruct Hidx as [s1 [s2 [Hidx1 [Hidx2 Heq_s]]]].
  subst s. 
  apply is_indexed_elements_cons_inv_l in Hidx2.
  destruct Hidx2 as [a [s2' [Hnth_last [Hidx2' Heq_s2]]]].
  apply is_indexed_elements_nil_inv_l in Hidx2'. 
  subst s2 s2'.
  assert (Hi_last_range:  0 <= i_last < Zlength (l ++ [x])).
  { apply Znth_error_range in Hnth_last. exact Hnth_last. }
  assert (Hi_last_lt: i_last < Zlength l).
  {
    destruct Hi_last_range as [_ Hi_ub].
    rewrite Zlength_app in Hi_ub.
    unfold Zlength in Hi_ub at 2.
    simpl in Hi_ub. 
    lia.
  }
  assert (Hnth_last_l: Znth_error l i_last = Some a).
  {
    assert (Hnth_last_copy: Znth_error (l ++ [x]) i_last = Some a) by exact Hnth_last. 
    rewrite Znth_error_app_l in Hnth_last_copy. 
    - exact Hnth_last_copy.
    - split. 
      + apply Znth_error_range in Hnth_last.  lia.
      + exact Hi_last_lt.
  }
  unfold feasible_set, non_adjacent_subseq. 
  exists (il' ++ [i_last]).
  split; [| split].
  - 
    apply is_indexed_elements_app. 
    + 
      eapply Forall2_congr; [| exact Hidx1].
      intros i a' Hin_i Hin_s Hnth.  
      symmetry. 
      assert (Hi_lt_last: i < i_last).
      { apply sincr_app_singleton_inv with (l1 := il'); auto. }
      assert (Hnth_l: Znth_error l i = Some a').
      {
        assert (Hnth_copy: Znth_error (l ++ [x]) i = Some a') by exact Hnth. 
        rewrite Znth_error_app_l in Hnth_copy.
        - exact Hnth_copy. 
        - split.
          + apply Znth_error_range in Hnth.  lia.
          + lia.
      }
      symmetry. exact Hnth_l.
    + 
      apply is_indexed_elements_cons. 
      * exact Hnth_last_l.
      * apply is_indexed_elements_nil. 
  - 
    exact Hsincr.
  - 
    exact Hgap. 
Qed.

Lemma feasible_set_app_x_inv:  forall l x s,
  feasible_set (l ++ [x]) s ->
  feasible_set l s \/
  (exists s', s = s' ++ [x] /\ feasible_set (removelast l) s').
Proof.
  intros l x s H.
  unfold feasible_set, non_adjacent_subseq in H.
  destruct H as [il [Hidx [Hsincr Hgap]]].   
  
  destruct (list_snoc_destruct il) as [Heq_il | [i_last [il' Heq_il]]]; subst il.
  
  - 
    left.
    apply (feasible_set_app_x_inv_empty_il l x s); auto.
  
  -
    destruct (Z.eq_dec i_last (Zlength l)) as [Heq_idx | Hneq_idx]. 
    
    + 
      right.
      eapply (feasible_set_app_x_inv_i_last_eq l x s il' i_last); eassumption.
    
    + 
      left.
      eapply (feasible_set_app_x_inv_i_last_neq l x s il' i_last); eassumption. 
Qed.

Lemma max_value_spec_app:
  forall l x m1 m2,
    max_value_spec l m1 ->
    max_value_spec (removelast l) m2 ->
    max_value_spec (l ++ [x]) (Z.max m1 (m2 + x)).
Proof.
  intros l x m1 m2 Hspec1 Hspec2.
  assert (H1: (exists s, feasible_set l s /\ sum s = m1) /\ (forall t, feasible_set l t -> sum t <= m1)).
  {
    destruct Hspec1 as [Hcase1 | Hcase2].
    - destruct Hcase1 as [s [? [? ?]]]. split; [exists s; auto | auto].
    - destruct Hcase2 as [Hle Heq]. split; [| subst; auto].
      exists []. split.
      + exists []. split. apply is_indexed_elements_nil. split; [simpl; auto | intros; contradiction].
      + subst. reflexivity.
  }
  destruct H1 as [[s1 [Hfeas1 Hsum1]] Hmax1].

  assert (H2: (exists s, feasible_set (removelast l) s /\ sum s = m2) /\ (forall t, feasible_set (removelast l) t -> sum t <= m2)).
  {
    destruct Hspec2 as [Hcase1 | Hcase2].
    - destruct Hcase1 as [s [? [? ?]]]. split; [exists s; auto | auto].
    - destruct Hcase2 as [Hle Heq]. split; [| subst; auto].
      exists []. split.
      + exists []. split. apply is_indexed_elements_nil. split; [simpl; auto | intros; contradiction].
      + subst. reflexivity.
  }
  destruct H2 as [[s2 [Hfeas2 Hsum2]] Hmax2].
  apply Z.max_case_strong; intros Hle.
  - 
    left. exists s1. split; [| split].
    + apply feasible_set_app_x_l. assumption.
    + assumption.
    + intros t Ht.
      apply feasible_set_app_x_inv in Ht.
      destruct Ht as [Ht | [t' [Heq Ht']]].
      * 
        apply Hmax1. assumption.
      *
        subst t. rewrite sum_app. simpl. rewrite Z.add_0_r.
        specialize (Hmax2 t' Ht').
        lia.
  - 
    left. exists (s2 ++ [x]). split; [| split].
    + apply feasible_set_app_x_r. assumption.
    + rewrite sum_app. simpl. rewrite Z.add_0_r. rewrite Hsum2. reflexivity.
    + intros t Ht.
      apply feasible_set_app_x_inv in Ht.
      destruct Ht as [Ht | [t' [Heq Ht']]].
      * 
        specialize (Hmax1 t Ht). lia.
      * 
        subst t. rewrite sum_app. simpl. rewrite Z.add_0_r.
        specialize (Hmax2 t' Ht').
        lia.
Qed.

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
Proof.
  intros body l default I H_init H_step.
  assert (H_gen: forall l_rest b_curr l_done, 
            I l_done b_curr -> 
            Hoare (list_iter body l_rest b_curr) 
                  (fun b_final => I (l_done ++ l_rest) b_final)).
  {
    induction l_rest as [|x xs IH].
    - 
      intros b_curr l_done H_inv.
      simpl.
      rewrite app_nil_r.
      apply Hoare_ret.
      auto.
    - 
      intros b_curr l_done H_inv.
      simpl.
      eapply Hoare_bind.
      + 
        apply H_step.
        apply H_inv.
      + 
        intros b_next H_next.
        specialize (IH b_next (l_done ++ [x]) H_next).
        rewrite <- app_assoc in IH.
        auto.
  }
  specialize (H_gen l default [] H_init).
  simpl in H_gen.
  apply H_gen.
Qed.

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
           assert (Hmax: max_value_spec (done ++ [x]) (Z.max m1 (m2 + x))).
           { apply max_value_spec_app; auto. }
           replace (Z.max m1 (m2 + x)) with (m2 + x) in Hmax.
           ++ exact Hmax. 
           ++ symmetry. apply Z.max_r. lia. 
        --
           rewrite removelast_app_x.
           auto.
      *
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
    intros st. destruct st as [[[m1 ans1] m2] ans2].
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