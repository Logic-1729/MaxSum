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

Lemma is_indexed_elements_prefix_extend :
  forall (l : list Z) (x : Z) (s il : list Z),
    is_indexed_elements l il s ->
    is_indexed_elements (l ++ [x]) il s.
Proof.
  intros l x s il H.
  unfold is_indexed_elements in *.
  induction H as [| i a il' s' Hnth Hrest IH]; simpl.
  - apply Forall2_nil.
  - apply Forall2_cons.
    + assert (Hrange: 0 <= i < Zlength l).
      { apply Znth_error_range in Hnth. tauto. }
      rewrite (Znth_error_app_l _ _ _ Hrange).
      exact Hnth.
    + apply IH.
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
Lemma sum_single: forall x, sum [x] = x.
Proof. intros. simpl. apply Z.add_0_r. Qed.

Lemma sincr_tail: forall a l, sincr (a :: l) -> sincr l.
Proof.
  intros a l Hsincr. unfold sincr in *.
  destruct l as [|b l'].
  - simpl. auto.
  - simpl in Hsincr. simpl. inversion Hsincr; subst. assumption.
Qed.   

Lemma feasible_set_preserved: 
  forall l s t,
    feasible_set l t -> feasible_set (l ++ [s]) t.
Proof.
  intros l s t [il [Hidx [Hsincr Hgap]]].
  exists il. split; [| split; auto].
  - revert s l t Hsincr Hgap Hidx.  
    induction il as [|i il' IH]; intros s l t Hsincr Hgap Hidx.
    + inversion Hidx; subst. apply Forall2_nil.
    + destruct t as [|y t'].
      * inversion Hidx.
      * constructor.
        -- inversion Hidx; subst.
           assert (H_range: 0 <= i < Zlength l).
           { apply Znth_error_range in H2. tauto. }
           rewrite (Znth_error_app_l _ _ _ H_range). apply H2.
        -- inversion Hidx; subst. apply IH. 
           ++ apply (sincr_tail i il' Hsincr).
           ++ intros i0 j0 Hi0 Hj0. apply Hgap.
              ** right. apply Hi0.
              ** apply in_cons. apply Hj0.
           ++ apply H4.                
Qed.

Lemma last_In: 
  forall (l: list Z) (tail: Z),
    l <> [] -> In (last l tail) l.
Proof. 
  intros l tail H. induction l as [|a l' IH].
  - contradiction.
  - destruct l' as [|a' l''].
    + simpl. left. reflexivity.
    + simpl. right. apply IH. discriminate.
Qed.         

Lemma feasible_set_extend:
  forall (l: list Z) (s: Z) (t: list Z),
    feasible_set (removelast l) t -> 
    feasible_set (l ++ [s]) (t ++ [s]).
Proof.
  intros l s t Hfeas. unfold feasible_set, non_adjacent_subseq in Hfeas.
  destruct Hfeas as [il [Hidx [Hsincr Hgap]]].
  exists (il ++ [Zlength l]). repeat split. 
  - apply is_indexed_elements_app.
    + apply is_indexed_elements_extend. apply Hidx.
    + apply is_indexed_elements_cons.
      * apply Znth_error_snoc_last.
      * apply is_indexed_elements_nil.
  - apply sincr_extend_last.
    + apply Hsincr.
    + destruct il as [|i' il'].
      * left. reflexivity. 
      * right. apply is_indexed_elements_range in Hidx. 
        rewrite Forall_forall in Hidx.
        assert (Hlast_In: In(last (i' :: il') 0) (i' :: il')).
        { apply last_In. discriminate. }
        specialize (Hidx _ Hlast_In).
        destruct (list_snoc_destruct l) as [Heq_l | [a [l' Heq_l]]].
        -- subst l; simpl in *; unfold Zlength in *; simpl in *. lia.
        -- subst l. rewrite removelast_app in Hidx by discriminate.
           simpl in Hidx. rewrite app_nil_r in Hidx.
           rewrite Zlength_app. unfold Zlength in *.  simpl. lia.
  - intros x y Hx Hy. apply in_app_or in Hx. apply in_app_or in Hy.
    destruct Hx as [Hx_il | Hx_lt]; destruct Hy as [Hy_il | Hy_lt].
    + apply Hgap; tauto.
    + simpl in *. destruct Hy_lt as [Heq_y | Hf]; [|contradiction].
      subst y. apply is_indexed_elements_range in Hidx.
      rewrite Forall_forall in Hidx. specialize (Hidx _ Hx_il).
      destruct (list_snoc_destruct l) as [Heq_l | [a [l' Heq_l]]].
      * subst l. simpl in Hidx. unfold Zlength in *. simpl. lia.
      * subst l. rewrite removelast_app in Hidx by discriminate.
        simpl in Hidx. rewrite app_nil_r in Hidx.
        rewrite Zlength_app. unfold Zlength in *. simpl. lia.
    + simpl in *. destruct Hx_lt as [Heq_x | Hf]; [|contradiction]. 
      subst x. apply is_indexed_elements_range in Hidx. 
      rewrite Forall_forall in Hidx. specialize (Hidx _ Hy_il). 
      destruct (list_snoc_destruct l) as [Heq_l | [a [l' Heq_l]]]. 
      * subst l. simpl. unfold Zlength in *. simpl in *. lia.
      * subst l. rewrite removelast_app in Hidx by discriminate.
        simpl in Hidx. rewrite app_nil_r in Hidx. 
        rewrite Zlength_app. unfold Zlength in *. simpl. lia.
    + simpl in *. destruct Hx_lt as [Heq_x | Hf]; [|contradiction].
      destruct Hy_lt as [Heq_y | Hf]; [|contradiction]. subst x y. lia.    
Qed.

Theorem max_sum_full_correct :
  forall l,
    Hoare (max_sum l)
      (fun '(m, s) => max_sum_full_spec l m s).
Proof.
  intros l. unfold max_sum. eapply Hoare_bind.
  - eapply Hoare_list_iter with 
      (I := fun done st => 
              match st with 
                (m1, ans1, m2, ans2) => 
                  max_value_spec done m1 /\
                  max_value_spec (removelast done) m2 /\
                  feasible_set done ans1 /\ sum ans1 = m1 /\
                  feasible_set (removelast done) ans2 /\  sum ans2 = m2
              end).
    + simpl. repeat split.
      * apply max_value_spec_nil.
      * apply max_value_spec_nil.
      * apply feasible_set_nil_intro.
      * apply feasible_set_nil_intro.
    + intros x done st. destruct st as [[[m1 ans1] m2] ans2].
      intros [Hm1 [Hm2 [Hfeas1 [Hsum1 [Hfeas2 Hsum2]]]]]. apply Hoare_choice.
      * eapply Hoare_assume_bind. intros H_le. apply Hoare_ret. repeat split. 
        -- assert (Hmax: max_value_spec (done ++ [x]) (Z.max m1 (m2 + x))).
           { apply max_value_spec_app; auto. }
           replace (Z.max m1 (m2 + x)) with (m2 + x) in Hmax.
           ++ apply Hmax.
           ++ symmetry. apply Z.max_r. lia.
        -- rewrite removelast_app_x. apply Hm1.
        -- apply feasible_set_extend. tauto.
        -- simpl. rewrite sum_app, sum_single, Hsum2. reflexivity.
        -- rewrite removelast_app_x. apply Hfeas1.
        -- apply Hsum1.
      * eapply Hoare_assume_bind. intros H_ge. apply Hoare_ret. repeat split.
        -- assert (Hmax: max_value_spec (done ++ [x]) (Z.max m1 (m2 + x))).
           { apply max_value_spec_app; auto. }
           replace (Z.max m1 (m2 + x)) with m1 in Hmax.
           ++ apply Hmax.
           ++ symmetry. apply Z.max_l. lia.
        -- rewrite removelast_app_x. apply Hm1.
        -- apply feasible_set_preserved. assumption.
        -- assumption.
        -- rewrite removelast_app_x. apply Hfeas1.
        -- apply Hsum1.
  - intros st. destruct st as [[[m1 ans1] m2] ans2].
    intros [Hm1 [Hm2 [Hfeas1 [Hsum1 [_ _]]]]]. apply Hoare_ret.
    unfold max_sum_full_spec. repeat split; auto.
Qed.

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


Definition max_sum_lex_inv (done : list Z)
             (max1 : Z) (ans1 : list Z) (il1 : list Z)
             (max2 : Z) (ans2 : list Z) (il2 : list Z)
             (idx : Z) : Prop :=
  Zlength done = idx /\
  (* ans1 is optimal and lex-min for done *)
  max_sum_full_spec done max1 ans1 /\
  is_indexed_elements done il1 ans1 /\
  non_adjacent_in il1 /\
  (forall s' il',
     feasible_set done s' ->
     is_indexed_elements done il' s' ->
     non_adjacent_in il' ->
     sum s' = max1 ->
     index_lex_lt il1 il' \/ il1 = il') /\
  (* ans2 is optimal and lex-min for removelast done *)
  (match done with
   | [] => max2 = 0 /\ ans2 = [] /\ il2 = []
   | _ => max_sum_full_spec (removelast done) max2 ans2 /\
          is_indexed_elements (removelast done) il2 ans2 /\
          non_adjacent_in il2 /\
          (forall s' il',
             feasible_set (removelast done) s' ->
             is_indexed_elements (removelast done) il' s' ->
             non_adjacent_in il' ->
             sum s' = max2 ->
             index_lex_lt il2 il' \/ il2 = il')
   end).

Lemma proof_il'_nil :
  forall (s' il' : list Z)
    (H : feasible_set [] s')
    (H0 : is_indexed_elements [] il' s')
    (H1 : non_adjacent_in il')
    (H2 : sum s' = 0),
    [] = il'.
Proof.
  intros s' il' H H0 H1 H2.
  apply feasible_set_nil in H.
  subst s'.
  apply is_indexed_elements_nil_inv_r in H0.
  rewrite H0; reflexivity.
Qed.

Lemma idx_eq_zero (idx : Z) (Hlen : Zlength ([] : list Z) = idx) : idx = 0.
Proof.
  unfold Zlength in Hlen.
  simpl in Hlen.
  rewrite Hlen; reflexivity.
Qed.

Lemma In_0_non_adjacent :
  forall i j : Z, In i [0] -> In j [0] -> i + 1 <> j.
Proof.
  intros. destruct H, H0.
  ++ lia.
  ++ simpl in H0. tauto.
  ++ simpl in H. tauto.
  ++ simpl in H. tauto.
Qed.

Lemma is_indexed_elements_restrict :
  forall (l : list Z) (x : Z) (s il : list Z),
  is_indexed_elements (l ++ [x]) il s ->
  (forall i, In i il -> i < Zlength l) ->
  is_indexed_elements l il s.
Proof.
  intros l x s il Hidx Hbound.
  revert s Hidx.
  induction il as [|i il' IH]; intros s Hidx; simpl in *.
  - apply is_indexed_elements_nil_inv_l in Hidx.
    rewrite Hidx.
    apply is_indexed_elements_nil.
  - apply is_indexed_elements_cons_inv_l in Hidx as (a & s' & Hnth & Hrest & ->).
    apply is_indexed_elements_cons.
    + (* Goal: Znth_error l i = Some a *)
      (* From Hnth: Znth_error (l ++ [x]) i = Some a *)
      pose proof (Znth_error_range _ _ _ Hnth) as [Hge Hlt_full].
      (* Hbound gives: i < Zlength l *)
      assert (Hin: In i (i :: il')) by (left; reflexivity).
      specialize (Hbound i Hin) as Hlt.
      (* Now we have 0 <= i and i < Zlength l *)
      rewrite (Znth_error_app_l l [x] i (conj Hge Hlt)) in Hnth.
      exact Hnth.
    + (* Inductive step for il' *)
      apply IH.
      intros j Hj.
      apply Hbound.
      right. exact Hj. tauto.
Qed.

Lemma max_sum_full_spec_inv :
  forall (l : list Z) (m : Z) (s : list Z),
  max_sum_full_spec l m s ->
  max_value_spec l m /\ feasible_set l s /\ sum s = m.
Proof.
  intros l m s H.
  exact H.
Qed.

Lemma feasible_single :
  forall x : Z,
    feasible_set [x] [x].
Proof.
  unfold feasible_set, non_adjacent_subseq.
  exists [0].
  split.
  + unfold is_indexed_elements.
      constructor; [compute; reflexivity | constructor].
  + unfold non_adjacent_in; simpl.
    split; [tauto | intros i j Hi Hj; inversion Hi; inversion Hj; lia].
Qed.

Lemma Zlength_removelast : forall (A: Type) (l : list A),
  l <> [] -> Zlength (removelast l) = Zlength l - 1.
Proof.
  intros A l Hnonnil.
  induction l as [| a l'].
  - exfalso; contradiction.
  - destruct l' as [| b l''].
    + simpl removelast. simpl. unfold Zlength. tauto.
    + simpl removelast in *.
      assert (Hl'_nonnil : b :: l'' <> []) by (
        intros H; discriminate H
      ).
      rewrite Zlength_cons.
      rewrite Zlength_cons.
      rewrite (IHl' Hl'_nonnil).
      lia.
Qed.

Lemma in_singleton: forall {A} (a x : A), In x [a] <-> x = a.
Proof.
  split; intros H.
  - now inversion H.
  - subst; left; reflexivity.
Qed.


Lemma max_value_spec_single_positive :
  forall x : Z, x > 0 -> max_value_spec [x] x.
Proof.
  intros x Hx. left. exists [x]. repeat split.
  - apply feasible_single.
  - apply sum_single.
  - intros t Ht. unfold feasible_set, non_adjacent_subseq in *.
    destruct Ht as [il [Hidx Hnonadj]].
    assert (Ht_is_empty_or_x: t = [] \/ t = [x]).
    { 
      unfold is_indexed_elements in Hidx. destruct t as [|a t'].
      + left. auto.
      + right. apply is_indexed_elements_cons_inv_r in Hidx.
        destruct Hidx as [i [il' [Heq [Hnth Hrest]]]].
        assert (Hi: i = 0).
        { 
          apply Znth_error_range in Hnth. unfold Zlength in Hnth. simpl in Hnth. lia. 
        }
        subst i. assert (Ha: a = x).
        {
          assert (Hx_nth: Znth_error [x] 0 = Some x) by apply Znth_error_cons_0. 
          rewrite Hx_nth in Hnth. injection Hnth as Ha. symmetry. apply Ha.
        }
        subst a. assert (Ht'_nil: t' = []).
        {
          destruct t' as [|b t''].
          - reflexivity. 
          - exfalso. apply is_indexed_elements_cons_inv_r in Hrest.
            destruct Hrest as [j [il'' [Heq_il' [Hnth' Hrest']]]].
            apply Znth_error_range in Hnth'. simpl in Hnth'.
            destruct Hnonadj as [Hsincr _]. rewrite Heq in Hsincr.
            apply sincr_cons_tail_Forall_lt in Hsincr. rewrite Heq_il' in Hsincr.
            assert (Hj_in: In j (j :: il'')) by (left;reflexivity).
            assert (Hj_0: j = 0) by (unfold Zlength in Hnth'; simpl in Hnth'; lia).  
            rewrite Hj_0 in Hsincr.
            apply Forall_cons_iff in Hsincr.
            destruct Hsincr as [H0 _].
            lia.
        }
        rewrite Ht'_nil.
        reflexivity. 
    }
    destruct Ht_is_empty_or_x.
    + rewrite H; simpl; lia.
    + rewrite H; simpl; lia.
Qed.

(* 此时 x>0, 取x最大 *)
Lemma max_sum_lex_inv_single_positive :
  forall (l : list Z) (x : Z)
    (Hfull1 : max_sum_full_spec [] 0 [])
    (Hgap1 : non_adjacent_in [])
    (Hgt : x > 0)
    (Hlex1 : forall s' il',
               feasible_set [] s' ->
               is_indexed_elements [] il' s' ->
               non_adjacent_in il' -> sum s' = 0 ->
               index_lex_lt [] il' \/ [] = il')
    (Hidx0 : Zlength ([] : list Z) = 0),
  max_sum_lex_inv [x] x [x] [0] 0 [] [] 1.
Proof.
  intros l x Hfull1 Hgap1 Hgt Hlex1 Hidx0.
  unfold max_sum_lex_inv.
  repeat split.
  - apply max_value_spec_single_positive; tauto.
  - apply feasible_single.
  - apply sum_single.
  - (* is_indexed_elements [x] [0] [x] *)
    unfold is_indexed_elements.
    apply Forall2_cons.
    + simpl; reflexivity.
    + apply Forall2_nil.
  - apply In_0_non_adjacent.
  - intros s' il' Hfeas Hidx Hnonadj Hsum.
    change ([x]) with ([] ++ [x]) in Hfeas.
    apply feasible_set_app_x_inv in Hfeas as [Hl | [t' [Heq Ht']]].
    + exfalso. apply feasible_set_nil in Hl; subst s'. simpl in Hsum. lia.
    + subst s'. apply feasible_set_nil in Ht'; subst t'.
      simpl in Hidx.
      apply is_indexed_elements_cons_inv_r in Hidx.
      destruct Hidx as (i & il'' & Heq_il & Hnth & Hnil).
      subst il'.
      apply is_indexed_elements_nil_inv_r in Hnil; subst il''.
      apply Znth_error_range in Hnth.
      simpl in Hnth. assert (i = 0). { destruct Hnth; unfold Zlength in H0; simpl in H0; lia. }
      subst i.
      right. reflexivity.
  - simpl. apply max_value_spec_nil.
  - simpl. apply feasible_set_nil_intro.
  - simpl. apply is_indexed_elements_nil.
  - tauto.
  - apply Hlex1.
Qed.

(* 此时 x < max1 = 0, 不取就是最大 *)
Lemma max_sum_lex_inv_single_case :
  forall (l : list Z) (x max1 idx : Z) (ans1 il1 : list Z)
    (Hlen : Zlength ([] : list Z) = idx)
    (Hfull1 : max_sum_full_spec [] max1 ans1)
    (Hidx1 : is_indexed_elements [] il1 ans1)
    (Hgap1 : non_adjacent_in il1)
    (Hlex1 : forall s' il',
               feasible_set [] s' ->
               is_indexed_elements [] il' s' ->
               non_adjacent_in il' -> sum s' = max1 ->
               index_lex_lt il1 il' \/ il1 = il')
    (Hlt : x < max1),
  max_sum_lex_inv [x] max1 ans1 il1 max1 ans1 il1 (idx + 1).
Proof.
  intros l x max1 idx ans1 il1 Hlen Hfull1 Hidx1 Hgap1 Hlex1 Hlt.
  unfold max_sum_lex_inv.
  repeat split.

  - simpl in Hlen; unfold Zlength in Hlen; simpl in Hlen; rewrite <- Hlen; reflexivity.
  - pose proof (proj1 (proj2 Hfull1)) as Hfeas_ans.
    pose proof (proj2 (proj2 Hfull1)) as Hsum_ans.
    apply feasible_set_nil in Hfeas_ans. rewrite Hfeas_ans in Hsum_ans.
    simpl in Hsum_ans.  (* Hsum_ans : 0 = max1 *)
    subst max1.
    (* Now prove max_value_spec [x] 0 *)
    right.
    split.
    + intros s Hfeas.
      change ([x]) with ([] ++ [x]) in Hfeas.
      apply feasible_set_app_x_inv in Hfeas as [Hl | [t' [Heq Ht']]].
      * (* s feasible in [] => s = [] => sum = 0 *)
        apply feasible_set_nil in Hl; subst s; simpl; lia.
      * (* s = t' ++ [x], t' feasible in [] => t' = [], s = [x] *)
        apply feasible_set_nil in Ht'; subst t'. simpl in Heq; subst s.
        simpl. lia.  (* x < 0, so sum = x < 0 <= 0 *)
    + reflexivity.
  - (* feasible_set [x] ans1 *)
    apply max_sum_full_spec_inv in Hfull1 as [_ [Hfeas _]].
    apply feasible_set_nil in Hfeas; subst ans1.
    unfold feasible_set. unfold non_adjacent_subseq. exists []. split.
    * apply is_indexed_elements_nil.
    * unfold non_adjacent_in. split.
      -- unfold sincr. tauto.
      -- intros i j Hini Hinj. destruct Hini, Hinj.
  - apply (proj2 (proj2 Hfull1)).
  - (* is_indexed_elements [x] il1 ans1 *)
    apply max_sum_full_spec_inv in Hfull1 as [_ [Hfeas _]].
    apply feasible_set_nil in Hfeas; subst ans1.
    apply is_indexed_elements_nil_inv_r in Hidx1; subst il1.
    apply is_indexed_elements_nil.
  - apply (proj1 Hgap1).
  - apply (proj2 Hgap1).
  - (* lex min for [x] *)
    intros s' il' Hfeas Hidx Hnonadj Hsum.
    (* Extract ans1 = [], max1 = 0 *)
    pose proof (proj1 (proj2 Hfull1)) as Hfeas_ans.
    pose proof (proj2 (proj2 Hfull1)) as Hsum_ans.
    apply feasible_set_nil in Hfeas_ans; subst ans1.
    simpl in Hsum_ans.  (* Hsum_ans : 0 = max1 *)
    rewrite <- Hsum_ans in Hsum.   (* sum s' = 0 *)
    rewrite <- Hsum_ans in Hlt.    (* x < 0 *)
    change ([x]) with ([] ++ [x]) in Hfeas.
    apply feasible_set_app_x_inv in Hfeas as [Hl | [t' [Heq Ht']]].
    + (* s' = [] *)
      apply feasible_set_nil in Hl; subst s'.
      apply is_indexed_elements_nil_inv_r in Hidx; subst il'.
      apply is_indexed_elements_nil_inv_r in Hidx1; subst il1.
      right. reflexivity.
    + (* s' = t' ++ [x] *)
      apply feasible_set_nil in Ht'; subst t'.
      subst s'. simpl in Hsum.  (* Hsum : x = 0 *)
      lia.  (* x = 0 and x < 0 → contradiction *)
  - (* max_value_spec [] max1 *)
    simpl. apply (proj1 Hfull1).
  - (* feasible_set [] ans1 *)
    apply (proj1 (proj2 Hfull1)).
  - (* sum ans1 = max1 *)
    apply (proj2 (proj2 Hfull1)).
  - (* is_indexed_elements [] il1 ans1 *)
    apply Hidx1.
  - (* sincr il1 *)
    apply (proj1 Hgap1).
  - (* non-adjacent gap *)
    apply (proj2 Hgap1).
  - (* lex min for [] *)
    apply Hlex1.
Qed.

(* Hlt 矛盾 *)
Lemma max_sum_lex_inv_contradiction_case :
  forall (l : list Z) (x max1 idx : Z) (ans1 il1 : list Z)
    (Hlen : Zlength ([] : list Z) = idx)
    (Hfull1 : max_sum_full_spec [] max1 ans1)
    (Hidx1 : is_indexed_elements [] il1 ans1)
    (Hgap1 : non_adjacent_in il1)
    (Hlex1 : forall s' il',
               feasible_set [] s' ->
               is_indexed_elements [] il' s' ->
               non_adjacent_in il' -> sum s' = max1 ->
               index_lex_lt il1 il' \/ il1 = il')
    (Heq : x = max1)
    (Hlt : index_lex_lt ([] ++ [idx]) il1),
  max_sum_lex_inv [x] x [x] [idx] max1 ans1 il1 (idx + 1).
Proof.
  intros l x max1 idx ans1 il1 Hlen Hfull1 Hidx1 Hgap1 Hlex1 Heq Hlt.
  unfold max_sum_lex_inv.
  repeat split.

  - simpl in Hlen; unfold Zlength in Hlen; simpl in Hlen; rewrite <- Hlen; reflexivity.
  - pose proof (proj1 (proj2 Hfull1)) as Hfeas_ans.
    pose proof (proj2 (proj2 Hfull1)) as Hsum_ans.
    apply feasible_set_nil in Hfeas_ans. rewrite Hfeas_ans in Hsum_ans.
    simpl in Hsum_ans.  (* Hsum_ans : 0 = max1 *)
    subst max1.
    (* Now prove max_value_spec [x] 0 *)
    right.
    split.
    + intros s Hfeas.
      change ([x]) with ([] ++ [x]) in Hfeas.
      apply feasible_set_app_x_inv in Hfeas as [Hl | [t' [Heq Ht']]].
      * (* s feasible in [] => s = [] => sum = 0 *)
        apply feasible_set_nil in Hl; subst s; simpl; lia.
      * (* s = t' ++ [x], t' feasible in [] => t' = [], s = [x] *)
        apply feasible_set_nil in Ht'; subst t'. simpl in Heq; subst s.
        simpl. lia.  (* x < 0, so sum = x < 0 <= 0 *)
    + rewrite Hsum_ans. reflexivity.
  - apply feasible_single.
  - apply sum_single.
  - unfold is_indexed_elements.
    simpl in Hlen; unfold Zlength in Hlen; simpl in Hlen.
    constructor.
    + rewrite <- Hlen. reflexivity.
    + constructor.
  - intros i j Hini Hinj. destruct Hini, Hinj.
    + lia.
    + simpl in H0; tauto.
    + simpl in H; tauto.
    + simpl in H; tauto.
  - intros s' il' Hfeas Hidx Hnonadj Hsum.
    (* First, get ans1 = [] *)
    pose proof (proj1 (proj2 Hfull1)) as Hfeas_ans.
    apply feasible_set_nil in Hfeas_ans; subst ans1.
    change ([x]) with ([] ++ [x]) in Hfeas.
    apply feasible_set_app_x_inv in Hfeas as [Hl | [t' [Heq_s Ht']]].
    + (* s' = [] *)
      apply feasible_set_nil in Hl; subst s'.
      apply is_indexed_elements_nil_inv_r in Hidx; subst il'.
      (* Now Hidx1 : is_indexed_elements [] il1 [] *)
      apply is_indexed_elements_nil_inv_r in Hidx1; subst il1.
      left. exact Hlt.
    + (* s' = [x] *)
      pose proof (proj2 (proj2 Hfull1)) as Hsum_ans.
      simpl in Hsum_ans. rewrite <- Heq in Hsum_ans.  (* x = 0 *)
      apply feasible_set_nil in Ht'; subst t'. subst s'.
      apply is_indexed_elements_cons_inv_r in Hidx.
      destruct Hidx as (i & il'' & Heq_il & Hnth & Hnil).
      subst il'.
      apply is_indexed_elements_nil_inv_r in Hnil; subst il''.
      apply Znth_error_range in Hnth.
      simpl in Hnth. assert (i = 0). { destruct Hnth; unfold Zlength in H0; simpl in H0; lia. }
      subst i.
      simpl in Hlen; unfold Zlength in Hlen; simpl in Hlen.
      rewrite Hlen.
      right. reflexivity.
- simpl. apply (proj1 Hfull1).
- apply (proj1 (proj2 Hfull1)).
- apply (proj2 (proj2 Hfull1)).
- apply Hidx1.
- apply (proj1 Hgap1).
- apply (proj2 Hgap1).
- apply Hlex1.
Qed.

Lemma max_sum_lex_inv_valid_case :
  forall (l : list Z) (x max1 idx : Z) (ans1 il1 : list Z)
    (Hlen : Zlength ([] : list Z) = idx)
    (Hfull1 : max_sum_full_spec [] max1 ans1)
    (Hidx1 : is_indexed_elements [] il1 ans1)
    (Hgap1 : non_adjacent_in il1)
    (Hlex1 : forall s' il',
               feasible_set [] s' ->
               is_indexed_elements [] il' s' ->
               non_adjacent_in il' -> sum s' = max1 ->
               index_lex_lt il1 il' \/ il1 = il')
    (Heq : x = max1)
    (Hnlt : ~ index_lex_lt ([] ++ [idx]) il1),
  max_sum_lex_inv [x] max1 ans1 il1 max1 ans1 il1 (idx + 1).
Proof.
  intros l x max1 idx ans1 il1 Hlen Hfull1 Hidx1 Hgap1 Hlex1 Heq Hnlt.
  unfold max_sum_lex_inv.
  repeat split.
  - simpl in Hlen; unfold Zlength in Hlen; simpl in Hlen; rewrite <- Hlen; reflexivity.
  - pose proof (proj1 (proj2 Hfull1)) as Hfeas.
    pose proof (proj2 (proj2 Hfull1)) as Hsum.
    apply feasible_set_nil in Hfeas.
    subst ans1.
    simpl in Hsum.
    subst max1.
    right; split.
    + intros s Hfeas_s.
      change ([x]) with ([] ++ [x]) in Hfeas_s.
      apply feasible_set_app_x_inv in Hfeas_s as [Hl | [t' [Heq Ht']]].
      * apply feasible_set_nil in Hl; subst s; simpl; lia.
      * apply feasible_set_nil in Ht'; subst t'; subst s; simpl; lia.
    + rewrite Hsum; reflexivity.
  - (* Goal 3: feasible_set [x] ans1 *)
    pose proof (proj1 (proj2 Hfull1)) as Hfeas.
    apply feasible_set_nil in Hfeas; subst ans1.
    unfold feasible_set. unfold non_adjacent_subseq. exists []. split.
    + apply is_indexed_elements_nil.
    + unfold non_adjacent_in; split.
      * unfold sincr; tauto.
      * intros i j Hini Hinj. destruct Hini, Hinj.
  - (* Goal 4: sum ans1 = max1 *)
    pose proof (proj1 (proj2 Hfull1)) as Hfeas.
    pose proof (proj2 (proj2 Hfull1)) as Hsum.
    apply feasible_set_nil in Hfeas; subst ans1.
    apply Hsum.
  - (* Goal 5: is_indexed_elements [x] il1 ans1 *)
    pose proof (proj1 (proj2 Hfull1)) as Hfeas.
    apply feasible_set_nil in Hfeas. subst ans1.
    apply is_indexed_elements_nil_inv_r in Hidx1. subst il1.
    apply is_indexed_elements_nil.
  - (* Goal 6: sincr il1 *)
    pose proof (proj1 (proj2 Hfull1)) as Hfeas_ans.
    apply feasible_set_nil in Hfeas_ans. subst ans1.
    pose proof (proj2 (proj2 Hfull1)) as Hsum_ans. simpl in Hsum_ans. subst max1.
    apply is_indexed_elements_nil_inv_r in Hidx1. subst il1. unfold sincr; tauto.
  - (* Goal 7: gap condition *)
    pose proof (proj1 (proj2 Hfull1)) as Hfeas_ans.
    apply feasible_set_nil in Hfeas_ans. subst ans1.
    apply is_indexed_elements_nil_inv_r in Hidx1; subst il1.
    intros i j Hi Hj; contradiction.
  - (* Goal 8: lex min for [x] *)
    pose proof (proj1 (proj2 Hfull1)) as Hfeas.
    pose proof (proj2 (proj2 Hfull1)) as Hsum.
    apply feasible_set_nil in Hfeas; subst ans1.
    simpl in Hsum; subst max1.
    apply is_indexed_elements_nil_inv_r in Hidx1; subst il1.
    intros s' il' Hfeas' Hidx' Hnonadj' Hsum'.
    change ([x]) with ([] ++ [x]) in Hfeas'.
    apply feasible_set_app_x_inv in Hfeas' as [Hl | [t' [Heq_s Ht']]].
    + apply feasible_set_nil in Hl; subst s'.
      apply is_indexed_elements_nil_inv_r in Hidx'; subst il'.
      right; reflexivity.
    + apply feasible_set_nil in Ht'; subst t'; subst s'.
      apply is_indexed_elements_cons_inv_r in Hidx'.
      destruct Hidx' as (i & il'' & -> & Hnth & Hnil).
      apply is_indexed_elements_nil_inv_r in Hnil; subst il''.
      apply Znth_error_range in Hnth.
      assert (i = 0) by (destruct Hnth; unfold Zlength in *; simpl in *; lia).
      subst i.
      left; simpl; auto.
  - (* Goal 9: max_value_spec (removelast [x]) max1 *)
    pose proof (proj1 (proj2 Hfull1)) as Hfeas.
    apply feasible_set_nil in Hfeas. subst ans1.
    pose proof (proj2 (proj2 Hfull1)) as Hsum.
    simpl in Hsum. subst max1.
    assert (removelast [x] = []) by reflexivity. subst.
    apply max_value_spec_nil.
  - (* Goal 10: feasible_set (removelast [x]) ans1 *)
    pose proof (proj1 (proj2 Hfull1)) as Hfeas.
    apply feasible_set_nil in Hfeas; subst ans1.
    apply feasible_set_nil_intro.
  - (* Goal 11: sum ans1 = max1 *)
    exact (proj2 (proj2 Hfull1)).
  - (* Goal 12: is_indexed_elements (removelast [x]) il1 ans1 *)
    pose proof (proj1 (proj2 Hfull1)) as Hfeas.
    apply feasible_set_nil in Hfeas. subst ans1.
    apply is_indexed_elements_nil_inv_r in Hidx1; subst il1.
    pose proof (proj1 (proj2 Hfull1)) as Hfeas.
    apply feasible_set_nil in Hfeas.
    apply is_indexed_elements_nil.
  - (* Goal 13: sincr il1 *)
    pose proof (proj1 (proj2 Hfull1)) as Hfeas.
    apply feasible_set_nil in Hfeas. subst ans1.
    apply is_indexed_elements_nil_inv_r in Hidx1; subst il1.
    simpl; auto.
  - (* Goal 14: gap condition *)
    pose proof (proj1 (proj2 Hfull1)) as Hfeas.
    apply feasible_set_nil in Hfeas. subst ans1.
    apply is_indexed_elements_nil_inv_r in Hidx1; subst il1.
    intros i j Hi Hj; contradiction.
  - (* Goal 15: lex min for removelast [x] = [] *)
    pose proof (proj1 (proj2 Hfull1)) as Hfeas.
    apply feasible_set_nil in Hfeas; subst ans1.
    apply is_indexed_elements_nil_inv_r in Hidx1; subst il1.
    pose proof (proj2 (proj2 Hfull1)) as Hsum.
    simpl in Hsum; subst max1.
    intros s' il' Hfeas' Hidx' Hnonadj' Hsum'.
    apply feasible_set_nil in Hfeas'; subst s'.
    apply is_indexed_elements_nil_inv_r in Hidx'; subst il'.
    right; reflexivity.
Qed.

Lemma index_lex_lt_extend_app_both :  
  forall (d0 x max1 max2 idx : Z) (drest ans2 il2 : list Z) (s' il' : list Z),
    Zlength (d0 :: drest) = idx ->
    max_sum_full_spec (removelast (d0 :: drest)) max2 ans2 ->
    is_indexed_elements (removelast (d0 :: drest)) il2 ans2 ->
    non_adjacent_in il2 ->
    (forall s' il',
       feasible_set (removelast (d0 :: drest)) s' ->
       is_indexed_elements (removelast (d0 :: drest)) il' s' ->
       non_adjacent_in il' -> sum s' = max2 ->
       index_lex_lt il2 il' \/ il2 = il') ->
    max2 + x > max1 ->
    feasible_set ((d0 :: drest) ++ [x]) s' ->
    is_indexed_elements ((d0 :: drest) ++ [x]) il' s' ->
    non_adjacent_in il' ->
    sum s' = max2 + x ->
    index_lex_lt (il2 ++ [idx]) il' \/ il2 ++ [idx] = il'.  
Proof.
Admitted.

Lemma max_sum_lex_inv_extend_case :
  forall (d0 x max1 max2 idx : Z) (drest ans1 il1 ans2 il2 : list Z)
    (Hlen : Zlength (d0 :: drest) = idx)
    (Hfull1 : max_sum_full_spec (d0 :: drest) max1 ans1)
    (Hidx1 : is_indexed_elements (d0 :: drest) il1 ans1)
    (Hgap1 : non_adjacent_in il1)
    (Hlex1 : forall s' il',
               feasible_set (d0 :: drest) s' ->
               is_indexed_elements (d0 :: drest) il' s' ->
               non_adjacent_in il' -> sum s' = max1 ->
               index_lex_lt il1 il' \/ il1 = il')
    (Hfull2 : max_sum_full_spec (removelast (d0 :: drest)) max2 ans2)
    (Hidx2 : is_indexed_elements (removelast (d0 :: drest)) il2 ans2)
    (Hgap2 : non_adjacent_in il2)
    (Hlex2 : forall s' il',
               feasible_set (removelast (d0 :: drest)) s' ->
               is_indexed_elements (removelast (d0 :: drest)) il' s' ->
               non_adjacent_in il' -> sum s' = max2 ->
               index_lex_lt il2 il' \/ il2 = il')
    (Hgt : max2 + x > max1),
  max_sum_lex_inv ((d0 :: drest) ++ [x]) (max2 + x) (ans2 ++ [x]) (il2 ++ [idx]) max1 ans1 il1 (idx + 1).
Proof.
  intros d0 x max1 max2 idx drest ans1 il1 ans2 il2 Hlen Hfull1 Hidx1 Hgap1 Hlex1 Hfull2 Hidx2 Hgap2 Hlex2 Hgt.
  unfold max_sum_lex_inv.
  repeat split.

  - rewrite Zlength_app. rewrite Hlen. reflexivity.
  - (* Goal2 max_value_spec ((d0 :: drest) ++ [x]) (max2 + x) *)
    left.
    exists (ans2 ++ [x]).
    split.
    + apply feasible_set_extend.
      apply (proj1 (proj2 Hfull2)).
    + split.
      * rewrite sum_app, sum_single.
        rewrite (proj2 (proj2 Hfull2)). reflexivity.
      * intros t Hfeas.
        apply feasible_set_app_x_inv in Hfeas as [Hleft | [t1 [-> Ht1]]].
        -- pose proof (proj1 Hfull1) as Hspec1.
           destruct Hspec1 as [Hexists | [Hle_all Hmax0]].
           ++ destruct Hexists as (s0 & Hfeas0 & Hsum0 & Hbound).
              specialize (Hbound t Hleft). lia.
           ++ specialize (Hle_all t Hleft). lia.
        -- pose proof (proj1 Hfull2) as Hspec2.
           destruct Hspec2 as [Hexists | [Hle_all Hmax0]].
           ++ destruct Hexists as (s2 & Hfeas2 & Hsum2 & Hbound).
              specialize (Hbound t1 Ht1). rewrite sum_app. simpl; lia.
           ++ specialize (Hle_all t1 Ht1). rewrite sum_app. simpl; lia.
  - apply feasible_set_extend.
    apply (proj1 (proj2 Hfull2)).
  - rewrite sum_app, sum_single.
    rewrite (proj2 (proj2 Hfull2)). reflexivity.
  - apply is_indexed_elements_app.
    + apply is_indexed_elements_extend.
      exact Hidx2.
    + apply is_indexed_elements_cons.
      * rewrite <- Hlen. apply Znth_error_snoc_last.
      * apply is_indexed_elements_nil.
  - apply sincr_extend_last.
    + apply (proj1 Hgap2).
    + destruct il2 as [|i0 il2'].
      * left; reflexivity.
      * right.
        assert (Hrem_len: Zlength (removelast (d0 :: drest)) = Zlength (d0 :: drest) - 1).
        { apply Zlength_removelast. discriminate. }
        pose proof (is_indexed_elements_range _ _ _ Hidx2) as Hrange_full.
        rewrite Forall_forall in Hrange_full.
        assert (Hlast_in: In (last (i0 :: il2') 0) (i0 :: il2')) by (apply last_In; discriminate).
        specialize (Hrange_full _ Hlast_in).
        (* Now: last ... < Zlength (removelast (d0::drest)) = Zlength (d0::drest) - 1 = idx - 1 *)
        rewrite Hrem_len in Hrange_full.
        rewrite Hlen in Hrange_full.  (* Zlength (d0::drest) = idx *)
        lia.
  - intros i j Hi Hj.
    apply in_app_or in Hi.
    apply in_app_or in Hj.
    destruct Hi as [Hi_il2 | Hi_idx]; destruct Hj as [Hj_il2 | Hj_idx].
    + (* i, j in il2 *)
      apply (proj2 Hgap2); auto.
    + assert (Hj_eq: j = idx).
      { apply in_singleton in Hj_idx. exact Hj_idx. }
      subst j.
      assert (Hrem_len: Zlength (removelast (d0 :: drest)) = Zlength (d0 :: drest) - 1).
      { unfold Zlength; destruct drest. simpl. reflexivity. apply Zlength_removelast. discriminate. }
      pose proof (is_indexed_elements_range _ _ _ Hidx2) as Hrange.
      rewrite Forall_forall in Hrange.
      specialize (Hrange i Hi_il2).
      rewrite Hrem_len in Hrange.
      rewrite Hlen in Hrange.
      lia.
    + (* i = idx, j in il2 *)
      assert (Hi_eq: i = idx) by (apply in_singleton in Hi_idx; exact Hi_idx).
      subst i.
      assert (Hrem_len: Zlength (removelast (d0 :: drest)) = Zlength (d0 :: drest) - 1).
      { apply Zlength_removelast. discriminate. }
      pose proof (is_indexed_elements_range _ _ _ Hidx2) as Hrange.
      rewrite Forall_forall in Hrange.
      specialize (Hrange j Hj_il2).
      rewrite Hrem_len, Hlen in Hrange.
      lia.
    + (* i = idx, j = idx *)
      assert (Hi_eq: i = idx) by (apply in_singleton in Hi_idx; exact Hi_idx).
      assert (Hj_eq: j = idx) by (apply in_singleton in Hj_idx; exact Hj_idx).
      subst i j.
      lia.
  - intros s' il' Hfeas Hidx' Hnonadj Hsum. 
    assert (Hfeas_backup : feasible_set ((d0 :: drest) ++ [x]) s') by exact Hfeas.
    apply feasible_set_app_x_inv in Hfeas as [Hleft | [t' [Heq Ht']]].
    + exfalso.
      assert (Hle: sum s' <= max1).
      { destruct (proj1 Hfull1) as [Hcase1 | Hcase2].   
        - destruct Hcase1 as (s0 & Hfeas0 & Hsum0 & Hbound).
          apply Hbound; exact Hleft.
        - destruct Hcase2 as (Hle_all & Hmax0).
          rewrite Hmax0.
          apply Hle_all; exact Hleft. 
      }
      lia. 
    + apply (index_lex_lt_extend_app_both d0 x max1 max2 idx drest ans2 il2 s' il' 
               Hlen Hfull2 Hidx2 Hgap2 Hlex2 Hgt Hfeas_backup Hidx' Hnonadj Hsum).
  - rewrite removelast_app_x. apply (proj1 Hfull1).
  - rewrite removelast_app_x. apply (proj1 (proj2 Hfull1)).
  - apply (proj2 (proj2 Hfull1)).
  - rewrite removelast_app_x. exact Hidx1.
  - apply (proj1 Hgap1).
  - apply (proj2 Hgap1).
  - rewrite removelast_app_x. exact Hlex1.
Qed.

Lemma index_lex_preserve_when_extend_list :
  forall (l :  list Z) (x : Z) (s' il' il1 ans1 : list Z) (max1 :  Z),
    l <> [] ->
    max_sum_full_spec l max1 ans1 ->
    is_indexed_elements l il1 ans1 ->
    non_adjacent_in il1 ->
    (forall s' il',
       feasible_set l s' ->
       is_indexed_elements l il' s' ->
       non_adjacent_in il' ->
       sum s' = max1 ->
       index_lex_lt il1 il' \/ il1 = il') ->
    feasible_set l s' ->
    is_indexed_elements (l ++ [x]) il' s' ->
    non_adjacent_in il' ->
    sum s' = max1 ->
    index_lex_lt il1 il' \/ il1 = il'.
Proof. 
Admitted.

Lemma max_sum_lex_inv_preserve_when_not_taken :
  forall (l : list Z) (x max1 max2 : Z) (ans1 ans2 il1 : list Z),
    l <> [] ->
    max_sum_full_spec l max1 ans1 ->
    is_indexed_elements l il1 ans1 ->
    non_adjacent_in il1 ->
    (forall s' il',
       feasible_set l s' ->
       is_indexed_elements l il' s' ->
       non_adjacent_in il' ->
       sum s' = max1 ->
       index_lex_lt il1 il' \/ il1 = il') ->
    max_sum_full_spec (removelast l) max2 ans2 ->
    max2 + x < max1 ->
    max_sum_lex_inv (l ++ [x]) max1 ans1 il1 max1 ans1 il1 (Zlength l + 1).
Proof.
  intros l x max1 max2 ans1 ans2 il1 Hneq Hfull1 Hidx1 Hgap1 Hlex1 Hfull2 Hlt.
  unfold max_sum_lex_inv.
  repeat split. 

  - apply Zlength_app.
  - assert (Hspec1: max_value_spec l max1) by (apply (proj1 Hfull1)).
    assert (Hspec2: max_value_spec (removelast l) max2) by (apply (proj1 Hfull2)).
    assert (Hspec_app: max_value_spec (l ++ [x]) (Z.max max1 (max2 + x))).
    { apply max_value_spec_app. exact Hspec1. exact Hspec2. }
    replace (Z.max max1 (max2 + x)) with max1 in Hspec_app. 
    + exact Hspec_app.
    + symmetry. apply Z.max_l. lia.
  - apply feasible_set_app_x_l. 
    apply (proj1 (proj2 Hfull1)).
  - apply (proj2 (proj2 Hfull1)).
  - apply is_indexed_elements_prefix_extend.
    tauto.
  - apply (proj1 Hgap1).
  - apply (proj2 Hgap1).
  - intros s' il' Hfeas Hidx' Hnonadj Hsum.
    apply feasible_set_app_x_inv in Hfeas as [Hfeas_l | [t' [Heq Ht']]].
    + (* s' 是 l 的可行解 *)
      apply (index_lex_preserve_when_extend_list l x s' il' il1 ans1 max1 
               Hneq Hfull1 Hidx1 Hgap1 Hlex1 Hfeas_l Hidx' Hnonadj Hsum).
    + (* s' = t' ++ [x] *)
      exfalso.
      assert (Hsum_t': sum t' <= max2).
      {
        pose proof (proj1 Hfull2) as Hspec2.
        destruct Hspec2 as [Hexists | [Hle Hm0]].
        - destruct Hexists as (s0 & _ & _ & Hbound).
          apply Hbound; exact Ht'. 
        - pose proof Hle t' Ht'. rewrite <- Hm0 in H. apply H.
      }
      rewrite Heq in Hsum. pose proof sum_app t' [x].
      rewrite H in Hsum. simpl in Hsum. lia.
  - rewrite removelast_app_x by (discriminate Hneq).
    destruct l as [|a l'].
    + tauto.
    + simpl. 
      repeat split; auto. 
      unfold max_sum_full_spec in Hfull1.
      * destruct Hfull1 as [H1 [_ _]]; tauto.
      * destruct Hfull1 as [_ [H2 _]]; tauto.
      * destruct Hfull1 as [_ [_ H3]]; tauto. 
      * unfold non_adjacent_in in Hgap1; destruct Hgap1; tauto.
      * unfold non_adjacent_in in Hgap1. apply Hgap1.
Qed.

Lemma index_lex_preserve_eq_case :
  forall (d0 x :  Z) (drest ans1 il1 ans2 il2 : list Z) (max1 max2 idx : Z)
    (s' il' : list Z),
    Zlength (d0 :: drest) = idx ->
    max_sum_full_spec (d0 :: drest) max1 ans1 ->
    is_indexed_elements (d0 :: drest) il1 ans1 ->
    non_adjacent_in il1 ->
    (forall s' il',
       feasible_set (d0 :: drest) s' ->
       is_indexed_elements (d0 :: drest) il' s' ->
       non_adjacent_in il' -> sum s' = max1 ->
       index_lex_lt il1 il' \/ il1 = il') ->
    max_sum_full_spec (removelast (d0 :: drest)) max2 ans2 ->
    is_indexed_elements (removelast (d0 :: drest)) il2 ans2 ->
    non_adjacent_in il2 ->
    (forall s' il',
       feasible_set (removelast (d0 :: drest)) s' ->
       is_indexed_elements (removelast (d0 :: drest)) il' s' ->
       non_adjacent_in il' -> sum s' = max2 ->
       index_lex_lt il2 il' \/ il2 = il') ->
    max2 + x = max1 ->
    index_lex_lt (il2 ++ [idx]) il1 ->
    feasible_set ((d0 :: drest) ++ [x]) s' ->
    is_indexed_elements ((d0 :: drest) ++ [x]) il' s' ->
    non_adjacent_in il' ->
    sum s' = max2 + x ->
    index_lex_lt (il2 ++ [idx]) il' \/ il2 ++ [idx] = il'. 
Proof. 
Admitted.

Lemma max_sum_lex_inv_eq_case : 
  forall (l : list Z) (x d0 : Z) (drest ans1 il1 ans2 il2 : list Z) (max1 max2 idx : Z)
    (Hlen :  Zlength (d0 :: drest) = idx)
    (Hfull1 : max_sum_full_spec (d0 :: drest) max1 ans1)
    (Hidx1 : is_indexed_elements (d0 :: drest) il1 ans1)
    (Hgap1 : non_adjacent_in il1)
    (Hlex1 : forall s' il',
               feasible_set (d0 :: drest) s' ->
               is_indexed_elements (d0 :: drest) il' s' ->
               non_adjacent_in il' -> sum s' = max1 ->
               index_lex_lt il1 il' \/ il1 = il')
    (Hfull2 : max_sum_full_spec (removelast (d0 :: drest)) max2 ans2)
    (Hidx2 : is_indexed_elements (removelast (d0 :: drest)) il2 ans2)
    (Hgap2 : non_adjacent_in il2)
    (Hlex2 : forall s' il',
               feasible_set (removelast (d0 ::  drest)) s' ->
               is_indexed_elements (removelast (d0 :: drest)) il' s' ->
               non_adjacent_in il' -> sum s' = max2 ->
               index_lex_lt il2 il' \/ il2 = il')
    (Heq : max2 + x = max1)
    (Hlex : index_lex_lt (il2 ++ [idx]) il1),
  max_sum_lex_inv ((d0 :: drest) ++ [x]) (max2 + x) (ans2 ++ [x]) (il2 ++ [idx]) max1 ans1 il1 (idx + 1).
Proof.
  intros l x d0 drest ans1 il1 ans2 il2 max1 max2 idx Hlen Hfull1 Hidx1 Hgap1 Hlex1 Hfull2 Hidx2 Hgap2 Hlex2 Heq Hlex.
  unfold max_sum_lex_inv.
  repeat split. 

  - rewrite Zlength_app. rewrite Hlen.  unfold Zlength; simpl; reflexivity.
  - assert (Hspec1 := proj1 Hfull1).
    assert (Hspec2 := proj1 Hfull2).
    pose proof (max_value_spec_app (d0 :: drest) x max1 max2 Hspec1 Hspec2) as Hspec_app. 
    assert (Hmax : Z.max max1 (max2 + x) = max2 + x).
    {
      rewrite Heq. 
      apply Z.max_idempotent.
    }
    rewrite Hmax in Hspec_app.
    exact Hspec_app.
  - apply feasible_set_extend. apply (proj1 (proj2 Hfull2)).
  - rewrite sum_app, sum_single. rewrite (proj2 (proj2 Hfull2)). reflexivity.
  - apply is_indexed_elements_app.
    + apply is_indexed_elements_extend; exact Hidx2.
    + apply is_indexed_elements_cons.
      * rewrite <- Hlen. apply Znth_error_snoc_last.
      * apply is_indexed_elements_nil.
  - apply sincr_extend_last. 
    + apply (proj1 Hgap2).
    + destruct il2 as [|i0 il2']. 
      * left; reflexivity. 
      * right.
        assert (Hrem: Zlength (removelast (d0 ::  drest)) = idx - 1).
        { rewrite Zlength_removelast. rewrite Hlen. reflexivity. discriminate. }
        pose proof (is_indexed_elements_range _ _ _ Hidx2) as Hrange.
        rewrite Forall_forall in Hrange.
        assert (Hlast: In (last (i0 :: il2') 0) (i0 :: il2')) by (apply last_In; discriminate).
        specialize (Hrange _ Hlast).
        rewrite Hrem in Hrange. lia. 
  - intros i j Hi Hj.
    apply in_app_or in Hi; apply in_app_or in Hj.
    destruct Hi as [Hi2 | Hi_eq]; destruct Hj as [Hj2 | Hj_eq].
    + apply (proj2 Hgap2); tauto.
    + apply in_singleton in Hj_eq; subst j.
      assert (Hrem: Zlength (removelast (d0 :: drest)) = idx - 1).
      { rewrite Zlength_removelast.  rewrite Hlen; reflexivity. discriminate. }
      pose proof (is_indexed_elements_range _ _ _ Hidx2) as Hrange.
      rewrite Forall_forall in Hrange; specialize (Hrange i Hi2).
      rewrite Hrem in Hrange; lia.
    + apply in_singleton in Hi_eq; subst i.
      assert (Hrem: Zlength (removelast (d0 :: drest)) = idx - 1).
      { rewrite Zlength_removelast.  rewrite Hlen; reflexivity. discriminate. }
      pose proof (is_indexed_elements_range _ _ _ Hidx2) as Hrange.
      rewrite Forall_forall in Hrange; specialize (Hrange j Hj2).
      rewrite Hrem in Hrange; lia. 
    + apply in_singleton in Hi_eq; apply in_singleton in Hj_eq; subst i j; lia. 
  - intros s' il' Hfeas Hidx' Hnonadj Hsum.
    apply (index_lex_preserve_eq_case d0 x drest ans1 il1 ans2 il2 max1 max2 idx s' il'
             Hlen Hfull1 Hidx1 Hgap1 Hlex1 Hfull2 Hidx2 Hgap2 Hlex2 Heq Hlex 
             Hfeas Hidx' Hnonadj Hsum).
  - rewrite removelast_app_x. apply (proj1 Hfull1).
  - rewrite removelast_app_x. apply (proj1 (proj2 Hfull1)).
  - apply (proj2 (proj2 Hfull1)).
  - rewrite removelast_app_x. exact Hidx1.
  - apply (proj1 Hgap1).
  - apply (proj2 Hgap1).
  - rewrite removelast_app_x. apply Hlex1.
Qed.

Lemma index_lex_preserve_eq_nlex_case :
  forall (d0 x : Z) (drest ans1 il1 ans2 il2 : list Z) (max1 max2 idx : Z)
    (s' il' : list Z),
    Zlength (d0 :: drest) = idx ->
    max_sum_full_spec (d0 :: drest) max1 ans1 ->
    is_indexed_elements (d0 :: drest) il1 ans1 ->
    non_adjacent_in il1 ->
    (forall s' il',
       feasible_set (d0 :: drest) s' ->
       is_indexed_elements (d0 :: drest) il' s' ->
       non_adjacent_in il' -> sum s' = max1 ->
       index_lex_lt il1 il' \/ il1 = il') ->
    max_sum_full_spec (removelast (d0 :: drest)) max2 ans2 ->
    is_indexed_elements (removelast (d0 :: drest)) il2 ans2 ->
    non_adjacent_in il2 ->
    (forall s' il',
       feasible_set (removelast (d0 :: drest)) s' ->
       is_indexed_elements (removelast (d0 :: drest)) il' s' ->
       non_adjacent_in il' -> sum s' = max2 ->
       index_lex_lt il2 il' \/ il2 = il') ->
    max2 + x = max1 ->
    ~ index_lex_lt (il2 ++ [idx]) il1 ->
    feasible_set ((d0 ::  drest) ++ [x]) s' ->
    is_indexed_elements ((d0 :: drest) ++ [x]) il' s' ->
    non_adjacent_in il' ->
    sum s' = max1 ->
    index_lex_lt il1 il' \/ il1 = il'. 
Proof. 
Admitted.

Lemma max_sum_lex_inv_eq_nlex_case :
  forall (x d0 : Z) (drest ans1 il1 ans2 il2 : list Z) (max1 max2 idx : Z)
    (Hlen : Zlength (d0 :: drest) = idx)
    (Hfull1 : max_sum_full_spec (d0 :: drest) max1 ans1)
    (Hidx1 :  is_indexed_elements (d0 :: drest) il1 ans1)
    (Hgap1 : non_adjacent_in il1)
    (Hlex1 : forall s' il',
               feasible_set (d0 :: drest) s' ->
               is_indexed_elements (d0 :: drest) il' s' ->
               non_adjacent_in il' -> sum s' = max1 ->
               index_lex_lt il1 il' \/ il1 = il')
    (Hfull2 : max_sum_full_spec (removelast (d0 :: drest)) max2 ans2)
    (Hidx2 : is_indexed_elements (removelast (d0 :: drest)) il2 ans2)
    (Hgap2 : non_adjacent_in il2)
    (Hlex2 : forall s' il',
               feasible_set (removelast (d0 :: drest)) s' ->
               is_indexed_elements (removelast (d0 :: drest)) il' s' ->
               non_adjacent_in il' -> sum s' = max2 ->
               index_lex_lt il2 il' \/ il2 = il')
    (Heq : max2 + x = max1)
    (Hnlex :  ~ index_lex_lt (il2 ++ [idx]) il1),
  max_sum_lex_inv ((d0 :: drest) ++ [x]) max1 ans1 il1 max1 ans1 il1 (idx + 1).
Proof.
  intros x d0 drest ans1 il1 ans2 il2 max1 max2 idx Hlen Hfull1 Hidx1 Hgap1 Hlex1 Hfull2 Hidx2 Hgap2 Hlex2 Heq Hnlex.
  unfold max_sum_lex_inv. 
  repeat split.
  - rewrite Zlength_app. rewrite Hlen; unfold Zlength; tauto.
  - assert (Hspec1 := proj1 Hfull1).
    assert (Hspec2 := proj1 Hfull2).
    pose proof (max_value_spec_app (d0 :: drest) x max1 max2 Hspec1 Hspec2) as Hspec_app.
    assert (Hmax : Z.max max1 (max2 + x) = max2 + x).
    {
      rewrite Heq. 
      apply Z.max_idempotent.
    }
    rewrite Hmax in Hspec_app.
    rewrite Heq in Hspec_app.
    apply Hspec_app.
  - apply feasible_set_app_x_l.
    apply (proj1 (proj2 Hfull1)).
  - apply (proj2 (proj2 Hfull1)).
  - apply is_indexed_elements_prefix_extend.
    exact Hidx1.
  - apply (proj1 Hgap1).
  - apply (proj2 Hgap1).
  - intros s' il' Hfeas Hidx' Hnonadj Hsum.
    apply (index_lex_preserve_eq_nlex_case d0 x drest ans1 il1 ans2 il2 max1 max2 idx s' il'
             Hlen Hfull1 Hidx1 Hgap1 Hlex1 Hfull2 Hidx2 Hgap2 Hlex2 Heq Hnlex
             Hfeas Hidx' Hnonadj Hsum).
  - rewrite removelast_app_x.  apply (proj1 Hfull1).
  - rewrite removelast_app_x.  apply (proj1 (proj2 Hfull1)).
  - apply (proj2 (proj2 Hfull1)).
  - rewrite removelast_app_x. exact Hidx1.
  - apply (proj1 Hgap1).
  - apply (proj2 Hgap1).
  - rewrite removelast_app_x. exact Hlex1.
Qed.

(** Level 4: Prove that the modified algorithm returns the lexicographically minimal optimal solution *)
Theorem max_sum_lex_correct :
  forall l,
    Hoare (max_sum_lex l)
      (fun '(m, s, il) => lex_min_spec l m s il).
Proof.
  intros l.
  unfold max_sum_lex.
  eapply Hoare_bind.
  - eapply Hoare_list_iter with
      (I := fun done st =>
        match st with
        | (max1, ans1, il1, max2, ans2, il2, idx) =>
            max_sum_lex_inv done max1 ans1 il1 max2 ans2 il2 idx
        end).
    + repeat split.
      * apply max_value_spec_nil.
      * apply feasible_set_nil_intro.
      * apply is_indexed_elements_nil.
      * tauto.
      * intros. right. apply proof_il'_nil with s'; tauto.
    + intros x done st.
      destruct st as [[[[[[max1 ans1] il1] max2] ans2] il2] idx].
      intros [Hlen [Hfull1 [Hidx1 [Hgap1 [Hlex1 Hrem]]]]].

      destruct done as [|d0 drest].
      * destruct Hrem as [-> [-> ->]].
        apply Hoare_choice.
        -- eapply Hoare_assume_bind.
           intros Hgt.
           apply Hoare_ret.

           assert (Hfeas1 : feasible_set [] ans1) by (apply (proj1 (proj2 Hfull1))).
           apply feasible_set_nil in Hfeas1. subst ans1.
           simpl in Hgt.  (* now Hgt : x > max1 *)
           assert (Hsum1 : sum [] = max1) by (apply (proj2 (proj2 Hfull1))); simpl in Hsum1.
           subst max1.  (* now max1 = 0 *)
           apply is_indexed_elements_nil_inv_r in Hidx1. subst il1.
           assert (Hidx0 : idx = 0). { apply idx_eq_zero. apply Hlen. }
           subst idx. simpl. rewrite Hidx0.
           apply max_sum_lex_inv_single_positive; tauto.
        -- apply Hoare_choice.
           ++ eapply Hoare_assume_bind.
              intros Hlt; simpl in Hlt.
              apply Hoare_ret. simpl.
              apply max_sum_lex_inv_single_case; tauto.
           ++ eapply Hoare_assume_bind.
              intros Heq; simpl in Heq.
              apply Hoare_choice.
              ** apply Hoare_assume_bind.
                 intros Hlt.
                 apply Hoare_ret; simpl.
                 (* 此时 Hlt 内存在矛盾 *)
                 apply max_sum_lex_inv_contradiction_case; tauto.
              ** apply Hoare_assume_bind.
                 intros Hnlt.
                 apply Hoare_ret; simpl.
                 apply max_sum_lex_inv_valid_case; tauto.
      * destruct Hrem as [Hfull2 [Hidx2 [Hgap2 Hlex2]]].
        apply Hoare_choice.
        -- eapply Hoare_assume_bind.
           intros Hgt.
           apply Hoare_ret.
           apply max_sum_lex_inv_extend_case; tauto.
        -- apply Hoare_choice.
           ++ eapply Hoare_assume_bind.
              intros Hlt.
              apply Hoare_ret.
              rewrite <- Hlen.
              apply max_sum_lex_inv_preserve_when_not_taken
              with (l := (d0 :: drest))
                   (x := x)
                   (max1 := max1)
                   (max2 := max2)
                   (ans1 := ans1)
                   (ans2 := ans2)
                   (il1 := il1). discriminate. tauto. tauto. tauto. tauto. tauto. tauto.
           ++ eapply Hoare_assume_bind.
              intros Heq.
              apply Hoare_choice.
              ** eapply Hoare_assume_bind.
                 intros Hlex.
                 apply Hoare_ret.
                 apply max_sum_lex_inv_eq_case; tauto.
              ** eapply Hoare_assume_bind.
                 intros Hnlex.
                 apply Hoare_ret.
                 apply max_sum_lex_inv_eq_nlex_case
                 with 
                   (x := x)
                   (max1 := max1)
                   (max2 := max2)
                   (ans1 := ans1)
                   (ans2 := ans2)
                   (il1 := il1)
                   (il2 := il2); tauto.
  - intros a Hinv.
    destruct a as [[[[[[max1 ans1] il1] max2] ans2] il2] idx].
    destruct Hinv as [Hlen [Hfull [Hidx [Hgap [Hlex _]]]]].
    unfold lex_min_spec.
    apply Hoare_ret.
    tauto.
Qed.
