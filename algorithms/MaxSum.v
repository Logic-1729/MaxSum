Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
Require Import MonadLib.MonadLib.
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

(** Definition of non-adjacent indices:  indices are strictly increasing and no two indices are adjacent *)
Definition non_adjacent_in (il: list Z): Prop :=
  sincr il /\ forall i j, In i il -> In j il -> i + 1 <> j. 

(** s is a non-adjacent subsequence of l with index list il *)
Definition non_adjacent_subseq (s l :  list Z): Prop :=
  exists il, is_indexed_elements l il s /\ non_adjacent_in il. 

(** Definition of sum of a list *)
Definition sum (l: list Z) : Z := fold_right Z.add 0 l.

(** Definition of the feasible set:  s is feasible if it is a non-adjacent subsequence of l *)
Definition feasible_set (l :  list Z) (s : list Z) := non_adjacent_subseq s l.

(** Specification for the maximum value:  m is the maximum sum among all feasible subsequences *)
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

Lemma sum_app:  forall l1 l2, sum (l1 ++ l2) = sum l1 + sum l2.
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
  - intros t H.  apply feasible_set_nil in H.  subst.  simpl.  lia.
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
        -- unfold Zlength.  rewrite Nat2Z.id. reflexivity.
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
  - 
    simpl in H.
    unfold is_indexed_elements in *.
    destruct il. 
    + inversion H; subst.  apply Forall2_nil.
    + inversion H; subst. 
      unfold Znth_error in H2.
      destruct (Z_le_gt_dec 0 z).
      * destruct (Z.to_nat z); simpl in H2; discriminate. 
      * discriminate. 
  - 
    unfold is_indexed_elements in *.
    eapply Forall2_congr; [| eauto]. 
    intros i a0 Hin_i Hin_s Hnth.
    assert (Hneq: z ::  l <> []) by congruence.
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
  forall (l :  list Z) (x : Z) (s il :  list Z),
    is_indexed_elements l il s ->
    is_indexed_elements (l ++ [x]) il s.
Proof.
  intros l x s il H. 
  unfold is_indexed_elements in *.
  induction H as [| i a il' s' Hnth Hrest IH]; simpl. 
  - apply Forall2_nil. 
  - apply Forall2_cons. 
    + assert (Hrange: 0 <= i < Zlength l).
      { apply Znth_error_range in Hnth.  tauto. }
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
    simpl.   auto.
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

Lemma last_in_list:   forall {A} (l:   list A) (d: A),
  l <> [] -> In (last l d) l.
Proof.
  intros A l d Hneq.
  induction l as [| a l' IH]. 
  - contradiction. 
  - destruct l' as [| b l'']. 
    + simpl.   left.  reflexivity.
    + simpl.  right. apply IH.  discriminate.
Qed.  

Lemma feasible_set_app_x_r:   forall l x s,
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
        { apply last_in_list.   discriminate. }
        specialize (Hidx _ Hin_last).
        destruct (list_snoc_destruct l) as [Heq_l | [a [l0 Heq_l]]]. 
        -- 
           subst l.   simpl in Hidx.   unfold Zlength in *. simpl in *. lia.
        -- 
           subst l.  
           rewrite removelast_app in Hidx by discriminate.
           simpl in Hidx.  rewrite app_nil_r in Hidx.  
           rewrite Zlength_app.   unfold Zlength in *. simpl in *.  lia.
  
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
      * subst l.   simpl in Hidx.  unfold Zlength in *.  simpl in *. lia.   
      * subst l.  
        rewrite removelast_app in Hidx by discriminate.   
        simpl in Hidx.    rewrite app_nil_r in Hidx. 
        rewrite Zlength_app.  unfold Zlength in *.  simpl in *. 
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
        simpl in Hidx.  rewrite app_nil_r in Hidx.  
        rewrite Zlength_app. unfold Zlength in *. simpl in *. 
        lia.  
    + 
      simpl in Hi_last, Hj_last.
      destruct Hi_last as [Heq_i | Hf]; [| contradiction]. 
      destruct Hj_last as [Heq_j | Hf]; [| contradiction].
      subst i j.
      lia.  
Qed.  

Lemma feasible_set_app_x_inv_empty_il:  forall l x s,
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

Lemma feasible_set_app_x_inv_l_empty:    forall (x:    Z) il' s1,
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
              simpl in Hin.   destruct Hin as [Heq | Hin'].  
              + subst.   exact Hya.  
              + assert (Ha_lt_j:    a < j) by (apply IH; auto). lia.
          }
          apply (Haux (il''' ++ [0]) i1 Hrest 0).
          apply in_app_iff.     right.   simpl. left.   reflexivity. 
        }
        lia.  
    + discriminate Hnth0.
Qed.  

Lemma feasible_set_app_x_inv_idx_bound: forall (l0 :    list Z) (a0 x :  Z) il' i,
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
  assert (Hi_lt:   i < Zlength (l0 ++ [a0])).
  { apply sincr_app_singleton_inv with (l1 := il'); auto. }
  apply is_indexed_elements_range in Hidx.
  rewrite Forall_forall in Hidx.
  specialize (Hidx i Hin_i) as [Hi_ge _]. 
  assert (Hneq: i + 1 <> Zlength (l0 ++ [a0])).
  {
    apply Hgap.
    - apply in_app_iff.  left. exact Hin_i.
    - apply in_app_iff.  right. simpl. left.   reflexivity.  
  }
  unfold Zlength in *.
  rewrite length_app in Hi_lt, Hneq.  
  simpl in Hi_lt, Hneq.  
  lia. 
Qed.  

Lemma sincr_app_cons_inv1:   forall l1 x,
  sincr (l1 ++ [x]) ->
  sincr l1.
Proof.
  intros l1 x Hsincr.
  destruct l1 as [| a l1'].  
  - simpl.   auto.
  - simpl in Hsincr |- *. 
    revert a Hsincr. 
    induction l1' as [| b l1'' IH]; intros a Hsincr.  
    + simpl in *. auto. 
    + simpl in Hsincr |- *.
      destruct Hsincr as [Hab Hrest].
      split; [exact Hab |].
      apply IH.   exact Hrest.
Qed. 

Lemma feasible_set_app_x_inv_i_last_eq:   forall l x s il' i_last,
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
      simpl.   rewrite app_nil_r.  
      assert (Hidx1_saved:   is_indexed_elements ((l0 ++ [a0]) ++ [x]) il' s1) by exact Hidx1.
      eapply Forall2_congr; [| exact Hidx1].    
      intros i a Hin_i Hin_s Hnth.  
      assert (Hlt:   i < Zlength l0).
      {
        eapply feasible_set_app_x_inv_idx_bound with (a0 := a0) (x := x) (il' := il').
        - 
          assert (Heq_i_last: i_last = Zlength (l0 ++ [a0])).
          { rewrite <- Heq_idx.   reflexivity.   }
          rewrite <- Heq_i_last. 
          exact Hsincr.
        - 
          intros i' j' Hi' Hj'.  
          assert (Heq_i_last:    i_last = Zlength (l0 ++ [a0])).
          { rewrite <- Heq_idx.  reflexivity. }
          rewrite <- Heq_i_last in Hi', Hj'.
          apply Hgap; auto.  
        - exact Hin_i.  
        - exists s1. exact Hidx1_saved.  
        - exists a.    exact Hnth.  
      }
      symmetry. 
      assert (Hnth_range:   0 <= i < Zlength ((l0 ++ [a0]) ++ [x])).
      { apply Znth_error_range in Hnth.   exact Hnth. }
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
    + apply in_app_iff.    left.  exact Hi.  
    + apply in_app_iff.  left.  exact Hj. 
Qed.  

Lemma feasible_set_app_x_inv_i_last_neq:  forall l x s il' i_last,
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
  { apply Znth_error_range in Hnth_last.  exact Hnth_last.  }
  assert (Hi_last_lt: i_last < Zlength l).
  {
    destruct Hi_last_range as [_ Hi_ub]. 
    rewrite Zlength_app in Hi_ub. 
    unfold Zlength in Hi_ub at 2.
    simpl in Hi_ub. 
    lia. 
  }
  assert (Hnth_last_l:  Znth_error l i_last = Some a).
  {
    assert (Hnth_last_copy: Znth_error (l ++ [x]) i_last = Some a) by exact Hnth_last.  
    rewrite Znth_error_app_l in Hnth_last_copy.  
    - exact Hnth_last_copy. 
    - split.  
      + apply Znth_error_range in Hnth_last.   lia.
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

Lemma feasible_set_app_x_inv:   forall l x s,
  feasible_set (l ++ [x]) s ->
  feasible_set l s \/
  (exists s', s = s' ++ [x] /\ feasible_set (removelast l) s').
Proof.
  intros l x s H. 
  unfold feasible_set, non_adjacent_subseq in H.
  destruct H as [il [Hidx [Hsincr Hgap]]].   
  destruct (list_snoc_destruct il) as [Heq_il | [i_last [il' Heq_il]]]; subst il.
  - left.  
    apply (feasible_set_app_x_inv_empty_il l x s); auto.
  - destruct (Z.eq_dec i_last (Zlength l)) as [Heq_idx | Hneq_idx].  
    * right.
      apply (feasible_set_app_x_inv_i_last_eq l x s il' i_last Heq_idx Hsincr Hgap Hidx).
    * left.  
      apply (feasible_set_app_x_inv_i_last_neq l x s il' i_last Hneq_idx Hsincr Hgap Hidx).
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
    - destruct Hcase1 as [s [?  [?  ? ]]]. split; [exists s; auto | auto].
    - destruct Hcase2 as [Hle Heq].  split; [| subst; auto]. 
      exists [].  split. 
      + exists []. split.  apply is_indexed_elements_nil.  split; [simpl; auto | intros; contradiction].
      + subst. reflexivity.
  }
  destruct H1 as [[s1 [Hfeas1 Hsum1]] Hmax1]. 

  assert (H2: (exists s, feasible_set (removelast l) s /\ sum s = m2) /\ (forall t, feasible_set (removelast l) t -> sum t <= m2)).
  {
    destruct Hspec2 as [Hcase1 | Hcase2]. 
    - destruct Hcase1 as [s [? [?  ?]]]. split; [exists s; auto | auto].
    - destruct Hcase2 as [Hle Heq].  split; [| subst; auto].
      exists []. split. 
      + exists []. split.  apply is_indexed_elements_nil. split; [simpl; auto | intros; contradiction].
      + subst. reflexivity. 
  }
  destruct H2 as [[s2 [Hfeas2 Hsum2]] Hmax2]. 
  apply Z.max_case_strong; intros Hle. 
  - 
    left.  exists s1. split; [| split].
    + apply feasible_set_app_x_l.  assumption.
    + assumption.
    + intros t Ht.
      apply feasible_set_app_x_inv in Ht.
      destruct Ht as [Ht | [t' [Heq Ht']]].
      * 
        apply Hmax1. assumption.
      *
        subst t.  rewrite sum_app.  simpl. rewrite Z.add_0_r. 
        specialize (Hmax2 t' Ht').
        lia.
  - 
    left. exists (s2 ++ [x]). split; [| split].
    + apply feasible_set_app_x_r. assumption.
    + rewrite sum_app. simpl.  rewrite Z.add_0_r. rewrite Hsum2. reflexivity.
    + intros t Ht.
      apply feasible_set_app_x_inv in Ht.
      destruct Ht as [Ht | [t' [Heq Ht']]]. 
      * 
        specialize (Hmax1 t Ht). lia.
      * 
        subst t. rewrite sum_app. simpl.  rewrite Z.add_0_r.
        specialize (Hmax2 t' Ht').
        lia.
Qed.

Lemma removelast_app_x:  forall {A} (l:  list A) x,
  removelast (l ++ [x]) = l.
Proof.
  intros.
  rewrite removelast_app.
  - simpl.  rewrite app_nil_r. reflexivity. 
  - discriminate.
Qed. 

Lemma Hoare_list_iter {A B:  Type}:  
  forall (body:  A -> B -> program B)
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
      simpl.  split; apply max_value_spec_nil.  
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
    intros st.  destruct st as [[[m1 ans1] m2] ans2].
    intros [Hm1 _].   
    apply Hoare_ret.  
    exact Hm1.
Qed.  

(** Level 3: Prove that the algorithm returns a correct feasible subsequence achieving the maximum value *)
Lemma sum_single:  forall x, sum [x] = x.
Proof.  intros. simpl. apply Z.add_0_r.  Qed.

Lemma sincr_tail:  forall a l, sincr (a :: l) -> sincr l.
Proof. 
  intros a l Hsincr.  unfold sincr in *.
  destruct l as [|b l']. 
  - simpl.  auto.
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
    + inversion Hidx; subst.  apply Forall2_nil. 
    + destruct t as [|y t'].
      * inversion Hidx. 
      * constructor. 
        -- inversion Hidx; subst.
           assert (H_range: 0 <= i < Zlength l).
           { apply Znth_error_range in H2.  tauto. }
           rewrite (Znth_error_app_l _ _ _ H_range). apply H2.
        -- inversion Hidx; subst.  apply IH.  
           ++ apply (sincr_tail i il' Hsincr).
           ++ intros i0 j0 Hi0 Hj0. apply Hgap.
              ** right. apply Hi0.
              ** apply in_cons. apply Hj0.
           ++ apply H4.                
Qed.

Lemma last_In:  
  forall (l:  list Z) (tail: Z),
    l <> [] -> In (last l tail) l.
Proof. 
  intros l tail H.  induction l as [|a l' IH]. 
  - contradiction. 
  - destruct l' as [|a' l''].
    + simpl.  left. reflexivity.
    + simpl.  right. apply IH. discriminate.
Qed.         

Lemma feasible_set_extend: 
  forall (l: list Z) (s: Z) (t: list Z),
    feasible_set (removelast l) t -> 
    feasible_set (l ++ [s]) (t ++ [s]).
Proof.
  intros l s t Hfeas.  unfold feasible_set, non_adjacent_subseq in Hfeas.
  destruct Hfeas as [il [Hidx [Hsincr Hgap]]]. 
  exists (il ++ [Zlength l]). repeat split.  
  - apply is_indexed_elements_app.
    + apply is_indexed_elements_extend.  apply Hidx.
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
        -- subst l; simpl in *; unfold Zlength in *; simpl in *.  lia.
        -- subst l.  rewrite removelast_app in Hidx by discriminate. 
           simpl in Hidx. rewrite app_nil_r in Hidx.
           rewrite Zlength_app.  unfold Zlength in *.  simpl.  lia.
  - intros x y Hx Hy. apply in_app_or in Hx. apply in_app_or in Hy.
    destruct Hx as [Hx_il | Hx_lt]; destruct Hy as [Hy_il | Hy_lt].
    + apply Hgap; tauto.
    + simpl in *. destruct Hy_lt as [Heq_y | Hf]; [|contradiction]. 
      subst y. apply is_indexed_elements_range in Hidx. 
      rewrite Forall_forall in Hidx.  specialize (Hidx _ Hx_il).
      destruct (list_snoc_destruct l) as [Heq_l | [a [l' Heq_l]]].
      * subst l.  simpl in Hidx. unfold Zlength in *. simpl.  lia.
      * subst l. rewrite removelast_app in Hidx by discriminate. 
        simpl in Hidx. rewrite app_nil_r in Hidx.
        rewrite Zlength_app. unfold Zlength in *. simpl. lia. 
    + simpl in *. destruct Hx_lt as [Heq_x | Hf]; [|contradiction].  
      subst x. apply is_indexed_elements_range in Hidx.  
      rewrite Forall_forall in Hidx.  specialize (Hidx _ Hy_il). 
      destruct (list_snoc_destruct l) as [Heq_l | [a [l' Heq_l]]].  
      * subst l.  simpl.  unfold Zlength in *.  simpl in *. lia.
      * subst l. rewrite removelast_app in Hidx by discriminate.
        simpl in Hidx. rewrite app_nil_r in Hidx.  
        rewrite Zlength_app. unfold Zlength in *. simpl. lia.
    + simpl in *. destruct Hx_lt as [Heq_x | Hf]; [|contradiction].
      destruct Hy_lt as [Heq_y | Hf]; [|contradiction]. subst x y.  lia.    
Qed.

Theorem max_sum_full_correct :
  forall l,
    Hoare (max_sum l)
      (fun '(m, s) => max_sum_full_spec l m s).
Proof.
  intros l.  unfold max_sum.  eapply Hoare_bind. 
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
    + intros x done st.  destruct st as [[[m1 ans1] m2] ans2].
      intros [Hm1 [Hm2 [Hfeas1 [Hsum1 [Hfeas2 Hsum2]]]]].  apply Hoare_choice.
      * eapply Hoare_assume_bind. intros H_le. apply Hoare_ret.  repeat split.  
        -- assert (Hmax: max_value_spec (done ++ [x]) (Z.max m1 (m2 + x))).
           { apply max_value_spec_app; auto. }
           replace (Z.max m1 (m2 + x)) with (m2 + x) in Hmax.
           ++ apply Hmax. 
           ++ symmetry. apply Z.max_r. lia.
        -- rewrite removelast_app_x.  apply Hm1.
        -- apply feasible_set_extend.  tauto.
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
        -- apply feasible_set_preserved.  assumption.
        -- assumption. 
        -- rewrite removelast_app_x. apply Hfeas1.
        -- apply Hsum1.
  - intros st. destruct st as [[[m1 ans1] m2] ans2]. 
    intros [Hm1 [Hm2 [Hfeas1 [Hsum1 [_ _]]]]]. apply Hoare_ret.
    unfold max_sum_full_spec. repeat split; auto. 
Qed.

(** ========================================================================
    Level 4: Lexicographically minimal solution
    ======================================================================== *)

Definition nat_list_to_Z_list (l: list nat) : list Z := map Z.of_nat l.

(** Lexicographical comparison of index lists *)
Fixpoint index_lex_lt (il1 il2: list nat) : Prop :=
  match il1, il2 with
  | [], [] => False           
  | [], _ ::  _ => True      
  | _ :: _, [] => False
  | i1 :: il1', i2 :: il2' =>
      (i1 < i2)%nat \/ (i1 = i2 /\ index_lex_lt il1' il2')
  end.

Definition non_adjacent_in_nat (il:  list nat): Prop :=
  let il_Z := nat_list_to_Z_list il in
  non_adjacent_in il_Z.

Definition is_indexed_elements_nat (l: list Z) (il: list nat) (s: list Z) : Prop :=
  is_indexed_elements l (nat_list_to_Z_list il) s.

Definition lex_min_spec (l: list Z) (m: Z) (s: list Z) (il: list nat) : Prop :=
  max_sum_full_spec l m s /\
  is_indexed_elements_nat l il s /\
  non_adjacent_in_nat il /\
  (forall s' (il':  list nat), 
     feasible_set l s' -> 
     is_indexed_elements_nat l il' s' -> 
     non_adjacent_in_nat il' ->
     sum s' = m -> 
     index_lex_lt il il' \/ il = il').

(** Modified algorithm to find the lexicographically minimal solution *)
Definition max_sum_lex (l: list Z): program (Z * list Z * list nat) :=
  '(max1, ans1, il1, _, _, _, _) <- 
    list_iter
      (fun n =>
         fun '(max1, ans1, il1, max2, ans2, il2, idx) =>
           let sum_include := max2 + n in
           choice
             (assume (sum_include > max1);; 
              ret (sum_include, ans2 ++ [n], il2 ++ [idx], max1, ans1, il1, (idx + 1)%nat))
             (choice
                (assume (sum_include < max1);;
                 ret (max1, ans1, il1, max1, ans1, il1, (idx + 1)%nat))
                (assume (sum_include = max1);;
                  choice 
                    (assume (index_lex_lt (il2 ++ [idx]) il1);;
                     ret (sum_include, ans2 ++ [n], il2 ++ [idx], max1, ans1, il1, (idx + 1)%nat))
                    (assume (~ index_lex_lt (il2 ++ [idx]) il1);;
                     ret (max1, ans1, il1, max1, ans1, il1, (idx + 1)%nat))
                )
             )
      )
      l
      (0, [], [], 0, [], [], 0%nat);; 
  ret (max1, ans1, il1).

Lemma Zlength_removelast_lt:  forall {A} (l: list A),
  l <> [] ->
  Zlength (removelast l) < Zlength l.
Proof.
  intros A l Hneq. 
  destruct l using rev_ind.
  - contradiction. 
  - rewrite removelast_app_x. 
    rewrite Zlength_app. 
    assert (Zlength [x] = 1).
    { unfold Zlength. simpl. auto. }
    lia. 
Qed.

Lemma sincr_app_singleton: forall (il: list Z) (x: Z),
  sincr il ->
  (forall i, In i il -> i < x) ->
  sincr (il ++ [x]).
Proof.
  intros il x Hsincr Hbound.
  induction il as [| a il' IH].
  - simpl. auto.
  - simpl.  destruct il' as [| b il''].
    + simpl.  simpl in Hsincr. split; auto.
      apply Hbound.  left. reflexivity.
    + simpl in Hsincr. destruct Hsincr as [Hab Hrest].
      simpl. split; [assumption |].
      apply IH; [assumption |]. 
      intros i Hi. apply Hbound. right. assumption.
Qed.

Lemma index_lex_lt_or_eq: forall il1 il2,
  index_lex_lt il1 il2 \/ il1 = il2 \/ index_lex_lt il2 il1.
Proof. 
  intros il1.
  induction il1 as [| a1 il1' IH]; intros il2.
  - destruct il2 as [| a2 il2'].
    + right. left. reflexivity.
    + left. simpl. auto.
  - destruct il2 as [| a2 il2'].
    + right. right. simpl. auto.
    + simpl. 
      destruct (Nat.lt_trichotomy a1 a2) as [Hlt | [Heq | Hgt]].
      * left. left. exact Hlt.
      * subst a2.
        specialize (IH il2').
        destruct IH as [IH_lt | [IH_eq | IH_gt]].
        -- left. right. split; [reflexivity | exact IH_lt]. 
        -- right. left. rewrite IH_eq. reflexivity.
        -- right. right. right. split; [reflexivity | exact IH_gt].
      * right. right. left. exact Hgt. 
Qed.

Theorem max_sum_lex_correct:
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
              | (m1, ans1, il1, m2, ans2, il2, idx) =>
                  Zlength done = Z.of_nat idx /\
                  lex_min_spec done m1 ans1 il1 /\
                  lex_min_spec (removelast done) m2 ans2 il2
              end).
+
      simpl.
      split.
      { 
        reflexivity. 
      }
      split.
      { 
        unfold lex_min_spec.
        split.
        { 
          unfold max_sum_full_spec.
          repeat split.
          - apply max_value_spec_nil.
          - apply feasible_set_nil_intro.
        }
        split.
        { 
          unfold is_indexed_elements_nat, nat_list_to_Z_list. simpl. 
          apply is_indexed_elements_nil. 
        }
        split.
        { 
          unfold non_adjacent_in_nat, nat_list_to_Z_list. simpl. 
          split; simpl; auto. 
        }
        { 
          intros s' il' Hfeas _ _ Hsum.
          apply feasible_set_nil in Hfeas. subst s'.
          destruct il' as [|n il'].
          - right. reflexivity.
          - left. simpl. auto.
        }
      }
      {
        simpl.
        unfold lex_min_spec.
        split.
        { 
          unfold max_sum_full_spec.
          repeat split.
          - apply max_value_spec_nil.
          - apply feasible_set_nil_intro.
        }
        split.
        { 
          unfold is_indexed_elements_nat, nat_list_to_Z_list. simpl. 
          apply is_indexed_elements_nil. 
        }
        split.
        { 
          unfold non_adjacent_in_nat, nat_list_to_Z_list. simpl. 
          split; simpl; auto. 
        }
        { 
          intros s' il' Hfeas _ _ Hsum.
          apply feasible_set_nil in Hfeas. subst s'.
          destruct il' as [|n il'].
          - right. reflexivity.
          - left. simpl. auto.
        }
      }
    + 
      intros n done st.
      destruct st as [[[[[[m1 ans1] il1] m2] ans2] il2] idx].
      intros [Hlen [Hspec1 Hspec2]].
      assert (Hidx_Z: Z.of_nat idx = Zlength done). { lia. }
      assert (Hidx_next: Z.of_nat (idx + 1) = Zlength (done ++ [n])).
      { 
        rewrite Nat2Z.inj_add. simpl. 
        rewrite Hidx_Z. 
        rewrite Zlength_app. 
        unfold Zlength. simpl. 
        lia. 
      }
      
      apply Hoare_choice.
      * (* Case: sum_include > max1 *)
        eapply Hoare_assume_bind.  intros Hgt.
        apply Hoare_ret. 
        split; [| split]. 
        -- rewrite <- Hidx_next.  reflexivity.
        -- unfold lex_min_spec. repeat split.
           ++ 
              replace (m2 + n) with (Z.max m1 (m2 + n)) by lia.
              apply max_value_spec_app.
              ** apply (proj1 Hspec1). 
              ** apply (proj1 Hspec2).
           ++ 
              apply feasible_set_extend.
              apply (proj1 (proj2 (proj1 Hspec2))).
           ++ (* Sum equality: sum (ans2 ++ [n]) = m2 + n *)
              simpl. 
              rewrite sum_app. 
              rewrite sum_single.
              rewrite (proj2 (proj2 (proj1 Hspec2))). 
              reflexivity.
           ++ 
              unfold is_indexed_elements_nat, nat_list_to_Z_list.
              rewrite map_app. simpl.
              apply is_indexed_elements_app.
              {
                apply is_indexed_elements_extend.
                apply (proj1 (proj2 Hspec2)).
              }
              {
                apply is_indexed_elements_cons.
                - 
                  rewrite Hidx_Z. 
                  apply Znth_error_snoc_last.
                - apply is_indexed_elements_nil.
              }
           ++ (* Non-adjacency: non_adjacent_in_nat (il2 ++ [idx]) *)
              unfold non_adjacent_in_nat, nat_list_to_Z_list.
              rewrite map_app. simpl.
              unfold non_adjacent_in.
              { 
                apply sincr_extend_last.
                - apply (proj1 (proj2 (proj2 Hspec2))).
                - destruct (map Z.of_nat il2) eqn:Hil2_map.
                  left. reflexivity.  
                  right.
                  destruct Hspec2 as [_ [Hidx_il2 _]].
                  unfold is_indexed_elements_nat, nat_list_to_Z_list in Hidx_il2.
                  rewrite Hil2_map in Hidx_il2.
                  apply is_indexed_elements_range in Hidx_il2.
                  rewrite Forall_forall in Hidx_il2.
                  assert (Hin: In (last (z :: l0) 0) (z :: l0)).
                  { apply last_in_list. discriminate. }
                  specialize (Hidx_il2 _ Hin).
                  destruct Hidx_il2 as [_ Hlt]. 
                  rewrite Hidx_Z.
                  assert (Hlen_le: Zlength (removelast done) <= Zlength done).
                  {
                    unfold Zlength.
                    apply Nat2Z.inj_le. 
                    destruct (list_snoc_destruct done) as [Heq | [x [l' Heq]]].
                    - 
                      subst done. simpl. lia.
                    - 
                      subst done.
                      rewrite removelast_app by discriminate.
                      simpl. rewrite app_nil_r. 
                      rewrite length_app.         
                      simpl.                     
                      lia.   
                  }
                  lia.
              }
           ++
              { 
                intros i j Hi Hj.
                unfold nat_list_to_Z_list in *.
                rewrite map_app in Hi, Hj.
                apply in_app_or in Hi; apply in_app_or in Hj.
                
                destruct Hi as [Hi|Hi], Hj as [Hj|Hj].
                - 
                  apply (proj2 (proj1 (proj2 (proj2 Hspec2)))); auto.
                  
                - 
                  destruct Hj as [Hj|F]; [subst j | contradiction].
                  destruct Hspec2 as [_ [Hidx_il2 _]].
                  apply is_indexed_elements_range in Hidx_il2.
                  rewrite Forall_forall in Hidx_il2.
                  specialize (Hidx_il2 _ Hi).
                  rewrite Hidx_Z.
                  assert (Hlen_bound: Zlength (removelast done) <= Zlength done - 1).
                  {
                    unfold Zlength.
                    destruct (list_snoc_destruct done) as [Heq | [x [l' Heq]]].
                    - subst done. 
                      unfold Zlength in Hidx_il2. simpl in Hidx_il2.
                      lia.
                    - subst done.
                      rewrite removelast_app by discriminate.
                      rewrite !length_app. simpl.
                      rewrite Nat2Z.inj_add. simpl.
                      lia.
                  }
                  lia.
                - 
                  destruct Hi as [Hi|F]; [subst i | contradiction].
                  destruct Hspec2 as [_ [Hidx_il2 _]].
                  apply is_indexed_elements_range in Hidx_il2.
                  rewrite Forall_forall in Hidx_il2.
                  specialize (Hidx_il2 _ Hj).
                  
                  rewrite Hidx_Z.
                  assert (Hlen_bound: Zlength (removelast done) < Zlength done).
                  {
                     unfold Zlength.
                     destruct done.
                     - 
                       simpl. 
                       unfold Zlength in Hidx_il2. simpl in Hidx_il2.
                       lia. 
                     - 
                       simpl. 
                       assert (Hrem: forall (h: Z) (t: list Z), length (removelast (h :: t)) = length t).
                       {
                         intros h t.
                         generalize dependent h.
                         induction t as [|x xs IH]; intros h0.
                         - simpl. reflexivity.
                         - simpl.
                           f_equal.
                           apply (IH x).
                       }
                       change (match done with | [] => [] | _ :: _ => z :: removelast done end) with (removelast (z :: done)).
                       rewrite Hrem.
                       lia.
                  }
                  lia.
                - 
                  destruct Hi as [Hi|F]; [subst i | contradiction].
                  destruct Hj as [Hj|F]; [subst j | contradiction].
                  lia.
              }
           ++ 
              intros s' il' Hfeas' Hidx' Hnonadj' Hsum'.
              destruct (feasible_set_app_x_inv done n s' Hfeas') as [Hfeas_skip | [s_prev [Heq_s Hfeas_incl]]].
              { 
                 assert (sum s' <= m1). 
                 { 
                  destruct Hspec1 as [[Hmax_prop _] _].
                   unfold max_value_spec in Hmax_prop.
                   destruct Hmax_prop as [H_has_opt | H_no_opt].
                 - 
                   destruct H_has_opt as [_ [_ [_ H_upper_bound]]].
                   apply H_upper_bound.
                   exact Hfeas_skip.
                 - 
                   destruct H_no_opt as [H_all_neg H_m1_zero].
                   rewrite H_m1_zero.
                   apply H_all_neg.
                   exact Hfeas_skip.
                 }
                 lia.
              }
               { 
                 subst s'.
                 assert (exists il_prev, il' = il_prev ++ [idx] /\ is_indexed_elements_nat (removelast done) il_prev s_prev) as [il_prev [Heq_il Hidx_prev]].
                 { 
                   admit. 
                 }
                 subst il'.
                 rewrite sum_app in Hsum'. simpl in Hsum'.
                 assert (Hsum_prev: sum s_prev = m2). { lia. }
                 assert (Hnonadj_prev:  non_adjacent_in_nat il_prev). 
                 {
                 unfold non_adjacent_in_nat, non_adjacent_in.  
                 unfold non_adjacent_in_nat, non_adjacent_in in Hnonadj'.
                 destruct Hnonadj' as [Hsincr' Hgap']. 
                 split. 
                 - 
                 unfold nat_list_to_Z_list in *. 
                 rewrite map_app in Hsincr'. 
                 simpl in Hsincr'. 
                 apply sincr_app_cons_inv1 with (x := Z.of_nat idx).
                 exact Hsincr'. 
                 - 
                 intros u v Hu Hv. 
                 unfold nat_list_to_Z_list in *.
                 apply Hgap'. 
                 + rewrite map_app. apply in_or_app.  left. exact Hu.
                 + rewrite map_app. apply in_or_app. left.  exact Hv.
                }
                 destruct Hspec2 as [_ [_ [_ Hlex2]]].
                 specialize (Hlex2 s_prev il_prev Hfeas_incl Hidx_prev Hnonadj_prev Hsum_prev).
                 destruct Hlex2 as [Hlt | Heq].
                 - 
                   left. 
                   admit.
                 - 
                   right. 
                   rewrite Heq. 
                   reflexivity.
              }
        -- 
           rewrite removelast_app_x. 
           apply Hspec1.
        
      * (* Case: sum_include <= max1 *)
        apply Hoare_choice.
        -- (* Case: sum_include < max1 *)
           eapply Hoare_assume_bind.  intros Hlt.
           apply Hoare_ret. 
           split; [| split]. 
           ++ rewrite <- Hidx_next.  reflexivity.
           ++ unfold lex_min_spec.  repeat split.
              ** assert (Hm1_done: max_value_spec done m1) by apply Hspec1.
                 assert (Hm2_rmlast:  max_value_spec (removelast done) m2) by apply Hspec2.
                 assert (Hmax: max_value_spec (done ++ [n]) (Z.max m1 (m2 + n))).
                 { apply max_value_spec_app; assumption. }
                 replace (Z.max m1 (m2 + n)) with m1 in Hmax.
                 --- exact Hmax. 
                 --- symmetry. apply Z.max_l. lia.
              ** apply feasible_set_app_x_l. apply Hspec1.
              ** apply Hspec1.
              ** unfold is_indexed_elements_nat. 
                 apply is_indexed_elements_prefix_extend.  apply Hspec1.
              ** apply Hspec1.
              ** apply Hspec1.
              ** intros s' il' Hfeas' Hidx' Hnonadj' Hsum'.
                 assert (Hno_n: feasible_set done s').
                 {
                   apply feasible_set_app_x_inv in Hfeas'.
                   destruct Hfeas' as [Hfeas_done | [s_prev [Heq Hfeas_prev]]].
                   - exact Hfeas_done. 
                   - exfalso. 
                     subst s'. 
                     rewrite sum_app in Hsum'.  simpl in Hsum'. 
                     rewrite Z.add_0_r in Hsum'. 
                     assert (Hsum_prev: sum s_prev <= m2).
                     {
                       destruct Hspec2 as [Hspec2_full _].
                       destruct Hspec2_full as [Hmax2 _].
                       destruct Hmax2 as [[s_opt [_ [_ Hmax_bound]]] | [Hle_zero Heq_zero]].
                       - apply Hmax_bound.  exact Hfeas_prev.
                       - rewrite Heq_zero. apply Hle_zero.  exact Hfeas_prev.
                     }
                     lia.
                 }
                 assert (Hidx_done: is_indexed_elements_nat done il' s').
                 {
                   unfold is_indexed_elements_nat in *.
                   unfold nat_list_to_Z_list in *.
                   eapply Forall2_congr; [| exact Hidx'].
                   intros i a Hin_i Hin_s Hnth. 
                   assert (Hi_range: 0 <= i < Zlength done).
                   {
                     split.
                     - apply Znth_error_range in Hnth.  tauto.
                     - (* TODO:  Prove indices are bounded *)
                       admit.
                   }
                   simpl in Hnth. 
                   rewrite Znth_error_app_l in Hnth; [| exact Hi_range].
                   exact Hnth.
                 }
                 assert (Hlex_min:  forall s' il',
                           feasible_set done s' ->
                           is_indexed_elements_nat done il' s' ->
                           non_adjacent_in_nat il' ->
                           sum s' = m1 ->
                           index_lex_lt il1 il' \/ il1 = il').
                 { apply Hspec1. }
                 specialize (Hlex_min s' il' Hno_n Hidx_done Hnonadj' Hsum').
                 exact Hlex_min.
           ++ rewrite removelast_app_x. exact Hspec1.
           
        -- (* Case: sum_include = max1 *)
           eapply Hoare_assume_bind. intros Heq.
           apply Hoare_choice.
           ++ (* Case: il2 ++ [idx] is lex smaller than il1 *)
              eapply Hoare_assume_bind. intros Hlex.
              apply Hoare_ret.
              split; [| split].
              ** symmetry. exact Hidx_next.
              ** unfold lex_min_spec.  repeat split.
                 --- (* max_value_spec *)
                     assert (Hmax: max_value_spec (done ++ [n]) (Z.max m1 (m2 + n))).
                     { apply max_value_spec_app; [apply Hspec1 | apply Hspec2]. }
                     rewrite Heq in Hmax.
                     rewrite Z.max_id in Hmax.
                     rewrite <- Heq in Hmax.
                     exact Hmax.
                 --- (* feasible_set *)
                     apply feasible_set_app_x_r. apply Hspec2.
                 --- (* sum *)
                     rewrite sum_app. simpl.  rewrite Z.add_0_r.
                     assert (Hsum2: sum ans2 = m2) by apply Hspec2.
                     lia.
                 --- (* is_indexed_elements_nat *)
                     unfold is_indexed_elements_nat, nat_list_to_Z_list.
                     rewrite map_app.  simpl.
                     apply is_indexed_elements_app. 
                     *** apply is_indexed_elements_extend.  apply Hspec2.
                     *** apply is_indexed_elements_cons; [| apply is_indexed_elements_nil]. 
                         rewrite Hidx_Z. apply Znth_error_snoc_last. 
                 --- (* non_adjacent_in_nat *)
                     unfold non_adjacent_in_nat, nat_list_to_Z_list, non_adjacent_in.  
                     rewrite map_app.  simpl (map Z.of_nat [idx]).
                     *** (* sincr (map Z.of_nat il2 ++ [Z.of_nat idx]) *)
                         apply sincr_app_singleton.  
                         ---- (* sincr (map Z.of_nat il2) *)
                              apply Hspec2.
                         ---- (* All elements of map Z.of_nat il2 are < Z.of_nat idx *)
                              intros i Hi. 
                              assert (Hrange:  Forall (fun z => 0 <= z /\ z < Zlength (removelast done)) (map Z.of_nat il2)).
                              {
                                assert (Hidx2: is_indexed_elements_nat (removelast done) il2 ans2) by apply Hspec2.
                                unfold is_indexed_elements_nat, nat_list_to_Z_list in Hidx2.
                                apply is_indexed_elements_range in Hidx2.
                                exact Hidx2.
                              }
                              rewrite Forall_forall in Hrange.
                              specialize (Hrange i Hi).
                              rewrite Hidx_Z. 
                              destruct done using rev_ind.
                              ++++ simpl in Hidx_Z.  unfold Zlength in Hidx_Z.  simpl in Hidx_Z.
                                   assert (idx = 0)%nat by lia.  subst idx.
                                   simpl in Hrange.  unfold Zlength in Hrange. simpl in Hrange.  lia.
                              ++++ assert (Hlen_rm:   Zlength (removelast (done ++ [x])) < Zlength (done ++ [x])).
                                   { apply Zlength_removelast_lt.   
                                     intro Hcontra.  
                                     destruct done; simpl in Hcontra; discriminate. 
                                   }
                                   rewrite removelast_app_x in Hlen_rm.  
                                   rewrite removelast_app_x in Hrange.
                                   lia.
                 ---
                     *** (* gap property:  no i, j with i + 1 = j *)
                         intros i j Hi Hj Hij.
                         unfold nat_list_to_Z_list in Hi, Hj.
                         rewrite map_app in Hi, Hj.
                         simpl in Hi, Hj. 
                         apply in_app_or in Hi. apply in_app_or in Hj. 
                         destruct Hi as [Hi_il2 | Hi_idx]; destruct Hj as [Hj_il2 | Hj_idx].
                         ---- (* Both in il2 *)
                              assert (Hgap2:  forall i0 j0, 
                                        In i0 (map Z.of_nat il2) -> 
                                        In j0 (map Z.of_nat il2) -> 
                                        i0 + 1 <> j0).
                              {
                                destruct Hspec2 as [_ [_ [Hnonadj2 _]]].
                                unfold non_adjacent_in_nat, nat_list_to_Z_list, non_adjacent_in in Hnonadj2.
                                destruct Hnonadj2 as [_ Hgap2']. 
                                exact Hgap2'.
                              }
                              apply (Hgap2 i j Hi_il2 Hj_il2 Hij).
                         ---- (* i in il2, j = idx *)
                              simpl in Hj_idx.  destruct Hj_idx as [Hj_eq | Hj_false]; [| contradiction].
                              subst j.  
                              assert (Hi_bound: i < Zlength (removelast done)).
                              {
                                assert (Hidx2: is_indexed_elements_nat (removelast done) il2 ans2) by apply Hspec2.
                                unfold is_indexed_elements_nat, nat_list_to_Z_list in Hidx2.
                                apply is_indexed_elements_range in Hidx2.
                                rewrite Forall_forall in Hidx2.
                                apply (proj2 (Hidx2 i Hi_il2)).
                              }
                              rewrite Hidx_Z in Hij.
                              destruct done using rev_ind.  
                              ++++ simpl in Hidx_Z.  unfold Zlength in Hidx_Z.   simpl in Hidx_Z.  
                                   assert (idx = 0)%nat by lia.   subst idx. 
                                   simpl in Hi_bound.  unfold Zlength in Hi_bound. simpl in Hi_bound. 
                                   assert (Hi_nonneg: 0 <= i).
                                   {
                                     clear -Hi_il2.
                                     rewrite in_map_iff in Hi_il2.
                                     destruct Hi_il2 as [n_val [Heq_i _]]. 
                                     subst i.
                                     apply Nat2Z.is_nonneg. 
                                   }
                                   lia.
                              ++++ assert (Hlen_rm:    Zlength (removelast (done ++ [x])) < Zlength (done ++ [x])).
                                   { apply Zlength_removelast_lt.   intro Hc.  destruct done; discriminate. }
                                   rewrite removelast_app_x in Hlen_rm, Hi_bound.
                                   lia.
                         ---- (* i = idx, j in il2 - impossible since i < j from sincr *)
                              simpl in Hi_idx. destruct Hi_idx as [Hi_eq | Hi_false]; [| contradiction].
                              subst i.  exfalso. 
                              assert (Hj_bound: j < Zlength (removelast done)).
                              {
                                assert (Hidx2: is_indexed_elements_nat (removelast done) il2 ans2) by apply Hspec2.
                                unfold is_indexed_elements_nat, nat_list_to_Z_list in Hidx2.
                                apply is_indexed_elements_range in Hidx2.
                                rewrite Forall_forall in Hidx2.
                                apply (proj2 (Hidx2 j Hj_il2)).
                              }
                              rewrite Hidx_Z in Hij.
                              destruct done using rev_ind.
                              ++++ simpl in Hidx_Z.   unfold Zlength in Hidx_Z. simpl in Hidx_Z.  
                                   assert (idx = 0)%nat by lia.  subst idx.
                                   simpl in Hij, Hj_bound.  unfold Zlength in Hj_bound. simpl in Hj_bound.
                                   assert (0 <= j).
                                   { clear -Hj_il2.
                                     apply in_map_iff in Hj_il2 as [n_val [Heq_j _]].  
                                     rewrite <- Heq_j.  lia. }
                                   lia.
                              ++++ assert (Hlen_rm:    Zlength (removelast (done ++ [x])) < Zlength (done ++ [x])).
                                   { apply Zlength_removelast_lt. intro Hc.  destruct done; discriminate.   }
                                   rewrite removelast_app_x in Hlen_rm, Hj_bound.
                                   lia.
                         ---- (* Both are idx - impossible *)
                              simpl in Hi_idx, Hj_idx. 
                              destruct Hi_idx as [Hi_eq | Hi_false]; [| contradiction].
                              destruct Hj_idx as [Hj_eq | Hj_false]; [| contradiction]. 
                              subst i j.  lia.
                 --- (* Lex minimality *)
                     intros s' il'' Hfeas' Hidx'' Hnonadj' Hsum'.
                     (* TODO: Complete lex minimality proof *)
                     admit. 
              ** rewrite removelast_app_x. exact Hspec1.
              
           ++ (* Case: ~ lex_lt (il2 ++ [idx]) il1 *)
              eapply Hoare_assume_bind.  intros Hnlex.
              apply Hoare_ret.
              split; [| split].
              ** symmetry.  exact Hidx_next. 
              ** unfold lex_min_spec. repeat split.
                 --- (* max_value_spec *)
                     assert (Hmax: max_value_spec (done ++ [n]) (Z.max m1 (m2 + n))).
                     { apply max_value_spec_app; [apply Hspec1 | apply Hspec2].  }
                     rewrite Heq in Hmax.
                     rewrite Z.max_id in Hmax.
                     exact Hmax.
                 --- apply feasible_set_app_x_l. apply Hspec1.
                 --- apply Hspec1.
                 --- unfold is_indexed_elements_nat. 
                     apply is_indexed_elements_prefix_extend. apply Hspec1.
                 --- apply Hspec1.
                 --- apply Hspec1.
                 --- (* Lex minimality *)
                     intros s' il'' Hfeas' Hidx'' Hnonadj' Hsum'.
                     (* TODO: Complete lex minimality proof *)
                     admit.
              ** rewrite removelast_app_x. exact Hspec1.
              
  - (* Final step: extract result *)
    intros st.
    destruct st as [[[[[[m1 ans1] il1] m2] ans2] il2] idx].
    intros [_ [Hspec1 _]].
    apply Hoare_ret.
    exact Hspec1.
Admitted. (* Main theorem admitted due to TODO items in lex minimality *)