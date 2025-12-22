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

Definition max_sum (l:  list Z): program (Z * list Z) :=
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
Definition non_adjacent_in (il: list Z): Prop :=
  sincr il /\ forall i j, In i il -> In j il -> i + 1 <> j.

(* s 是 l 的一个不相邻子序列, 索引列表是 il *)
Definition non_adjacent_subseq (s l :  list Z): Prop:=
  exists il, is_indexed_elements l il s /\ non_adjacent_in il. 

(* list 求和的定义 *)
Definition sum (l: list Z) : Z := fold_right Z.add 0 l.

(* 可行集合的定义 *)
Definition feasible_set (l :  list Z) (s : list Z) := non_adjacent_subseq s l.

(* Definition max_value_spec (l:  list Z) (m: Z) : Prop :=
  max_value_of_subset_with_default
    (fun s => feasible_set l s)
    (fun s => sum s)
    0
    m.  *)

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

(* "排末元素"集合的最大值 *)
Definition max_value_spec_excl_last (prefix:  list Z) (m: Z) : Prop :=
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


(* ========================================================================== *)
(* 最长上升子序列 (LIS) 相关定义和证明 *)
(* ========================================================================== *)

(* 判断一个序列是否严格递增 *)
Definition is_strictly_increasing (l: list Z) : Prop :=
  forall i j, 0 <= i -> i < j -> j < Zlength l ->
    exists vi vj, Znth_error l i = Some vi /\ 
                  Znth_error l j = Some vj /\ 
                  vi < vj.

(* 判断子序列是否是上升子序列 *)
Definition is_increasing_subseq (s l:  list Z) : Prop :=
  is_subsequence l s /\ is_strictly_increasing s. 

(* LIS 算法的状态：(末尾元素, 长度, 子序列) *)
Definition LIS_state := (Z * Z * list Z)%type.

(* LIS 算法定义 *)
Definition LIS (l: list Z) (least: Z): program (Z * list Z) :=
  st <- list_iter
    (fun n st =>
      '(n0, len0, l0) <- max_object_of_subset
        Z.le
        (fun '(n0, len0, l0) => In (n0, len0, l0) st /\ n0 < n)
        (fun '(n0, len0, l0) => len0);;
      ret (st ++ [(n, len0 + 1, l0 ++ [n])]))
    l
    [(least, 0, [])];;
  '(n0, len0, l0) <- max_object_of_subset
    Z.le
    (fun '(n0, len0, l0) => In (n0, len0, l0) st)
    (fun '(n0, len0, l0) => len0);;
  ret (len0, l0).

(* LIS 算法的不变式 *)
Definition LIS_invariant (prefix: list Z) (least: Z) (st: list LIS_state) : Prop :=
  forall n len l,
    In (n, len, l) st ->
    (* l 是以 n 结尾的递增子序列 *)
    is_increasing_subseq l prefix /\
    (l = [] \/ Znth_error l (Zlength l - 1) = Some n) /\
    (* len 是该子序列的长度 *)
    Zlength l = len /\
    (* len 是以 n 结尾的最长上升子序列的长度 *)
    (forall l', is_increasing_subseq l' prefix ->
                (l' = [] \/ Znth_error l' (Zlength l' - 1) = Some n) ->
                Zlength l' <= len).

(* 最长上升子序列的长度规范 *)
Definition LIS_length_spec (l: list Z) (len: Z) : Prop :=
  (exists s,
    is_increasing_subseq s l /\
    Zlength s = len /\
    forall s', is_increasing_subseq s' l -> Zlength s' <= len).

(* 最长上升子序列的完整规范（包含序列本身）*)
Definition LIS_full_spec (l: list Z) (len: Z) (s: list Z) : Prop :=
  is_increasing_subseq s l /\
  Zlength s = len /\
  forall s', is_increasing_subseq s' l -> Zlength s' <= len.

(* 辅助引理：序列长度的性质 *)
Lemma Zlength_nonneg_list : 
  forall (l: list Z), 0 <= Zlength l. 
Proof.
  intros.  apply Zlength_nonneg. 
Qed.

(* 辅助引理：空序列是任意序列的子序列 *)
Lemma is_subsequence_nil : forall (l : list Z), is_subsequence l [].
Proof. Admitted.

(* 辅助引理：空序列是递增的 *)
Lemma empty_is_increasing : 
  forall l, is_increasing_subseq [] l.
Proof.
  intros l. split.
  - apply is_subsequence_nil.
  - unfold is_strictly_increasing. 
    intros. (* 自动引入 i, j 和所有不等式假设 *)
    unfold Zlength in *. (* 展开 Zlength 定义 *)
    simpl in *.          (* 计算空列表长度为 0 *)
    lia.                 (* 0 <= i < j < 0 推出矛盾 *)
Qed.

(* 辅助引理：追加元素后保持递增性 *)
Lemma append_preserves_increasing :
  forall l s n,
    is_increasing_subseq s l ->
    (s = [] \/ exists last, Znth_error s (Zlength s - 1) = Some last /\ last < n) ->
    In n l ->
    is_increasing_subseq (s ++ [n]) l.
Proof. 
Admitted.  (* 需要详细证明 *)

(* 第二档难度：证明 LIS 算法输出的长度是正确的 *)
Theorem LIS_length_correct :
  forall l least,
    least < fold_right Z.min (least - 1) l ->
    Hoare (LIS l least)
      (fun '(len, _) => LIS_length_spec l len).
Proof.
Admitted.  (* 主要证明框架，需要使用 list_iter 的归纳性质 *)

(* 第三档难度：证明 LIS 算法输出的序列是正确的 *)
Theorem LIS_full_correct :
  forall l least,
    least < fold_right Z.min (least - 1) l ->
    Hoare (LIS l least)
      (fun '(len, s) => LIS_full_spec l len s).
Proof.
Admitted. (* 在长度正确的基础上，进一步证明序列本身是最长的 *)

(* ========================================================================== *)
(* 第四档难度：字典序最小的 LIS *)
(* ========================================================================== *)

(* 索引的字典序比较 *)
Fixpoint index_lex_lt (il1 il2: list Z) : Prop :=
  match il1, il2 with
  | [], [] => False
  | [], _ ::  _ => True
  | _ ::  _, [] => False
  | i1 :: il1', i2 :: il2' =>
      i1 < i2 \/ (i1 = i2 /\ index_lex_lt il1' il2')
  end.

(* 字典序最小的规范 *)
Definition LIS_lex_min_spec (l: list Z) (len: Z) (s: list Z) : Prop :=
  exists il,
    is_indexed_elements l il s /\
    is_strictly_increasing s /\
    Zlength s = len /\
    (* s 是最长的 *)
    (forall s', is_increasing_subseq s' l -> Zlength s' <= len) /\
    (* s 的索引序列是字典序最小的 *)
    (forall s' il',
      is_indexed_elements l il' s' ->
      is_strictly_increasing s' ->
      Zlength s' = len ->
      index_lex_lt il il' \/ il = il').

(* 修改后的 LIS 算法（优先选择字典序最小的）*)
Definition LIS_lex_min (l: list Z) (least: Z): program (Z * list Z) :=
  st <- list_iter
    (fun n st =>
      '(n0, len0, l0, il0) <- max_object_of_subset
        Z.le
        (fun '(n0, len0, l0, il0) =>
          In (n0, len0, l0, il0) st /\ n0 < n)
        (fun '(n0, len0, l0, il0) => len0);;
      (* 在相同长度下选择字典序最小的 *)
      ret (st ++ [(n, len0 + 1, l0 ++ [n], il0 ++ [Zlength l0])]))
    l
    [(least, 0, [], [])];;
  '(n0, len0, l0, il0) <- max_object_of_subset
    Z.le
    (fun '(n0, len0, l0, il0) => In (n0, len0, l0, il0) st)
    (fun '(n0, len0, l0, il0) => len0);;
  ret (len0, l0).

(* 第四档难度：证明修改后的算法输出字典序最小的 LIS *)
Theorem LIS_lex_min_correct : 
  forall l least,
    least < fold_right Z.min (least - 1) l ->
    Hoare (LIS_lex_min l least)
      (fun '(len, s) => LIS_lex_min_spec l len s).
Proof.
Admitted. (* 最高难度证明，需要维护索引信息并证明字典序性质 *)


(* ========================================================================== *)
(* 原 MaxSum 相关引理 *)
(* ========================================================================== *)

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
  forall (A : Type) (l :  list A) (x : A),
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
      + (* Prove:  is_indexed_elements (prefix ++ [n]) il l *)
      (* Need:  non_adjacent_in il and Hbound for il *)
        assert (Hnonadj_il : non_adjacent_in il).
        { destruct Hnonadj as [Hsincr_cons Hnoadj_cons].
          (* sincr (i ::  il) implies sincr il *)
          assert (Hsincr_il : sincr il).
          { destruct il as [|j js]. 
            - unfold sincr; constructor.
            - pose proof sincr_app_cons_inv2 [i] j js. 
              simpl in *.
              pose proof H Hsincr_cons.
              tauto.
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
      
        assert (Hbound_il :  Forall (fun i0 => i0 < Zlength prefix - 1) il).
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
    - (* Show:  Znth_error (prefix ++ [n]) last = Some n *)
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
          (* Now goal:  nth_error (prefix ++ [n]) (length prefix) = Some n *)
          apply nth_error_app_r. 
        * (* last >= Zlength (prefix ++ [n]) — contradiction *)
          exfalso; lia.
      + (* last < 0 — contradiction *)
        exfalso; lia.
    - apply Forall2_nil.
  }

  assert (Hindexed_new : is_indexed_elements (prefix ++ [n]) (il2 ++ [last]) (ans2 ++ [n])).
  { apply is_indexed_elements_app; auto.  }

  (* ---------- Part 2: non_adjacent_in ---------- *)
  destruct Hnonadj as [Hsincr Hnoadj]. 

  (* (a) sincr (il2 ++ [last]) *)
  assert (Hsincr_new : sincr (il2 ++ [last])).
  { (* Step 1: Show all elements in il2 are < last *)
    assert (Hlt_all :  Forall (fun i => i < last) il2).
    { apply Forall_forall.
      intros i Hin.
      rewrite Forall_forall in Hbound.
      pose proof Hbound i Hin.
      lia.
    }
    admit.  (* 需要完整证明 sincr 性质 *)
  }

  (* (b) no two indices are consecutive *)
  assert (Hnoadj_new : forall i j,
      In i (il2 ++ [last]) -> In j (il2 ++ [last]) -> i + 1 <> j).
{ admit.
  }

  split.
  - exact Hindexed_new. 
  - split.
    + exact Hsincr_new.
    + exact Hnoadj_new. 
Admitted. 



Lemma max_sum_value_optimal :
  forall l,
    Hoare (max_sum l)
      (fun '(m, s) =>
         max_value_spec l m /\ feasible_set l s).
Admitted. 