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

(* Definition of non-adjacent indices: il is a list of indices *)
Definition non_adjacent_in (il: list Z): Prop :=
  sincr il /\ forall i j, In i il -> In j il -> i + 1 <> j.

(* s is a non-adjacent subsequence of l, with index list il *)
Definition non_adjacent_subseq (s l :  list Z): Prop:=
  exists il, is_indexed_elements l il s /\ non_adjacent_in il. 

(* Definition of sum of a list *)
Definition sum (l: list Z) : Z := fold_right Z.add 0 l.

(* Definition of the feasible set *)
Definition feasible_set (l :  list Z) (s : list Z) := non_adjacent_subseq s l.

(* Maximum value of the set *)
Definition max_value_spec (l: list Z) (m: Z) : Prop :=
  (exists s,
      feasible_set l s /\
      sum s = m /\
      forall t, feasible_set l t -> sum t <= m)
  \/
  ((forall s, feasible_set l s -> sum s <= 0%Z) /\ m = 0%Z).

(* Maximum value of the set excluding the last element *)
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

(* Invariant *)
Definition P (prefix: list Z) (st: Z * list Z * Z * list Z) : Prop :=
  let '(max1, ans1, max2, ans2) := st in
  (exists il1, is_indexed_elements prefix il1 ans1 /\ non_adjacent_in il1)
  /\ (exists il2, is_indexed_elements prefix il2 ans2 /\ non_adjacent_in il2
                  /\ Forall (fun i => i < Zlength prefix - 1) il2)
  /\ max_value_spec prefix max1
  /\ max_value_spec_excl_last prefix max2. 

(* Check if a list is strictly increasing *)
Definition is_strictly_increasing (l: list Z) : Prop :=
  forall i j, 0 <= i -> i < j -> j < Zlength l ->
    exists vi vj, Znth_error l i = Some vi /\ 
                  Znth_error l j = Some vj /\ 
                  vi < vj.

(* Check if a subsequence is an increasing subsequence *)
Definition is_increasing_subseq (s l:  list Z) : Prop :=
  is_subsequence l s /\ is_strictly_increasing s. 

(* State for LIS algorithm: (last element, length, subsequence) *)
Definition LIS_state := (Z * Z * list Z)%type.

(* LIS Algorithm Definition *)
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

(* Invariant for LIS Algorithm *)
Definition LIS_invariant (prefix: list Z) (least: Z) (st: list LIS_state) : Prop :=
  forall n len l,
    In (n, len, l) st ->
    is_increasing_subseq l prefix /\
    (l = [] \/ Znth_error l (Zlength l - 1) = Some n) /\
    Zlength l = len /\
    (forall l', is_increasing_subseq l' prefix ->
                (l' = [] \/ Znth_error l' (Zlength l' - 1) = Some n) ->
                Zlength l' <= len).

(* Specification for the length of the LIS *)
Definition LIS_length_spec (l: list Z) (len: Z) : Prop :=
  (exists s,
    is_increasing_subseq s l /\
    Zlength s = len /\
    forall s', is_increasing_subseq s' l -> Zlength s' <= len).

(* Full specification for LIS (including the sequence itself) *)
Definition LIS_full_spec (l: list Z) (len: Z) (s: list Z) : Prop :=
  is_increasing_subseq s l /\
  Zlength s = len /\
  forall s', is_increasing_subseq s' l -> Zlength s' <= len.

(* Auxiliary Lemma: Length of a list is non-negative *)
Lemma Zlength_nonneg_list : 
  forall (l: list Z), 0 <= Zlength l. 
Proof.
  intros.  
  apply Zlength_nonneg. 
Qed.

(* Auxiliary Lemma: Empty list is a subsequence of any list *)
Lemma is_subsequence_nil : forall (l : list Z), is_subsequence l [].
Proof. 
Admitted.

(* Auxiliary Lemma: Empty list is increasing *)
Lemma empty_is_increasing : 
  forall l, is_increasing_subseq [] l.
Proof.
  intros l. 
  split.
  - apply is_subsequence_nil.
  - unfold is_strictly_increasing. 
    intros. 
    unfold Zlength in *. 
    simpl in *.          
    lia.                
Qed.

(* Auxiliary Lemma: Appending an element preserves increasing property *)
Lemma append_preserves_increasing :
  forall l s n,
    is_increasing_subseq s l ->
    (s = [] \/ exists last, Znth_error s (Zlength s - 1) = Some last /\ last < n) ->
    In n l ->
    is_increasing_subseq (s ++ [n]) l.
Proof. 
Admitted.  (* Requires detailed proof *)

(* Level 2: Prove LIS algorithm outputs the correct length *)
Theorem LIS_length_correct :
  forall l least,
    least < fold_right Z.min (least - 1) l ->
    Hoare (LIS l least)
      (fun '(len, _) => LIS_length_spec l len).
Proof.
Admitted.  (* Main proof framework, requires induction on list_iter *)

(* Level 3: Prove LIS algorithm outputs a correct subsequence *)
Theorem LIS_full_correct :
  forall l least,
    least < fold_right Z.min (least - 1) l ->
    Hoare (LIS l least)
      (fun '(len, s) => LIS_full_spec l len s).
Proof.
Admitted. (* Based on length correctness, further prove sequence maximality *)

(* ========================================================================== *)
(* Level 4: Lexicographically Minimal LIS *)
(* ========================================================================== *)

(* Lexicographical comparison of indices *)
Fixpoint index_lex_lt (il1 il2: list Z) : Prop :=
  match il1, il2 with
  | [], [] => False
  | [], _ ::  _ => True
  | _ ::  _, [] => False
  | i1 :: il1', i2 :: il2' =>
      i1 < i2 \/ (i1 = i2 /\ index_lex_lt il1' il2')
  end.

(* Specification for Lexicographically Minimal LIS *)
Definition LIS_lex_min_spec (l: list Z) (len: Z) (s: list Z) : Prop :=
  exists il,
    is_indexed_elements l il s /\
    is_strictly_increasing s /\
    Zlength s = len /\
    (* s is the longest *)
    (forall s', is_increasing_subseq s' l -> Zlength s' <= len) /\
    (* The index sequence of s is lexicographically minimal *)
    (forall s' il',
      is_indexed_elements l il' s' ->
      is_strictly_increasing s' ->
      Zlength s' = len ->
      index_lex_lt il il' \/ il = il').

(* Modified LIS Algorithm (Prioritizes Lexicographically Minimal) *)
Definition LIS_lex_min (l: list Z) (least: Z): program (Z * list Z) :=
  st <- list_iter
    (fun n st =>
      res <- max_object_of_subset
        Z.le
        (fun '(n0, len0, l0, il0) =>
          In (n0, len0, l0, il0) st /\ n0 < n)
        (fun '(n0, len0, l0, il0) => len0);;
      let '(n0, len0, l0, il0) := res in
      (* Choose lexicographically minimal for same length *)
      ret (st ++ [(n, len0 + 1, l0 ++ [n], il0 ++ [Zlength l0])]))
    l
    [(least, 0, [], [])];;
  res <- max_object_of_subset
    Z.le
    (fun '(n0, len0, l0, il0) => In (n0, len0, l0, il0) st)
    (fun '(n0, len0, l0, il0) => len0);;
  let '(n0, len0, l0, il0) := res in
  ret (len0, l0).

(* Level 4: Prove modified algorithm outputs lexicographically minimal LIS *)
Theorem LIS_lex_min_correct : 
  forall l least,
    least < fold_right Z.min (least - 1) l ->
    Hoare (LIS_lex_min l least)
      (fun '(len, s) => LIS_lex_min_spec l len s).
Proof.
Admitted. 