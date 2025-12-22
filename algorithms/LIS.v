Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
From MonadLib.SetMonad Require Import SetBasic SetHoare FixpointLib.
From MaxMinLib Require Import MaxMin Interface.
Require Import Algorithms.MapLib.

Import ListNotations.
Import MonadNotation.
Local Open Scope monad.
Local Open Scope Z.

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
