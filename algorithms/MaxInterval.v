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

(* assume leftmost is less than any interval
   assume the left endpoint of l is increasing *)

Definition max_interval (l: list (Z * Z)) (leftmost: Z):
  program (Z * list (Z * Z)) :=
  '(leftmost0, size0, ans0) <- list_iter
                                 (fun '(l, r) =>
                                   fun '(leftmost0, size0, ans0) =>
                                     choice
                                       (assume (l <= leftmost0);;
                                        ret (leftmost0, size0, ans0))
                                       (assume (l > leftmost0);;
                                        ret (r, size0 + 1, ans0 ++ [(l, r)])))
                                l
                                (leftmost, 0, []);;
  ret (size0, ans0).
