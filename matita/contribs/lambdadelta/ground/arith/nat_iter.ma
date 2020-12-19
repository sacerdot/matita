(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "ground/arith/pnat_iter.ma".
include "ground/arith/nat.ma".

(* NON-NEGATIVE INTEGERS ****************************************************)

definition niter (n:nat) (A:Type[0]) (f:A→A) (a:A) ≝
match n with
[ nzero  ⇒ a
| ninj p ⇒ f^{A}p a
]
.

interpretation
  "iterated function (non-negative integers)"
  'Exp A f n = (niter n A f).

(* Basic rewrites ***********************************************************)

lemma niter_zero (A) (f) (a): a = (f^{A}𝟎) a.
// qed.

lemma niter_inj (A) (f) (p) (a): f^p a = f^{A}(ninj p) a.
// qed.

(* Advanced rewrites ********************************************************)

lemma niter_appl (A) (f) (n) (a): f (f^n a) = f^{A}n (f a).
#A #f * //
#p #a <niter_inj <niter_inj <piter_appl //
qed.
