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

include "ground/arith/nat_iter.ma".
include "ground/arith/nat_succ.ma".

(* NON-NEGATIVE INTEGERS ****************************************************)

(* Rewrites with niter ******************************************************)

lemma niter_succ (A) (f) (n) (a): f (f^n a) = f^{A}(↑n) a.
#A #f * //
qed.
