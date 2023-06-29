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

(* SUCCESSOR FOR NON-NEGATIVE INTEGERS **************************************)

(* Constructions with niter *************************************************)

(*** iter_S *)
lemma niter_succ (A) (f) (n:ℕ): f ∘ f^n ⊜ f^{A}(⁤↑n).
#A #f * //
qed.
