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

include "ground/arith/nat_succ_iter.ma".
include "static_2/notation/functions/uparrowstar_2_0.ma".
include "static_2/syntax/sh.ma".

(* SORT HIERARCHY ***********************************************************)

definition sh_nexts (h) (n): nat → nat ≝ ⇡[h]^n.

interpretation
  "iterated next sort (sort hierarchy)"
  'UpArrowStar_2_0 h n = (sh_nexts h n).

(* Basic constructions *)

lemma sh_nexts_zero (h): ∀s. s = ⇡*[h,𝟎]s.
// qed.

lemma sh_nexts_unit (h): ⇡[h] ≐ ⇡*[h,𝟏].
// qed.

lemma sh_nexts_succ (h) (n): ⇡[h] ∘ (⇡*[h,n]) ≐ ⇡*[h,↑n].
/2 width=1 by niter_succ/ qed.

(* Advanced constructions ****************************)

lemma sh_nexts_swap (h) (n): ⇡[h] ∘ (⇡*[h,n]) ≐ ⇡*[h,n] ∘ ⇡[h].
/2 width=1 by niter_appl/ qed.

(* Helper constructions *****************************************************)

lemma sh_nexts_succ_next (h) (n): ⇡*[h,n] ∘ (⇡[h]) ≐ ⇡*[h,↑n].
// qed.
