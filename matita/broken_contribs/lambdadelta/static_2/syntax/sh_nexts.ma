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

lemma sh_nexts_zero (h):
      ∀s. s = ⇡*[h,𝟎]s.
// qed.

lemma sh_nexts_unit (h):
      ∀s. ⇡[h]s = ⇡*[h,𝟏]s.
// qed.

lemma sh_nexts_succ (h) (n):
      ∀s. ⇡[h](⇡*[h,n]s) = ⇡*[h,↑n]s.
#h #n #s @(niter_succ … (⇡[h]))
qed.

(* Advanced constructions ****************************)

lemma sh_nexts_swap (h) (n):
      ∀s. ⇡[h](⇡*[h,n]s) = ⇡*[h,n](⇡[h]s).
#h #n #s @(niter_appl … (⇡[h]))
qed.

(* Helper constructions *****************************************************)

lemma sh_nexts_succ_next (h) (n):
      ∀s. ⇡*[h,n](⇡[h]s) = ⇡*[h,↑n]s.
// qed.
