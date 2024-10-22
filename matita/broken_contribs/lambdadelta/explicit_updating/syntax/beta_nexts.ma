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

include "explicit_updating/syntax/substitution_pushs_nexts.ma".
include "explicit_updating/syntax/beta.ma".

(* β-SUBSTITUTION FOR TERM **************************************************)

(* Constructions with subst_nexts *******************************************)

lemma beta_lref_le (m) (n) (v):
      m ≤ n → ↑*[m](𝛏𝟏) = ⬕[⁤↑n←v]𝛏↑m.
/2 width=1 by subst_pushs_dapp_le/
qed-.

lemma beta_lref_succ (n) (v):
      ↑*[n]v = ⬕[n←v]𝛏↑n.
#n #v
<beta_unfold <subst_tapp_lref //
qed.

lemma beta_lref_gt_succ (p) (n) (v):
      ↑*[n]𝛏p = ⬕[n←v]𝛏(↑p+n).
#p #n #v
<beta_unfold <subst_tapp_lref
<subst_pushs_dapp_gt //
qed.
