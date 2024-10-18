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

include "ground/arith/nat_le.ma".
include "ground/arith/nat_rplus_succ.ma".
include "explicit_updating/syntax/term_nexts.ma".
include "explicit_updating/syntax/substitution_pushs.ma".

(* ITERATED PUSH FOR SUBSTITUTION *******************************************)

(* Constructions with subst_nexts *******************************************)

lemma subst_pushs_dapp_le (m) (n):
      m ≤ n → ∀S. ↑*[m](ξ𝟏) = (⫯*[⁤↑n]S)＠⧣❨↑m❩.
#m #n #H0 elim H0 -n
[ #S @(nat_ind_succ … m) -m //
  #m #IH <subst_pushs_succ <subst_push_succ <IH -S //
| #n #_ #IH #S <subst_pushs_succ_swap <IH -S //
]
qed-.

lemma subst_pushs_dapp_gt (S) (p) (n):
      ↑*[n](S＠⧣❨p❩) = (⫯*[n]S)＠⧣❨p+n❩.
#S #p #n @(nat_ind_succ … n) -n //
#n #IH <nrplus_succ_dx <subst_pushs_succ <subst_push_succ <IH -IH //
qed.
