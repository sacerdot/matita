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

include "explicit_updating/syntax/substitution_pushs.ma".
include "explicit_updating/syntax/substitution_valid_push.ma".

(* VALIDITY FOR SUBSTITUTION *************************************************)

(* Constructions with subst_pushs ********************************************)

lemma subst_valid_pushs (b) (n) (S):
      b ⊢ S → b ⊢ ⫯*[n]S.
#b #n @(nat_ind_succ … n) -n //
#n #IH #S #HS
/3 width=1 by subst_valid_push/
qed.

(* Inversions with subst_pushs ***********************************************)

lemma subst_valid_inv_pushs (b) (n) (S):
      b ⊢ ⫯*[n]S → b ⊢ S.
#b #n @(nat_ind_succ … n) -n //
#n #IH #S #HS
/3 width=1 by subst_valid_inv_push/
qed-.
