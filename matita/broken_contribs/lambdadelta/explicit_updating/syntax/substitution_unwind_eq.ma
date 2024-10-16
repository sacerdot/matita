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

include "ground/relocation/fb/fbr_dapp_eq.ma".
include "ground/relocation/fb/fbr_after_dapp.ma".
include "explicit_updating/syntax/substitution_eq.ma".
include "explicit_updating/syntax/substitution_after.ma".
include "explicit_updating/syntax/substitution_unwind.ma".

(* SUBSTITUTION FOR UNWIND **************************************************)

(* Constructions with extensional equivalence for substitution **************)

lemma subst_unwind_eq_repl:
      compatible_2_fwd … fbr_eq subst_eq subst_unwind.
#f1 #f2 #Hf #p
<subst_unwind_dapp <subst_unwind_dapp >fbr_dapp_eq_repl
/2 width=3 by term_eq_lref/
qed.

lemma subst_unwind_after (g) (f):
      (𝐬❨g•f❩) ≐ 𝐬❨g❩•f.
#g #f #p
<subst_unwind_dapp <fbr_dapp_after
<subst_after_dapp <subst_unwind_dapp
//
qed.
