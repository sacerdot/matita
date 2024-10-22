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
include "explicit_updating/syntax/substitution_eq.ma".
include "explicit_updating/syntax/substitution_after.ma".

(* COMPOSITION WITH RELOCATION FOR SUBSTITUTION *****************************)

(* Constructions with subst_eq **********************************************)

lemma subst_after_eq_repl:
      compatible_3 … subst_eq fbr_eq subst_eq subst_after.
#S1 #S2 #HS #f1 #f2 #Hf #p
<subst_after_dapp <subst_after_dapp
/3 width=1 by subst_dapp_eq_repl, fbr_dapp_eq_repl/
qed.
