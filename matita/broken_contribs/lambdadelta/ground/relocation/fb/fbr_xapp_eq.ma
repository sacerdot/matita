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

include "ground/relocation/fb/fbr_xapp.ma".
include "ground/relocation/fb/fbr_dapp_eq.ma".

(* EXTENDED DEPTH APPLICATION FOR FINITE RELOCATION MAPS WITH BOOLEANS ******)

(* Inversions with fbr_xxeq *************************************************)

lemma fbr_xxeq_inv_eq (f1) (f2):
      fbr_xapp f1 ⊜ fbr_xapp f2 →
      f1 ≐ f2.
/3 width=1 by fbr_dxeq_inv_eq, eq_inv_npos_bi/
qed-.

(* Constructions with fbr_xxeq **********************************************)

(* Note: this is fbr_xxeq_eq *)
lemma fbr_xapp_eq_repl (n):
      compatible_2_fwd … fbr_eq (eq …) (λf.f＠❨n❩).
* // #p #f1 #f2 #Hf
<fbr_xapp_pos <fbr_xapp_pos
<(fbr_dapp_eq_repl … Hf) -Hf //
qed.
