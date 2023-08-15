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

include "ground/relocation/fb/fbr_minus.ma".
include "ground/relocation/fb/fbr_eq.ma".

(* SUBTRACTION FOR FINITE RELOCATION MAPS WITH BOOLEANS *********************)

(* Constructions with fbr_eq ************************************************)

lemma fbr_minus_eq_repl_dx (g):
      compatible_2_fwd … fbr_eq (eq …) (λf.g-f).
#g #f1 #f2 #Hf
generalize in match g; -g
elim Hf -f1 -f2 //
[ #b #g1 #g2 #_ #IH * // #bf #f
  <fbr_bext_rcons_bi <fbr_bext_rcons_bi //
| #g2 #_ #IH * // #bf #f
  <fbr_minus_id_dx <fbr_minus_rcons_push <IH -IH
  <fbr_minus_id_dx //
| #g1 #_ #IH * // #bf #f
  <fbr_minus_id_dx <fbr_minus_rcons_push >IH -IH
  <fbr_minus_id_dx //
]
qed.
