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

include "ground/arith/nat_le_pred.ma".
include "ground/relocation/gr_basic.ma".
include "ground/relocation/gr_after_uni.ma".

(* RELATIONAL COMPOSITION FOR GENERIC RELOCATION MAPS ***********************)

(* Constructions with gr_basic **********************************************)

(*** after_basic_rc *)
lemma after_basic_rc (d2) (d1):
      d1 ≤ d2 → ∀h2,h1.d2 ≤ h1+d1 → 𝐛❨d2,h2❩ ⊚ 𝐛❨d1,h1❩ ≘ 𝐛❨d1,h1+h2❩.
#d2 #d1 @(nat_ind_2_succ … d2 d1) -d2 -d1
[ #d1 #H #h2 #h1 #_
  <(nle_inv_zero_dx … H) -d1 //
| #d2 #IH #_ #h2 #h1 <nplus_zero_dx #H
  elim (nle_inv_succ_sn … H) -H #Hd2 #Hh1
  >Hh1 -Hh1 <nplus_succ_sn
  /3 width=7 by gr_after_push/
| #d2 #d1 #IH #H1 #h2 #h1 <nplus_succ_dx #H2
  lapply (nle_inv_succ_bi … H1) -H1 #H1
  lapply (nle_inv_succ_bi … H2) -H2 #H2
  /3 width=7 by gr_after_refl/
]
qed.
