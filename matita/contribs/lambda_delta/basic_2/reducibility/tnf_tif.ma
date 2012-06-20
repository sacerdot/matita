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

include "basic_2/substitution/tps_lift.ma".
include "basic_2/reducibility/tif.ma".
include "basic_2/reducibility/tnf.ma".

(* CONTEXT-FREE NORMAL TERMS ************************************************)

(* Main properties properties ***********************************************)

lemma tpr_tif_eq: ∀T1,T2. T1 ➡ T2 →  𝐈⦃T1⦄ → T1 = T2.
#T1 #T2 #H elim H -T1 -T2
[ //
| * #V1 #V2 #T1 #T2 #_ #_ #IHV1 #IHT1 #H
  [ elim (tif_inv_appl … H) -H #HV1 #HT1 #_
    >IHV1 -IHV1 // -HV1 >IHT1 -IHT1 //
  | elim (tif_inv_cast … H)
  ]
| #V1 #V2 #W #T1 #T2 #_ #_ #_ #_ #H
  elim (tif_inv_appl … H) -H #_ #_ #H
  elim (simple_inv_bind … H)
| * #V1 #V2 #T1 #T #T2 #_ #_ #HT2 #IHV1 #IHT1 #H
  [ -HT2 -IHV1 -IHT1 elim (tif_inv_abbr … H)
  | <(tps_inv_refl_SO2 … HT2 ?) -HT2 //
    elim (tif_inv_abst … H) -H #HV1 #HT1
    >IHV1 -IHV1 // -HV1 >IHT1 -IHT1 //
  ]
| #V #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #_ #H
  elim (tif_inv_appl … H) -H #_ #_ #H
  elim (simple_inv_bind … H)
| #V1 #T1 #T #T2 #_ #_ #_ #H
  elim (tif_inv_abbr … H)
| #V1 #T1 #T2 #_ #_ #H
  elim (tif_inv_cast … H)
]
qed.

theorem tif_tnf: ∀T1.  𝐈⦃T1⦄ → 𝐍⦃T1⦄.
/3 width=1/ qed.

(* Note: this property is unusual *)
lemma tnf_trf_false: ∀T1. 𝐑⦃T1⦄ → 𝐍⦃T1⦄ → ⊥.
#T1 #H elim H -T1
[ #V #T #_ #IHV #H elim (tnf_inv_abst … H) -H /2 width=1/
| #V #T #_ #IHT #H elim (tnf_inv_abst … H) -H /2 width=1/
| #V #T #_ #IHV #H elim (tnf_inv_appl … H) -H /2 width=1/
| #V #T #_ #IHV #H elim (tnf_inv_appl … H) -H /2 width=1/
| #V #T #H elim (tnf_inv_abbr … H)
| #V #T #H elim (tnf_inv_cast … H)
| #V #W #T #H elim (tnf_inv_appl … H) -H #_ #_ #H
  elim (simple_inv_bind … H)
]
qed.

theorem tnf_tif: ∀T1. 𝐍⦃T1⦄ → 𝐈⦃T1⦄.
/2 width=3/ qed.

lemma tnf_abst: ∀V,T. 𝐍⦃V⦄ → 𝐍⦃T⦄ → 𝐍⦃ⓛV.T⦄.
/4 width=1/ qed.

lemma tnf_appl: ∀V,T. 𝐍⦃V⦄ → 𝐍⦃T⦄ → 𝐒⦃T⦄ → 𝐍⦃ⓐV.T⦄.
/4 width=1/ qed.
