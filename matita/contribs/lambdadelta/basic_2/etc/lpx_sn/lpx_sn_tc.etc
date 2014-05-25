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

include "basic_2/relocation/lpx_sn.ma".

(* SN POINTWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS *********)

(* Properties on transitive_closure *****************************************)

lemma TC_lpx_sn_pair_refl: ∀R. (∀I,L. reflexive … (R I L)) →
                           ∀L1,L2. TC … (lpx_sn R) L1 L2 →
                           ∀I,V. TC … (lpx_sn R) (L1.ⓑ{I}V) (L2. ⓑ{I}V).
#R #HR #L1 #L2 #H @(TC_star_ind … L2 H) -L2
[ /2 width=1 by lpx_sn_refl/
| /3 width=1 by TC_reflexive, lpx_sn_refl/
| /3 width=5 by lpx_sn_pair, step/
]
qed-.

lemma TC_lpx_sn_pair: ∀R. (∀I,L. reflexive … (R I L)) →
                      ∀I,L1,L2. TC … (lpx_sn R) L1 L2 →
                      ∀V1,V2. LTC … (R I) L1 V1 V2 →
                      TC … (lpx_sn R) (L1.ⓑ{I}V1) (L2. ⓑ{I}V2).
#R #HR #I #L1 #L2 #HL12 #V1 #V2 #H @(TC_star_ind_dx … V1 H) -V1 //
[ /2 width=1 by TC_lpx_sn_pair_refl/
| /4 width=3 by TC_strap, lpx_sn_pair, lpx_sn_refl/
]
qed-.

lemma lpx_sn_LTC_TC_lpx_sn: ∀R. (∀I,L. reflexive … (R I L)) →
                            ∀L1,L2. lpx_sn (λI.LTC … (R I)) L1 L2 →
                            TC … (lpx_sn R) L1 L2.
#R #HR #L1 #L2 #H elim H -L1 -L2
/2 width=1 by TC_lpx_sn_pair, lpx_sn_atom, inj/
qed-.

(* Inversion lemmas on transitive closure ***********************************)

lemma TC_lpx_sn_inv_atom2: ∀R,L1. TC … (lpx_sn R) L1 (⋆) → L1 = ⋆.
#R #L1 #H @(TC_ind_dx … L1 H) -L1
[ /2 width=2 by lpx_sn_inv_atom2/
| #L1 #L #HL1 #_ #IHL2 destruct /2 width=2 by lpx_sn_inv_atom2/
]
qed-.

lemma TC_lpx_sn_inv_pair2: ∀R. (∀I.s_rs_transitive … (R I) (λ_.lpx_sn R)) →
                           ∀I,L1,K2,V2. TC  … (lpx_sn R) L1 (K2.ⓑ{I}V2) →
                           ∃∃K1,V1. TC … (lpx_sn R) K1 K2 & LTC … (R I) K1 V1 V2 & L1 = K1.ⓑ{I}V1.
#R #HR #I #L1 #K2 #V2 #H @(TC_ind_dx … L1 H) -L1
[ #L1 #H elim (lpx_sn_inv_pair2 … H) -H /3 width=5 by inj, ex3_2_intro/
| #L1 #L #HL1 #_ * #K #V #HK2 #HV2 #H destruct
  elim (lpx_sn_inv_pair2 … HL1) -HL1 #K1 #V1 #HK1 #HV1 #H destruct
  lapply (HR … HV2 … HK1) -HR -HV2 /3 width=5 by TC_strap, ex3_2_intro/
]
qed-.

lemma TC_lpx_sn_ind: ∀R. (∀I.s_rs_transitive … (R I) (λ_.lpx_sn R)) →
                     ∀S:relation lenv.
                     S (⋆) (⋆) → (
                        ∀I,K1,K2,V1,V2.
                        TC … (lpx_sn R) K1 K2 → LTC … (R I) K1 V1 V2 →
                        S K1 K2 → S (K1.ⓑ{I}V1) (K2.ⓑ{I}V2)
                     ) →
                     ∀L2,L1. TC … (lpx_sn R) L1 L2 → S L1 L2.
#R #HR #S #IH1 #IH2 #L2 elim L2 -L2
[ #X #H >(TC_lpx_sn_inv_atom2 … H) -X //
| #L2 #I #V2 #IHL2 #X #H
  elim (TC_lpx_sn_inv_pair2 … H) // -H -HR
  #L1 #V1 #HL12 #HV12 #H destruct /3 width=1 by/
]
qed-.

lemma TC_lpx_sn_inv_atom1: ∀R,L2. TC … (lpx_sn R) (⋆) L2 → L2 = ⋆.
#R #L2 #H elim H -L2
[ /2 width=2 by lpx_sn_inv_atom1/
| #L #L2 #_ #HL2 #IHL1 destruct /2 width=2 by lpx_sn_inv_atom1/
]
qed-.

fact TC_lpx_sn_inv_pair1_aux: ∀R. (∀I.s_rs_transitive … (R I) (λ_.lpx_sn R)) →
                              ∀L1,L2. TC … (lpx_sn R) L1 L2 →
                              ∀I,K1,V1. L1 = K1.ⓑ{I}V1 →
                              ∃∃K2,V2. TC … (lpx_sn R) K1 K2 & LTC … (R I) K1 V1 V2 & L2 = K2. ⓑ{I} V2.
#R #HR #L1 #L2 #H @(TC_lpx_sn_ind … H) // -HR -L1 -L2
[ #J #K #W #H destruct
| #I #L1 #L2 #V1 #V2 #HL12 #HV12 #_ #J #K #W #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma TC_lpx_sn_inv_pair1: ∀R. (∀I.s_rs_transitive … (R I) (λ_.lpx_sn R)) →
                           ∀I,K1,L2,V1. TC … (lpx_sn R) (K1.ⓑ{I}V1) L2 →
                           ∃∃K2,V2. TC … (lpx_sn R) K1 K2 & LTC … (R I) K1 V1 V2 & L2 = K2. ⓑ{I} V2.
/2 width=3 by TC_lpx_sn_inv_pair1_aux/ qed-.

lemma TC_lpx_sn_inv_lpx_sn_LTC: ∀R. (∀I.s_rs_transitive … (R I) (λ_.lpx_sn R)) →
                                ∀L1,L2. TC … (lpx_sn R) L1 L2 →
                                lpx_sn (λI.LTC … (R I)) L1 L2.
/3 width=4 by TC_lpx_sn_ind, lpx_sn_pair/ qed-.

(* Forward lemmas on transitive closure *************************************)

lemma TC_lpx_sn_fwd_length: ∀R,L1,L2. TC … (lpx_sn R) L1 L2 → |L1| = |L2|.
#R #L1 #L2 #H elim H -L2
[ #L2 #HL12 >(lpx_sn_fwd_length … HL12) -HL12 //
| #L #L2 #_ #HL2 #IHL1
  >IHL1 -L1 >(lpx_sn_fwd_length … HL2) -HL2 //
]
qed-.
