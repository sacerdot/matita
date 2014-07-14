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

include "basic_2/substitution/drop_leq.ma".
include "basic_2/substitution/lpx_sn.ma".

(* SN POINTWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS *********)

(* Properties on dropping ****************************************************)

lemma lpx_sn_drop_conf: ∀R,L1,L2. lpx_sn R L1 L2 →
                        ∀I,K1,V1,i. ⇩[i] L1 ≡ K1.ⓑ{I}V1 →
                        ∃∃K2,V2. ⇩[i] L2 ≡ K2.ⓑ{I}V2 & lpx_sn R K1 K2 & R K1 V1 V2.
#R #L1 #L2 #H elim H -L1 -L2
[ #I0 #K0 #V0 #i #H elim (drop_inv_atom1 … H) -H #H destruct
| #I #K1 #K2 #V1 #V2 #HK12 #HV12 #IHK12 #I0 #K0 #V0 #i #H elim (drop_inv_O1_pair1 … H) * -H
  [ -IHK12 #H1 #H2 destruct /3 width=5 by drop_pair, ex3_2_intro/
  | -HK12 -HV12 #Hi #HK10 elim (IHK12 … HK10) -IHK12 -HK10
    /3 width=5 by drop_drop_lt, ex3_2_intro/
  ]
]
qed-.

lemma lpx_sn_drop_trans: ∀R,L1,L2. lpx_sn R L1 L2 →
                         ∀I,K2,V2,i. ⇩[i] L2 ≡ K2.ⓑ{I}V2 →
                         ∃∃K1,V1. ⇩[i] L1 ≡ K1.ⓑ{I}V1 & lpx_sn R K1 K2 & R K1 V1 V2.
#R #L1 #L2 #H elim H -L1 -L2
[ #I0 #K0 #V0 #i #H elim (drop_inv_atom1 … H) -H #H destruct
| #I #K1 #K2 #V1 #V2 #HK12 #HV12 #IHK12 #I0 #K0 #V0 #i #H elim (drop_inv_O1_pair1 … H) * -H
  [ -IHK12 #H1 #H2 destruct /3 width=5 by drop_pair, ex3_2_intro/
  | -HK12 -HV12 #Hi #HK10 elim (IHK12 … HK10) -IHK12 -HK10
    /3 width=5 by drop_drop_lt, ex3_2_intro/
  ]
]
qed-.

lemma lpx_sn_deliftable_dropable: ∀R. l_deliftable_sn R → dropable_sn (lpx_sn R).
#R #HR #L1 #K1 #s #d #e #H elim H -L1 -K1 -d -e
[ #d #e #He #X #H >(lpx_sn_inv_atom1 … H) -H
  /4 width=3 by drop_atom, lpx_sn_atom, ex2_intro/
| #I #K1 #V1 #X #H elim (lpx_sn_inv_pair1 … H) -H
  #L2 #V2 #HL12 #HV12 #H destruct
  /3 width=5 by drop_pair, lpx_sn_pair, ex2_intro/
| #I #L1 #K1 #V1 #e #_ #IHLK1 #X #H elim (lpx_sn_inv_pair1 … H) -H
  #L2 #V2 #HL12 #HV12 #H destruct
  elim (IHLK1 … HL12) -L1 /3 width=3 by drop_drop, ex2_intro/
| #I #L1 #K1 #V1 #W1 #d #e #HLK1 #HWV1 #IHLK1 #X #H
  elim (lpx_sn_inv_pair1 … H) -H #L2 #V2 #HL12 #HV12 #H destruct
  elim (HR … HV12 … HLK1 … HWV1) -V1
  elim (IHLK1 … HL12) -L1 /3 width=5 by drop_skip, lpx_sn_pair, ex2_intro/
]
qed-.

lemma lpx_sn_liftable_dedropable: ∀R. (∀L. reflexive ? (R L)) →
                                  l_liftable R → dedropable_sn (lpx_sn R).
#R #H1R #H2R #L1 #K1 #s #d #e #H elim H -L1 -K1 -d -e
[ #d #e #He #X #H >(lpx_sn_inv_atom1 … H) -H
  /4 width=4 by drop_atom, lpx_sn_atom, ex3_intro/
| #I #K1 #V1 #X #H elim (lpx_sn_inv_pair1 … H) -H
  #K2 #V2 #HK12 #HV12 #H destruct
  lapply (lpx_sn_fwd_length … HK12)
  #H @(ex3_intro … (K2.ⓑ{I}V2)) (**) (* explicit constructor *)
  /3 width=1 by lpx_sn_pair, monotonic_le_plus_l/
  @leq_O2 normalize //
| #I #L1 #K1 #V1 #e #_ #IHLK1 #K2 #HK12 elim (IHLK1 … HK12) -K1
  /3 width=5 by drop_drop, leq_pair, lpx_sn_pair, ex3_intro/
| #I #L1 #K1 #V1 #W1 #d #e #HLK1 #HWV1 #IHLK1 #X #H
  elim (lpx_sn_inv_pair1 … H) -H #K2 #W2 #HK12 #HW12 #H destruct
  elim (lift_total W2 d e) #V2 #HWV2
  lapply (H2R … HW12 … HLK1 … HWV1 … HWV2) -W1
  elim (IHLK1 … HK12) -K1
  /3 width=6 by drop_skip, leq_succ, lpx_sn_pair, ex3_intro/
]
qed-.

fact lpx_sn_dropable_aux: ∀R,L2,K2,s,d,e. ⇩[s, d, e] L2 ≡ K2 → ∀L1. lpx_sn R L1 L2 →
                          d = 0 → ∃∃K1. ⇩[s, 0, e] L1 ≡ K1 & lpx_sn R K1 K2.
#R #L2 #K2 #s #d #e #H elim H -L2 -K2 -d -e
[ #d #e #He #X #H >(lpx_sn_inv_atom2 … H) -H 
  /4 width=3 by drop_atom, lpx_sn_atom, ex2_intro/
| #I #K2 #V2 #X #H elim (lpx_sn_inv_pair2 … H) -H
  #K1 #V1 #HK12 #HV12 #H destruct
  /3 width=5 by drop_pair, lpx_sn_pair, ex2_intro/
| #I #L2 #K2 #V2 #e #_ #IHLK2 #X #H #_ elim (lpx_sn_inv_pair2 … H) -H
  #L1 #V1 #HL12 #HV12 #H destruct
  elim (IHLK2 … HL12) -L2 /3 width=3 by drop_drop, ex2_intro/
| #I #L2 #K2 #V2 #W2 #d #e #_ #_ #_ #L1 #_
  <plus_n_Sm #H destruct
]
qed-.

lemma lpx_sn_dropable: ∀R. dropable_dx (lpx_sn R).
/2 width=5 by lpx_sn_dropable_aux/ qed-.
