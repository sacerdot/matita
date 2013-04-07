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

include "basic_2/grammar/lenv_append.ma".

(* SN POINTWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS *********)

inductive lpx_sn (R:lenv→relation term): relation lenv ≝
| lpx_sn_stom: lpx_sn R (⋆) (⋆)
| lpx_sn_pair: ∀I,K1,K2,V1,V2.
               lpx_sn R K1 K2 → R K1 V1 V2 →
               lpx_sn R (K1. ⓑ{I} V1) (K2. ⓑ{I} V2)
.

definition lpx_sn_confluent: predicate (lenv→relation term) ≝ λR.
                             ∀L0,T0,T1. R L0 T0 T1 → ∀T2. R L0 T0 T2 →
                             ∀L1. lpx_sn R L0 L1 → ∀L2. lpx_sn R L0 L2 →
                             ∃∃T. R L1 T1 T & R L2 T2 T.

definition lpx_sn_transitive: predicate (lenv→relation term) ≝ λR.
                              ∀L1,T1,T. R L1 T1 T → ∀L2. lpx_sn R L1 L2 →
                              ∀T2. R L2 T T2 → R L1 T1 T2.


(* Basic inversion lemmas ***************************************************)

fact lpx_sn_inv_atom1_aux: ∀R,L1,L2. lpx_sn R L1 L2 → L1 = ⋆ → L2 = ⋆.
#R #L1 #L2 * -L1 -L2
[ //
| #I #K1 #K2 #V1 #V2 #_ #_ #H destruct
]
qed-.

lemma lpx_sn_inv_atom1: ∀R,L2. lpx_sn R (⋆) L2 → L2 = ⋆.
/2 width=4 by lpx_sn_inv_atom1_aux/ qed-.

fact lpx_sn_inv_pair1_aux: ∀R,L1,L2. lpx_sn R L1 L2 → ∀I,K1,V1. L1 = K1. ⓑ{I} V1 →
                           ∃∃K2,V2. lpx_sn R K1 K2 & R K1 V1 V2 & L2 = K2. ⓑ{I} V2.
#R #L1 #L2 * -L1 -L2
[ #J #K1 #V1 #H destruct
| #I #K1 #K2 #V1 #V2 #HK12 #HV12 #J #L #W #H destruct /2 width=5/
]
qed-.

lemma lpx_sn_inv_pair1: ∀R,I,K1,V1,L2. lpx_sn R (K1. ⓑ{I} V1) L2 →
                        ∃∃K2,V2. lpx_sn R K1 K2 & R K1 V1 V2 & L2 = K2. ⓑ{I} V2.
/2 width=3 by lpx_sn_inv_pair1_aux/ qed-.

fact lpx_sn_inv_atom2_aux: ∀R,L1,L2. lpx_sn R L1 L2 → L2 = ⋆ → L1 = ⋆.
#R #L1 #L2 * -L1 -L2
[ //
| #I #K1 #K2 #V1 #V2 #_ #_ #H destruct
]
qed-.

lemma lpx_sn_inv_atom2: ∀R,L1. lpx_sn R L1 (⋆) → L1 = ⋆.
/2 width=4 by lpx_sn_inv_atom2_aux/ qed-.

fact lpx_sn_inv_pair2_aux: ∀R,L1,L2. lpx_sn R L1 L2 → ∀I,K2,V2. L2 = K2. ⓑ{I} V2 →
                           ∃∃K1,V1. lpx_sn R K1 K2 & R K1 V1 V2 & L1 = K1. ⓑ{I} V1.
#R #L1 #L2 * -L1 -L2
[ #J #K2 #V2 #H destruct
| #I #K1 #K2 #V1 #V2 #HK12 #HV12 #J #K #W #H destruct /2 width=5/
]
qed-.

lemma lpx_sn_inv_pair2: ∀R,I,L1,K2,V2. lpx_sn R L1 (K2. ⓑ{I} V2) →
                        ∃∃K1,V1. lpx_sn R K1 K2 & R K1 V1 V2 & L1 = K1. ⓑ{I} V1.
/2 width=3 by lpx_sn_inv_pair2_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lpx_sn_fwd_length: ∀R,L1,L2. lpx_sn R L1 L2 → |L1| = |L2|.
#R #L1 #L2 #H elim H -L1 -L2 normalize //
qed-.

(* Basic properties *********************************************************)

lemma lpx_sn_refl: ∀R. (∀L. reflexive ? (R L)) → reflexive … (lpx_sn R).
#R #HR #L elim L -L // /2 width=1/
qed-.

lemma lpx_sn_append: ∀R. l_appendable_sn R →
                     ∀K1,K2. lpx_sn R K1 K2 → ∀L1,L2. lpx_sn R L1 L2 →
                     lpx_sn R (L1 @@ K1) (L2 @@ K2).
#R #HR #K1 #K2 #H elim H -K1 -K2 // /3 width=1/
qed-.

lemma lpx_sn_trans: ∀R. lpx_sn_transitive R → Transitive … (lpx_sn R).
#R #HR #L1 #L #H elim H -L1 -L //
#I #L1 #L #V1 #V #HL1 #HV1 #IHL1 #X #H
elim (lpx_sn_inv_pair1 … H) -H #L2 #V2 #HL2 #HV2 #H destruct /3 width=5/
qed-.

lemma lpx_sn_conf: ∀R. lpx_sn_confluent R → confluent … (lpx_sn R).
#R #HR #L0 @(f_ind … length … L0) -L0 #n #IH *
[ #_ #X1 #H1 #X2 #H2 -n
  >(lpx_sn_inv_atom1 … H1) -X1
  >(lpx_sn_inv_atom1 … H2) -X2 /2 width=3/
| #L0 #I #V0 #Hn #X1 #H1 #X2 #H2 destruct
  elim (lpx_sn_inv_pair1 … H1) -H1 #L1 #V1 #HL01 #HV01 #H destruct
  elim (lpx_sn_inv_pair1 … H2) -H2 #L2 #V2 #HL02 #HV02 #H destruct
  elim (IH … HL01 … HL02) -IH normalize // #L #HL1 #HL2
  elim (HR … HV01 … HV02 … HL01 … HL02) -L0 -V0 /3 width=5/
]
qed-.
