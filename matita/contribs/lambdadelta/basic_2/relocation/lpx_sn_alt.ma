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

include "basic_2/relocation/ldrop.ma".
include "basic_2/relocation/lpx_sn.ma".

(* SN POINTWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS *********)

(* alternative definition of lpx_sn_alt *)
inductive lpx_sn_alt (R:relation3 lenv term term): relation lenv ≝
| lpx_sn_alt_intro: ∀L1,L2.
                    (∀I1,I2,K1,K2,V1,V2,i.
                       ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 → I1 = I2 ∧ R K1 V1 V2
                    ) →
                    (∀I1,I2,K1,K2,V1,V2,i.
                       ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 → lpx_sn_alt R K1 K2
                    ) → |L1| = |L2| → lpx_sn_alt R L1 L2
.

(* Basic forward lemmas ******************************************************)

lemma lpx_sn_alt_fwd_length: ∀R,L1,L2. lpx_sn_alt R L1 L2 → |L1| = |L2|.
#R #L1 #L2 * -L1 -L2 //
qed-.

(* Basic inversion lemmas ***************************************************)

lemma lpx_sn_alt_inv_gen: ∀R,L1,L2. lpx_sn_alt R L1 L2 →
                          |L1| = |L2| ∧
                          ∀I1,I2,K1,K2,V1,V2,i.
                          ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                          ∧∧ I1 = I2 & R K1 V1 V2 & lpx_sn_alt R K1 K2.
#R #L1 #L2 * -L1 -L2
#L1 #L2 #IH1 #IH2 #HL12 @conj //
#I1 #I2 #K1 #K2 #HLK1 #HLK2 #i #HLK1 #HLK2
elim (IH1 … HLK1 HLK2) -IH1 /3 width=7 by and3_intro/
qed-.

lemma lpx_sn_alt_inv_atom1: ∀R,L2. lpx_sn_alt R (⋆) L2 → L2 = ⋆.
#R #L2 #H lapply (lpx_sn_alt_fwd_length … H) -H
normalize /2 width=1 by length_inv_zero_sn/
qed-.

lemma lpx_sn_alt_inv_pair1: ∀R,I,L2,K1,V1. lpx_sn_alt R (K1.ⓑ{I}V1) L2 →
                            ∃∃K2,V2. lpx_sn_alt R K1 K2 & R K1 V1 V2 & L2 = K2.ⓑ{I}V2.
#R #I1 #L2 #K1 #V1 #H elim (lpx_sn_alt_inv_gen … H) -H
#H #IH elim (length_inv_pos_sn … H) -H
#I2 #K2 #V2 #HK12 #H destruct
elim (IH I1 I2 K1 K2 V1 V2 0) -IH /2 width=5 by ex3_2_intro/
qed-.

lemma lpx_sn_alt_inv_atom2: ∀R,L1. lpx_sn_alt R L1 (⋆) → L1 = ⋆.
#R #L1 #H lapply (lpx_sn_alt_fwd_length … H) -H
normalize /2 width=1 by length_inv_zero_dx/
qed-.

lemma lpx_sn_alt_inv_pair2: ∀R,I,L1,K2,V2. lpx_sn_alt R L1 (K2.ⓑ{I}V2) →
                            ∃∃K1,V1. lpx_sn_alt R K1 K2 & R K1 V1 V2 & L1 = K1.ⓑ{I}V1.
#R #I2 #L1 #K2 #V2 #H elim (lpx_sn_alt_inv_gen … H) -H
#H #IH elim (length_inv_pos_dx … H) -H
#I1 #K1 #V1 #HK12 #H destruct
elim (IH I1 I2 K1 K2 V1 V2 0) -IH /2 width=5 by ex3_2_intro/
qed-.

(* Basic properties *********************************************************)

lemma lpx_sn_alt_intro_alt: ∀R,L1,L2. |L1| = |L2| →
                            (∀I1,I2,K1,K2,V1,V2,i.
                               ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                               ∧∧ I1 = I2 & R K1 V1 V2 & lpx_sn_alt R K1 K2
                            ) → lpx_sn_alt R L1 L2.
#R #L1 #L2 #HL12 #IH @lpx_sn_alt_intro // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #i #HLK1 #HLK2
elim (IH … HLK1 HLK2) -IH -HLK1 -HLK2 /2 width=1 by conj/
qed.

lemma lpx_sn_alt_atom: ∀R. lpx_sn_alt R (⋆) (⋆).
#R @lpx_sn_alt_intro_alt //
#I1 #I2 #K1 #K2 #V1 #V2 #i #HLK1 elim (ldrop_inv_atom1 … HLK1) -HLK1
#H destruct
qed.

lemma lpx_sn_alt_pair: ∀R,I,L1,L2,V1,V2.
                       lpx_sn_alt R L1 L2 → R L1 V1 V2 →
                       lpx_sn_alt R (L1.ⓑ{I}V1) (L2.ⓑ{I}V2).
#R #I #L1 #L2 #V1 #V2 #H #HV12 elim (lpx_sn_alt_inv_gen … H) -H
#HL12 #IH @lpx_sn_alt_intro_alt normalize //
#I1 #I2 #K1 #K2 #W1 #W2 #i @(nat_ind_plus … i) -i
[ #HLK1 #HLK2
  lapply (ldrop_inv_O2 … HLK1) -HLK1 #H destruct
  lapply (ldrop_inv_O2 … HLK2) -HLK2 #H destruct
  /4 width=3 by lpx_sn_alt_intro_alt, and3_intro/
| -HL12 -HV12 /3 width=5 by ldrop_inv_drop1/
]
qed.

(* Main properties **********************************************************)

theorem lpx_sn_lpx_sn_alt: ∀R,L1,L2. lpx_sn R L1 L2 → lpx_sn_alt R L1 L2.
#R #L1 #L2 #H elim H -L1 -L2
/2 width=1 by lpx_sn_alt_atom, lpx_sn_alt_pair/
qed.

(* Main inversion lemmas ****************************************************)

theorem lpx_sn_alt_inv_lpx_sn: ∀R,L1,L2. lpx_sn_alt R L1 L2 → lpx_sn R L1 L2.
#R #L1 elim L1 -L1
[ #L2 #H lapply (lpx_sn_alt_inv_atom1 … H) -H //
| #L1 #I #V1 #IH #X #H elim (lpx_sn_alt_inv_pair1 … H) -H
  #L2 #V2 #HL12 #HV12 #H destruct /3 width=1 by lpx_sn_pair/
]
qed-.

(* Advanced properties ******************************************************)

lemma lpx_sn_intro_alt: ∀R,L1,L2. |L1| = |L2| →
                        (∀I1,I2,K1,K2,V1,V2,i.
                           ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                           ∧∧ I1 = I2 & R K1 V1 V2 & lpx_sn R K1 K2
                        ) → lpx_sn R L1 L2.
#R #L1 #L2 #HL12 #IH @lpx_sn_alt_inv_lpx_sn
@lpx_sn_alt_intro_alt // -HL12
#I1 #I2 #K1 #K2 #V1 #V2 #i #HLK1 #HLK2
elim (IH … HLK1 HLK2) -IH -HLK1 -HLK2 /3 width=1 by lpx_sn_lpx_sn_alt, and3_intro/
qed.

(* Advanced inversion lemmas ************************************************)

lemma lpx_sn_inv_gen: ∀R,L1,L2. lpx_sn R L1 L2 →
                      |L1| = |L2| ∧
                      ∀I1,I2,K1,K2,V1,V2,i.
                      ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L2 ≡ K2.ⓑ{I2}V2 →
                      ∧∧ I1 = I2 & R K1 V1 V2 & lpx_sn R K1 K2.
#R #L1 #L2 #H lapply (lpx_sn_lpx_sn_alt … H) -H
#H elim (lpx_sn_alt_inv_gen … H) -H
#HL12 #IH @conj //
#I1 #I2 #K1 #K2 #V1 #V2 #i #HLK1 #HLK2
elim (IH … HLK1 HLK2) -IH -HLK1 -HLK2 /3 width=1 by lpx_sn_alt_inv_lpx_sn, and3_intro/
qed-.
