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

include "static_2/syntax/bind.ma".

(* EXTENSION TO BINDERS OF A RELATION FOR TERMS *****************************)

inductive ext2 (R:relation term): relation bind ≝
| ext2_unit: ∀I. ext2 R (BUnit I) (BUnit I)
| ext2_pair: ∀I,V1,V2. R V1 V2 → ext2 R (BPair I V1) (BPair I V2)
.

(* Basic_inversion lemmas **************************************************)

fact ext2_inv_unit_sn_aux: ∀R,Z1,Z2. ext2 R Z1 Z2 →
                           ∀I. Z1 = BUnit I → Z2 = BUnit I.
#R #Z1 #Z2 * -Z1 -Z2 #I [2: #V1 #V2 #_ ]
#J #H destruct //
qed-.

lemma ext2_inv_unit_sn: ∀R,I,Z2. ext2 R (BUnit I) Z2 → Z2 = BUnit I.
/2 width=4 by ext2_inv_unit_sn_aux/ qed-.

fact ext2_inv_pair_sn_aux: ∀R,Z1,Z2. ext2 R Z1 Z2 →
                           ∀I,V1. Z1 = BPair I V1 →
                           ∃∃V2. R V1 V2 & Z2 = BPair I V2.
#R #Z1 #Z2 * -Z1 -Z2 #I [2: #V1 #V2 #HV12 ]
#J #W1 #H destruct /2 width=3 by ex2_intro/
qed-.

lemma ext2_inv_pair_sn: ∀R,Z2,I,V1. ext2 R (BPair I V1) Z2 →
                        ∃∃V2. R V1 V2 & Z2 = BPair I V2.
/2 width=3 by ext2_inv_pair_sn_aux/ qed-.

fact ext2_inv_unit_dx_aux: ∀R,Z1,Z2. ext2 R Z1 Z2 →
                           ∀I. Z2 = BUnit I → Z1 = BUnit I.
#R #Z1 #Z2 * -Z1 -Z2 #I [2: #V1 #V2 #_ ]
#J #H destruct //
qed-.

lemma ext2_inv_unit_dx: ∀R,I,Z1. ext2 R Z1 (BUnit I) → Z1 = BUnit I.
/2 width=4 by ext2_inv_unit_dx_aux/ qed-.

fact ext2_inv_pair_dx_aux: ∀R,Z1,Z2. ext2 R Z1 Z2 →
                           ∀I,V2. Z2 = BPair I V2 →
                           ∃∃V1. R V1 V2 & Z1 = BPair I V1.
#R #Z1 #Z2 * -Z1 -Z2 #I [2: #V1 #V2 #HV12 ]
#J #W2 #H destruct /2 width=3 by ex2_intro/
qed-.

lemma ext2_inv_pair_dx: ∀R,Z1,I,V2. ext2 R Z1 (BPair I V2) →
                        ∃∃V1. R V1 V2 & Z1 = BPair I V1.
/2 width=3 by ext2_inv_pair_dx_aux/ qed-.

(* Advanced inversion lemmas ***********************************************)

lemma ext2_inv_unit: ∀R,I1,I2. ext2 R (BUnit I1) (BUnit I2) → I1 = I2.
#R #I1 #I2 #H lapply (ext2_inv_unit_sn … H) -H
#H destruct //
qed-.

lemma ext2_inv_pair: ∀R,I1,I2,V1,V2. ext2 R (BPair I1 V1) (BPair I2 V2) →
                     I1 = I2 ∧ R V1 V2.
#R #I1 #I2 #V1 #V2 #H elim (ext2_inv_pair_sn … H) -H
#V #HV #H destruct /2 width=1 by conj/
qed-.

(* Basic properties ********************************************************)

lemma ext2_refl: ∀R. reflexive … R → reflexive … (ext2 R).
#R #HR * /2 width=1 by ext2_pair/
qed.

lemma ext2_sym: ∀R. symmetric … R → symmetric … (ext2 R).
#R #HR #T1 #T2 * /3 width=1 by ext2_unit, ext2_pair/
qed-.

lemma ext2_dec: ∀R. (∀T1,T2. Decidable (R T1 T2)) →
                ∀I1,I2. Decidable (ext2 R I1 I2).
#R #HR * #I1 [2: #T1 ] * #I2 [2,4: #T2 ]
[ elim (eq_bind2_dec I1 I2) #HI12 destruct
  [ elim (HR T1 T2) -HR #HT12 /3 width=1 by ext2_pair, or_introl/ ]
  @or_intror #H elim (ext2_inv_pair … H) -H /2 width=1 by/
| @or_intror #H lapply (ext2_inv_unit_sn … H) -H
  #H destruct
| @or_intror #H lapply (ext2_inv_unit_dx … H) -H
  #H destruct
| elim (eq_bind1_dec I1 I2) #HI12 destruct
  /4 width=2 by ext2_inv_unit, ext2_unit, or_intror, or_introl/
]
qed-.
