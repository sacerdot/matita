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

include "basic_2/grammar/lenv_length.ma".

(* SN POINTWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS *********)

inductive lpx_sn (R:relation4 bind2 lenv term term): relation lenv ≝
| lpx_sn_atom: lpx_sn R (⋆) (⋆)
| lpx_sn_pair: ∀I,K1,K2,V1,V2.
               lpx_sn R K1 K2 → R I K1 V1 V2 →
               lpx_sn R (K1.ⓑ{I}V1) (K2.ⓑ{I}V2)
.

(* Basic properties *********************************************************)

lemma lpx_sn_refl: ∀R. (∀I,L. reflexive ? (R I L)) → reflexive … (lpx_sn R).
#R #HR #L elim L -L /2 width=1 by lpx_sn_atom, lpx_sn_pair/
qed-.

(* Basic inversion lemmas ***************************************************)

fact lpx_sn_inv_atom1_aux: ∀R,L1,L2. lpx_sn R L1 L2 → L1 = ⋆ → L2 = ⋆.
#R #L1 #L2 * -L1 -L2
[ //
| #I #K1 #K2 #V1 #V2 #_ #_ #H destruct
]
qed-.

lemma lpx_sn_inv_atom1: ∀R,L2. lpx_sn R (⋆) L2 → L2 = ⋆.
/2 width=4 by lpx_sn_inv_atom1_aux/ qed-.

fact lpx_sn_inv_pair1_aux: ∀R,L1,L2. lpx_sn R L1 L2 → ∀I,K1,V1. L1 = K1.ⓑ{I}V1 →
                           ∃∃K2,V2. lpx_sn R K1 K2 & R I K1 V1 V2 & L2 = K2.ⓑ{I}V2.
#R #L1 #L2 * -L1 -L2
[ #J #K1 #V1 #H destruct
| #I #K1 #K2 #V1 #V2 #HK12 #HV12 #J #L #W #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma lpx_sn_inv_pair1: ∀R,I,K1,V1,L2. lpx_sn R (K1.ⓑ{I}V1) L2 →
                        ∃∃K2,V2. lpx_sn R K1 K2 & R I K1 V1 V2 & L2 = K2.ⓑ{I}V2.
/2 width=3 by lpx_sn_inv_pair1_aux/ qed-.

fact lpx_sn_inv_atom2_aux: ∀R,L1,L2. lpx_sn R L1 L2 → L2 = ⋆ → L1 = ⋆.
#R #L1 #L2 * -L1 -L2
[ //
| #I #K1 #K2 #V1 #V2 #_ #_ #H destruct
]
qed-.

lemma lpx_sn_inv_atom2: ∀R,L1. lpx_sn R L1 (⋆) → L1 = ⋆.
/2 width=4 by lpx_sn_inv_atom2_aux/ qed-.

fact lpx_sn_inv_pair2_aux: ∀R,L1,L2. lpx_sn R L1 L2 → ∀I,K2,V2. L2 = K2.ⓑ{I}V2 →
                           ∃∃K1,V1. lpx_sn R K1 K2 & R I K1 V1 V2 & L1 = K1.ⓑ{I}V1.
#R #L1 #L2 * -L1 -L2
[ #J #K2 #V2 #H destruct
| #I #K1 #K2 #V1 #V2 #HK12 #HV12 #J #K #W #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma lpx_sn_inv_pair2: ∀R,I,L1,K2,V2. lpx_sn R L1 (K2.ⓑ{I}V2) →
                        ∃∃K1,V1. lpx_sn R K1 K2 & R I K1 V1 V2 & L1 = K1.ⓑ{I}V1.
/2 width=3 by lpx_sn_inv_pair2_aux/ qed-.

lemma lpx_sn_inv_pair: ∀R,I1,I2,L1,L2,V1,V2.
                       lpx_sn R (L1.ⓑ{I1}V1) (L2.ⓑ{I2}V2) →
                       ∧∧ lpx_sn R L1 L2 & R I1 L1 V1 V2 & I1 = I2.
#R #I1 #I2 #L1 #L2 #V1 #V2 #H elim (lpx_sn_inv_pair1 … H) -H
#L0 #V0 #HL10 #HV10 #H destruct /2 width=1 by and3_intro/
qed-.

(* Basic forward lemmas *****************************************************)

lemma lpx_sn_fwd_length: ∀R,L1,L2. lpx_sn R L1 L2 → |L1| = |L2|.
#R #L1 #L2 #H elim H -L1 -L2 normalize //
qed-.
