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
| lpx_sn_atom: lpx_sn R (⋆) (⋆)
| lpx_sn_pair: ∀I,K1,K2,V1,V2.
               lpx_sn R K1 K2 → R K1 V1 V2 →
               lpx_sn R (K1. ⓑ{I} V1) (K2. ⓑ{I} V2)
.

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

(* Advanced forward lemmas **************************************************)

lemma lpx_sn_fwd_append1: ∀R,L1,K1,L. lpx_sn R (K1 @@ L1) L →
                          ∃∃K2,L2. lpx_sn R K1 K2 &  L = K2 @@ L2.
#R #L1 elim L1 -L1
[ #K1 #K2 #HK12
  @(ex2_2_intro … K2 (⋆)) // (* explicit constructor, /2 width=4/ does not work *)
| #L1 #I #V1 #IH #K1 #X #H
  elim (lpx_sn_inv_pair1 … H) -H #L #V2 #H1 #HV12 #H destruct
  elim (IH … H1) -IH -H1 #K2 #L2 #HK12 #H destruct
  @(ex2_2_intro … (L2.ⓑ{I}V2) HK12) // (* explicit constructor, /2 width=4/ does not work *)
]
qed-.

lemma lpx_sn_fwd_append2: ∀R,L2,K2,L. lpx_sn R L (K2 @@ L2) →
                          ∃∃K1,L1. lpx_sn R K1 K2 & L = K1 @@ L1.
#R #L2 elim L2 -L2
[ #K2 #K1 #HK12
  @(ex2_2_intro … K1 (⋆)) // (**) (* explicit constructor, /2 width=4/ does not work *)
| #L2 #I #V2 #IH #K2 #X #H
  elim (lpx_sn_inv_pair2 … H) -H #L #V1 #H1 #HV12 #H destruct
  elim (IH … H1) -IH -H1 #K1 #L1 #HK12 #H destruct
  @(ex2_2_intro … (L1.ⓑ{I}V1) HK12) // (* explicit constructor, /2 width=4/ does not work *)
]
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
