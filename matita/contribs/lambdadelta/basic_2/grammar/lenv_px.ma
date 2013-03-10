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

(* POINTWISE EXTENSION OF A CONTEXT-FREE REALTION FOR TERMS *****************)

inductive lpx (R:relation term): relation lenv ≝
| lpx_stom: lpx R (⋆) (⋆)
| lpx_pair: ∀I,K1,K2,V1,V2.
            lpx R K1 K2 → R V1 V2 → lpx R (K1. ⓑ{I} V1) (K2. ⓑ{I} V2)
.

(* Basic inversion lemmas ***************************************************)

fact lpx_inv_atom1_aux: ∀R,L1,L2. lpx R L1 L2 → L1 = ⋆ → L2 = ⋆.
#R #L1 #L2 * -L1 -L2
[ //
| #I #K1 #K2 #V1 #V2 #_ #_ #H destruct
]
qed-.

lemma lpx_inv_atom1: ∀R,L2. lpx R (⋆) L2 → L2 = ⋆.
/2 width=4 by lpx_inv_atom1_aux/ qed-.

fact lpx_inv_pair1_aux: ∀R,L1,L2. lpx R L1 L2 → ∀I,K1,V1. L1 = K1. ⓑ{I} V1 →
                        ∃∃K2,V2. lpx R K1 K2 & R V1 V2 & L2 = K2. ⓑ{I} V2.
#R #L1 #L2 * -L1 -L2
[ #J #K1 #V1 #H destruct
| #I #K1 #K2 #V1 #V2 #HK12 #HV12 #J #L #W #H destruct /2 width=5/
]
qed-.

lemma lpx_inv_pair1: ∀R,I,K1,V1,L2. lpx R (K1. ⓑ{I} V1) L2 →
                     ∃∃K2,V2. lpx R K1 K2 & R V1 V2 & L2 = K2. ⓑ{I} V2.
/2 width=3 by lpx_inv_pair1_aux/ qed-.

fact lpx_inv_atom2_aux: ∀R,L1,L2. lpx R L1 L2 → L2 = ⋆ → L1 = ⋆.
#R #L1 #L2 * -L1 -L2
[ //
| #I #K1 #K2 #V1 #V2 #_ #_ #H destruct
]
qed-.

lemma lpx_inv_atom2: ∀R,L1. lpx R L1 (⋆) → L1 = ⋆.
/2 width=4 by lpx_inv_atom2_aux/ qed-.

fact lpx_inv_pair2_aux: ∀R,L1,L2. lpx R L1 L2 → ∀I,K2,V2. L2 = K2. ⓑ{I} V2 →
                        ∃∃K1,V1. lpx R K1 K2 & R V1 V2 & L1 = K1. ⓑ{I} V1.
#R #L1 #L2 * -L1 -L2
[ #J #K2 #V2 #H destruct
| #I #K1 #K2 #V1 #V2 #HK12 #HV12 #J #K #W #H destruct /2 width=5/
]
qed-.

lemma lpx_inv_pair2: ∀R,I,L1,K2,V2. lpx R L1 (K2. ⓑ{I} V2) →
                     ∃∃K1,V1. lpx R K1 K2 & R V1 V2 & L1 = K1. ⓑ{I} V1.
/2 width=3 by lpx_inv_pair2_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lpx_fwd_length: ∀R,L1,L2. lpx R L1 L2 → |L1| = |L2|.
#R #L1 #L2 #H elim H -L1 -L2 normalize //
qed-.

(* Advanced inversion lemmas ************************************************)

lemma lpx_inv_append1: ∀R,L1,K1,L. lpx R (K1 @@ L1) L →
                       ∃∃K2,L2. lpx R K1 K2 & lpx R L1 L2 & L = K2 @@ L2.
#R #L1 elim L1 -L1 normalize
[ #K1 #K2 #HK12
  @(ex3_2_intro … K2 (⋆)) // (**) (* explicit constructor, /2 width=5/ does not work *)
| #L1 #I #V1 #IH #K1 #X #H
  elim (lpx_inv_pair1 … H) -H #L #V2 #H1 #HV12 #H destruct
  elim (IH … H1) -IH -H1 #K2 #L2 #HK12 #HL12 #H destruct
  @(ex3_2_intro … HK12) [2: /2 width=2/ | skip | // ] (* explicit constructor, /3 width=5/ does not work *)
]
qed-.

lemma lpx_inv_append2: ∀R,L2,K2,L. lpx R L (K2 @@ L2) →
                       ∃∃K1,L1. lpx R K1 K2 & lpx R L1 L2 & L = K1 @@ L1.
#R #L2 elim L2 -L2 normalize
[ #K2 #K1 #HK12
  @(ex3_2_intro … K1 (⋆)) // (**) (* explicit constructor, /2 width=5/ does not work *)
| #L2 #I #V2 #IH #K2 #X #H
  elim (lpx_inv_pair2 … H) -H #L #V1 #H1 #HV12 #H destruct
  elim (IH … H1) -IH -H1 #K1 #L1 #HK12 #HL12 #H destruct
  @(ex3_2_intro … HK12) [2: /2 width=2/ | skip | // ] (* explicit constructor, /3 width=5/ does not work *)
]
qed-.

(* Basic properties *********************************************************)

lemma lpx_refl: ∀R. reflexive ? R → reflexive … (lpx R).
#R #HR #L elim L -L // /2 width=1/
qed.

lemma lpx_sym: ∀R. symmetric ? R → symmetric … (lpx R).
#R #HR #L1 #L2 #H elim H -H // /3 width=1/
qed.

lemma lpx_trans: ∀R. Transitive ? R → Transitive … (lpx R).
#R #HR #L1 #L #H elim H -L //
#I #K1 #K #V1 #V #_ #HV1 #IHK1 #X #H
elim (lpx_inv_pair1 … H) -H #K2 #V2 #HK2 #HV2 #H destruct /3 width=3/
qed.

lemma lpx_conf: ∀R. confluent ? R → confluent … (lpx R).
#R #HR #L0 #L1 #H elim H -L1
[ #X #H >(lpx_inv_atom1 … H) -X /2 width=3/
| #I #K0 #K1 #V0 #V1 #_ #HV01 #IHK01 #X #H
  elim (lpx_inv_pair1 … H) -H #K2 #V2 #HK02 #HV02 #H destruct
  elim (IHK01 … HK02) -K0 #K #HK1 #HK2
  elim (HR … HV01 … HV02) -HR -V0 /3 width=5/
]
qed.

lemma lpx_TC_inj: ∀R,L1,L2. lpx R L1 L2 → lpx (TC … R) L1 L2.
#R #L1 #L2 #H elim H -L1 -L2 // /3 width=1/
qed.

lemma lpx_TC_step: ∀R,L1,L. lpx (TC … R) L1 L →
                   ∀L2. lpx R L L2 → lpx (TC … R) L1 L2.
#R #L1 #L #H elim H -L /2 width=1/
#I #K1 #K #V1 #V #_ #HV1 #IHK1 #X #H
elim (lpx_inv_pair1 … H) -H #K2 #V2 #HK2 #HV2 #H destruct /3 width=3/
qed.

lemma TC_lpx_pair_dx: ∀R. reflexive ? R →
                      ∀I,K,V1,V2. TC … R V1 V2 →
                      TC … (lpx R) (K.ⓑ{I}V1) (K.ⓑ{I}V2).
#R #HR #I #K #V1 #V2 #H elim H -V2
/4 width=5 by lpx_refl, lpx_pair, inj, step/ (**) (* too slow without trace *)
qed.

lemma TC_lpx_pair_sn: ∀R. reflexive ? R →
                      ∀I,V,K1,K2. TC … (lpx R) K1 K2 →
                      TC … (lpx R) (K1.ⓑ{I}V) (K2.ⓑ{I}V).
#R #HR #I #V #K1 #K2 #H elim H -K2
/4 width=5 by lpx_refl, lpx_pair, inj, step/ (**) (* too slow without trace *)
qed.

lemma lpx_TC: ∀R,L1,L2. TC … (lpx R) L1 L2 → lpx (TC … R) L1 L2.
#R #L1 #L2 #H elim H -L2 /2 width=1/ /2 width=3/
qed.

lemma lpx_inv_TC: ∀R. reflexive ? R →
                  ∀L1,L2. lpx (TC … R) L1 L2 → TC … (lpx R) L1 L2.
#R #HR #L1 #L2 #H elim H -L1 -L2 /3 width=1/ /3 width=3/
qed.

lemma lpx_append: ∀R,K1,K2. lpx R K1 K2 → ∀L1,L2. lpx R L1 L2 →
                  lpx R (L1 @@ K1) (L2 @@ K2).
#R #K1 #K2 #H elim H -K1 -K2 // /3 width=1/
qed.
