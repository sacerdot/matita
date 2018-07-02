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

include "static_2/notation/relations/lrsubeqc_2.ma".
include "static_2/syntax/lenv.ma".

(* RESTRICTED REFINEMENT FOR LOCAL ENVIRONMENTS *****************************)

(* Basic_2A1: just tpr_cpr and tprs_cprs require the extended lsubr_atom *)
(* Basic_2A1: includes: lsubr_pair *)
inductive lsubr: relation lenv ≝
| lsubr_atom: lsubr (⋆) (⋆)
| lsubr_bind: ∀I,L1,L2. lsubr L1 L2 → lsubr (L1.ⓘ{I}) (L2.ⓘ{I})
| lsubr_beta: ∀L1,L2,V,W. lsubr L1 L2 → lsubr (L1.ⓓⓝW.V) (L2.ⓛW)
| lsubr_unit: ∀I1,I2,L1,L2,V. lsubr L1 L2 → lsubr (L1.ⓑ{I1}V) (L2.ⓤ{I2})
.

interpretation
  "restricted refinement (local environment)"
  'LRSubEqC L1 L2 = (lsubr L1 L2).

(* Basic properties *********************************************************)

lemma lsubr_refl: ∀L. L ⫃ L.
#L elim L -L /2 width=1 by lsubr_atom, lsubr_bind/
qed.

(* Basic inversion lemmas ***************************************************)

fact lsubr_inv_atom1_aux: ∀L1,L2. L1 ⫃ L2 → L1 = ⋆ → L2 = ⋆.
#L1 #L2 * -L1 -L2 //
[ #I #L1 #L2 #_ #H destruct
| #L1 #L2 #V #W #_ #H destruct
| #I1 #I2 #L1 #L2 #V #_ #H destruct  
]
qed-.

lemma lsubr_inv_atom1: ∀L2. ⋆ ⫃ L2 → L2 = ⋆.
/2 width=3 by lsubr_inv_atom1_aux/ qed-.

fact lsubr_inv_bind1_aux: ∀L1,L2. L1 ⫃ L2 → ∀I,K1. L1 = K1.ⓘ{I} →
                          ∨∨ ∃∃K2. K1 ⫃ K2 & L2 = K2.ⓘ{I}
                           | ∃∃K2,V,W. K1 ⫃ K2 & L2 = K2.ⓛW &
                                       I = BPair Abbr (ⓝW.V)
                           | ∃∃J1,J2,K2,V. K1 ⫃ K2 & L2 = K2.ⓤ{J2} &
                                           I = BPair J1 V.
#L1 #L2 * -L1 -L2
[ #J #K1 #H destruct
| #I #L1 #L2 #HL12 #J #K1 #H destruct /3 width=3 by or3_intro0, ex2_intro/
| #L1 #L2 #V #W #HL12 #J #K1 #H destruct /3 width=6 by or3_intro1, ex3_3_intro/
| #I1 #I2 #L1 #L2 #V #HL12 #J #K1 #H destruct /3 width=4 by or3_intro2, ex3_4_intro/
]
qed-.

(* Basic_2A1: uses: lsubr_inv_pair1 *)
lemma lsubr_inv_bind1: ∀I,K1,L2. K1.ⓘ{I} ⫃ L2 →
                       ∨∨ ∃∃K2. K1 ⫃ K2 & L2 = K2.ⓘ{I}
                        | ∃∃K2,V,W. K1 ⫃ K2 & L2 = K2.ⓛW &
                                    I = BPair Abbr (ⓝW.V)
                        | ∃∃J1,J2,K2,V. K1 ⫃ K2 & L2 = K2.ⓤ{J2} &
                                        I = BPair J1 V.
/2 width=3 by lsubr_inv_bind1_aux/ qed-.

fact lsubr_inv_atom2_aux: ∀L1,L2. L1 ⫃ L2 → L2 = ⋆ → L1 = ⋆.
#L1 #L2 * -L1 -L2 //
[ #I #L1 #L2 #_ #H destruct
| #L1 #L2 #V #W #_ #H destruct
| #I1 #I2 #L1 #L2 #V #_ #H destruct
]
qed-.

lemma lsubr_inv_atom2: ∀L1. L1 ⫃ ⋆ → L1 = ⋆.
/2 width=3 by lsubr_inv_atom2_aux/ qed-.

fact lsubr_inv_bind2_aux: ∀L1,L2. L1 ⫃ L2 → ∀I,K2. L2 = K2.ⓘ{I} →
                          ∨∨ ∃∃K1. K1 ⫃ K2 & L1 = K1.ⓘ{I}
                           | ∃∃K1,W,V. K1 ⫃ K2 & L1 = K1.ⓓⓝW.V & I = BPair Abst W
                           | ∃∃J1,J2,K1,V. K1 ⫃ K2 & L1 = K1.ⓑ{J1}V & I = BUnit J2.
#L1 #L2 * -L1 -L2
[ #J #K2 #H destruct
| #I #L1 #L2 #HL12 #J #K2 #H destruct /3 width=3 by ex2_intro, or3_intro0/
| #L1 #L2 #V1 #V2 #HL12 #J #K2 #H destruct /3 width=6 by ex3_3_intro, or3_intro1/
| #I1 #I2 #L1 #L2 #V #HL12 #J #K2 #H destruct /3 width=5 by ex3_4_intro, or3_intro2/
]
qed-.

lemma lsubr_inv_bind2: ∀I,L1,K2. L1 ⫃ K2.ⓘ{I} →
                       ∨∨ ∃∃K1. K1 ⫃ K2 & L1 = K1.ⓘ{I}
                        | ∃∃K1,W,V. K1 ⫃ K2 & L1 = K1.ⓓⓝW.V & I = BPair Abst W
                        | ∃∃J1,J2,K1,V. K1 ⫃ K2 & L1 = K1.ⓑ{J1}V & I = BUnit J2.
/2 width=3 by lsubr_inv_bind2_aux/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma lsubr_inv_abst1: ∀K1,L2,W. K1.ⓛW ⫃ L2 →
                       ∨∨ ∃∃K2. K1 ⫃ K2 & L2 = K2.ⓛW
                        | ∃∃I2,K2. K1 ⫃ K2 & L2 = K2.ⓤ{I2}.
#K1 #L2 #W #H elim (lsubr_inv_bind1 … H) -H *
/3 width=4 by ex2_2_intro, ex2_intro, or_introl, or_intror/ 
#K2 #V2 #W2 #_ #_ #H destruct
qed-.

lemma lsubr_inv_unit1: ∀I,K1,L2. K1.ⓤ{I} ⫃ L2 →
                       ∃∃K2. K1 ⫃ K2 & L2 = K2.ⓤ{I}.
#I #K1 #L2 #H elim (lsubr_inv_bind1 … H) -H *
[ #K2 #HK12 #H destruct /2 width=3 by ex2_intro/
| #K2 #V #W #_ #_ #H destruct
| #I1 #I2 #K2 #V #_ #_ #H destruct
]
qed-.

lemma lsubr_inv_pair2: ∀I,L1,K2,W. L1 ⫃ K2.ⓑ{I}W →
                       ∨∨ ∃∃K1. K1 ⫃ K2 & L1 = K1.ⓑ{I}W
                        | ∃∃K1,V. K1 ⫃ K2 & L1 = K1.ⓓⓝW.V & I = Abst.
#I #L1 #K2 #W #H elim (lsubr_inv_bind2 … H) -H *
[ /3 width=3 by ex2_intro, or_introl/
| #K2 #X #V #HK12 #H1 #H2 destruct /3 width=4 by ex3_2_intro, or_intror/
| #I1 #I1 #K2 #V #_ #_ #H destruct   
]
qed-.

lemma lsubr_inv_abbr2: ∀L1,K2,V. L1 ⫃ K2.ⓓV →
                       ∃∃K1. K1 ⫃ K2 & L1 = K1.ⓓV.
#L1 #K2 #V #H elim (lsubr_inv_pair2 … H) -H *
[ /2 width=3 by ex2_intro/
| #K1 #X #_ #_ #H destruct
]
qed-.

lemma lsubr_inv_abst2: ∀L1,K2,W. L1 ⫃ K2.ⓛW →
                       ∨∨ ∃∃K1. K1 ⫃ K2 & L1 = K1.ⓛW
                        | ∃∃K1,V. K1 ⫃ K2 & L1 = K1.ⓓⓝW.V.
#L1 #K2 #W #H elim (lsubr_inv_pair2 … H) -H *
/3 width=4 by ex2_2_intro, ex2_intro, or_introl, or_intror/
qed-.

lemma lsubr_inv_unit2: ∀I,L1,K2. L1 ⫃ K2.ⓤ{I} →
                       ∨∨ ∃∃K1. K1 ⫃ K2 & L1 = K1.ⓤ{I}
                        | ∃∃J,K1,V. K1 ⫃ K2 & L1 = K1.ⓑ{J}V.
#I #L1 #K2 #H elim (lsubr_inv_bind2 … H) -H *
[ /3 width=3 by ex2_intro, or_introl/
| #K1 #W #V #_ #_ #H destruct
| #I1 #I2 #K1 #V #HK12 #H1 #H2 destruct /3 width=5 by ex2_3_intro, or_intror/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma lsubr_fwd_bind1: ∀I1,K1,L2. K1.ⓘ{I1} ⫃ L2 →
                       ∃∃I2,K2. K1 ⫃ K2 & L2 = K2.ⓘ{I2}.
#I1 #K1 #L2 #H elim (lsubr_inv_bind1 … H) -H *
[ #K2 #HK12 #H destruct /3 width=4 by ex2_2_intro/
| #K2 #W1 #V1 #HK12 #H1 #H2 destruct /3 width=4 by ex2_2_intro/
| #I1 #I2 #K2 #V1 #HK12 #H1 #H2 destruct /3 width=4 by ex2_2_intro/
]
qed-.

lemma lsubr_fwd_bind2: ∀I2,L1,K2. L1 ⫃ K2.ⓘ{I2} →
                       ∃∃I1,K1. K1 ⫃ K2 & L1 = K1.ⓘ{I1}.
#I2 #L1 #K2 #H elim (lsubr_inv_bind2 … H) -H *
[ #K1 #HK12 #H destruct /3 width=4 by ex2_2_intro/
| #K1 #W1 #V1 #HK12 #H1 #H2 destruct /3 width=4 by ex2_2_intro/
| #I1 #I2 #K1 #V1 #HK12 #H1 #H2 destruct /3 width=4 by ex2_2_intro/
]
qed-.
