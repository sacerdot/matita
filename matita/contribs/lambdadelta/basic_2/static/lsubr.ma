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

include "basic_2/notation/relations/lrsubeqc_2.ma".
include "basic_2/substitution/drop.ma".

(* RESTRICTED LOCAL ENVIRONMENT REFINEMENT **********************************)

inductive lsubr: relation lenv ≝
| lsubr_atom: ∀L. lsubr L (⋆)
| lsubr_pair: ∀I,L1,L2,V. lsubr L1 L2 → lsubr (L1.ⓑ{I}V) (L2.ⓑ{I}V)
| lsubr_beta: ∀L1,L2,V,W. lsubr L1 L2 → lsubr (L1.ⓓⓝW.V) (L2.ⓛW)
.

interpretation
  "local environment refinement (restricted)"
  'LRSubEqC L1 L2 = (lsubr L1 L2).

(* Basic properties *********************************************************)

lemma lsubr_refl: ∀L. L ⫃ L.
#L elim L -L /2 width=1 by lsubr_atom, lsubr_pair/
qed.

(* Basic inversion lemmas ***************************************************)

fact lsubr_inv_atom1_aux: ∀L1,L2. L1 ⫃ L2 → L1 = ⋆ → L2 = ⋆.
#L1 #L2 * -L1 -L2 //
[ #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #V #W #_ #H destruct
]
qed-.

lemma lsubr_inv_atom1: ∀L2. ⋆ ⫃ L2 → L2 = ⋆.
/2 width=3 by lsubr_inv_atom1_aux/ qed-.

fact lsubr_inv_abst1_aux: ∀L1,L2. L1 ⫃ L2 → ∀K1,W. L1 = K1.ⓛW →
                          L2 = ⋆ ∨ ∃∃K2. K1 ⫃ K2 & L2 = K2.ⓛW.
#L1 #L2 * -L1 -L2
[ #L #K1 #W #H destruct /2 width=1 by or_introl/
| #I #L1 #L2 #V #HL12 #K1 #W #H destruct /3 width=3 by ex2_intro, or_intror/
| #L1 #L2 #V1 #V2 #_ #K1 #W #H destruct
]
qed-.

lemma lsubr_inv_abst1: ∀K1,L2,W. K1.ⓛW ⫃ L2 →
                       L2 = ⋆ ∨ ∃∃K2. K1 ⫃ K2 & L2 = K2.ⓛW.
/2 width=3 by lsubr_inv_abst1_aux/ qed-.

fact lsubr_inv_abbr2_aux: ∀L1,L2. L1 ⫃ L2 → ∀K2,W. L2 = K2.ⓓW →
                          ∃∃K1. K1 ⫃ K2 & L1 = K1.ⓓW.
#L1 #L2 * -L1 -L2
[ #L #K2 #W #H destruct
| #I #L1 #L2 #V #HL12 #K2 #W #H destruct /2 width=3 by ex2_intro/
| #L1 #L2 #V1 #V2 #_ #K2 #W #H destruct
]
qed-.

lemma lsubr_inv_abbr2: ∀L1,K2,W. L1 ⫃ K2.ⓓW →
                       ∃∃K1. K1 ⫃ K2 & L1 = K1.ⓓW.
/2 width=3 by lsubr_inv_abbr2_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lsubr_fwd_length: ∀L1,L2. L1 ⫃ L2 → |L2| ≤ |L1|.
#L1 #L2 #H elim H -L1 -L2 /2 width=1 by monotonic_le_plus_l/
qed-.

lemma lsubr_fwd_drop2_pair: ∀L1,L2. L1 ⫃ L2 →
                            ∀I,K2,W,s,i. ⇩[s, 0, i] L2 ≡ K2.ⓑ{I}W →
                            (∃∃K1. K1 ⫃ K2 & ⇩[s, 0, i] L1 ≡ K1.ⓑ{I}W) ∨
                            ∃∃K1,V. K1 ⫃ K2 & ⇩[s, 0, i] L1 ≡ K1.ⓓⓝW.V & I = Abst.
#L1 #L2 #H elim H -L1 -L2
[ #L #I #K2 #W #s #i #H
  elim (drop_inv_atom1 … H) -H #H destruct
| #J #L1 #L2 #V #HL12 #IHL12 #I #K2 #W #s #i #H
  elim (drop_inv_O1_pair1 … H) -H * #Hi #HLK2 destruct [ -IHL12 | -HL12 ]
  [ /3 width=3 by drop_pair, ex2_intro, or_introl/
  | elim (IHL12 … HLK2) -IHL12 -HLK2 *
    /4 width=4 by drop_drop_lt, ex3_2_intro, ex2_intro, or_introl, or_intror/
  ]
| #L1 #L2 #V1 #V2 #HL12 #IHL12 #I #K2 #W #s #i #H
  elim (drop_inv_O1_pair1 … H) -H * #Hi #HLK2 destruct [ -IHL12 | -HL12 ]
  [ /3 width=4 by drop_pair, ex3_2_intro, or_intror/
  | elim (IHL12 … HLK2) -IHL12 -HLK2 *
    /4 width=4 by drop_drop_lt, ex3_2_intro, ex2_intro, or_introl, or_intror/
  ]
]
qed-.

lemma lsubr_fwd_drop2_abbr: ∀L1,L2. L1 ⫃ L2 →
                            ∀K2,V,s,i. ⇩[s, 0, i] L2 ≡ K2.ⓓV →
                            ∃∃K1. K1 ⫃ K2 & ⇩[s, 0, i] L1 ≡ K1.ⓓV.
#L1 #L2 #HL12 #K2 #V #s #i #HLK2 elim (lsubr_fwd_drop2_pair … HL12 … HLK2) -L2 // *
#K1 #W #_ #_ #H destruct
qed-.
