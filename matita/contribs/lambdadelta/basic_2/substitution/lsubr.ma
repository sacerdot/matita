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

(* LOCAL ENVIRONMENT REFINEMENT FOR SUBSTITUTION ****************************)

inductive lsubr: relation lenv ≝
| lsubr_sort: ∀L. lsubr L (⋆)
| lsubr_abbr: ∀L1,L2,V. lsubr L1 L2 → lsubr (L1. ⓓV) (L2.ⓓV)
| lsubr_abst: ∀I,L1,L2,V1,V2. lsubr L1 L2 → lsubr (L1. ⓑ{I}V1) (L2. ⓛV2)
.

interpretation
  "local environment refinement (substitution)"
  'SubEq L1 L2 = (lsubr L1 L2).

definition lsubr_trans: ∀S. predicate (lenv → relation S) ≝ λS,R.
                        ∀L2,s1,s2. R L2 s1 s2 → ∀L1. L1 ⊑ L2 → R L1 s1 s2.

(* Basic properties *********************************************************)

lemma lsubr_bind: ∀I,L1,L2,V. L1 ⊑ L2 → L1. ⓑ{I} V ⊑ L2.ⓑ{I} V.
* /2 width=1/ qed.

lemma lsubr_abbr: ∀I,L1,L2,V. L1 ⊑ L2 → L1. ⓓV ⊑ L2. ⓑ{I}V.
* /2 width=1/ qed.

lemma lsubr_refl: ∀L. L ⊑ L.
#L elim L -L // /2 width=1/
qed.

lemma TC_lsubr_trans: ∀S,R. lsubr_trans S R → lsubr_trans S (LTC … R).
#S #R #HR #L1 #s1 #s2 #H elim H -s2
[ /3 width=3/
| #s #s2 #_ #Hs2 #IHs1 #L2 #HL12
  lapply (HR … Hs2 … HL12) -HR -Hs2 /3 width=3/
]
qed.

(* Basic inversion lemmas ***************************************************)

fact lsubr_inv_atom1_aux: ∀L1,L2. L1 ⊑ L2 → L1 = ⋆ → L2 = ⋆.
#L1 #L2 * -L1 -L2 //
[ #L1 #L2 #V #_ #H destruct
| #I #L1 #L2 #V1 #V2 #_ #H destruct
]
qed-.

lemma lsubr_inv_atom1: ∀L2. ⋆ ⊑ L2 → L2 = ⋆.
/2 width=3 by lsubr_inv_atom1_aux/ qed-.

fact lsubr_inv_abbr2_aux: ∀L1,L2. L1 ⊑ L2 → ∀K2,W. L2 = K2.ⓓW →
                          ∃∃K1. K1 ⊑ K2 & L1 = K1.ⓓW.
#L1 #L2 * -L1 -L2
[ #L #K2 #W #H destruct
| #L1 #L2 #V #HL12 #K2 #W #H destruct /2 width=3/
| #I #L1 #L2 #V1 #V2 #_ #K2 #W #H destruct
]
qed-.

lemma lsubr_inv_abbr2: ∀L1,K2,W. L1 ⊑ K2.ⓓW →
                       ∃∃K1. K1 ⊑ K2 & L1 = K1.ⓓW.
/2 width=3 by lsubr_inv_abbr2_aux/ qed-.

fact lsubr_inv_abst2_aux: ∀L1,L2. L1 ⊑ L2 → ∀K2,W2. L2 = K2.ⓛW2 →
                          ∃∃I,K1,W1. K1 ⊑ K2 & L1 = K1.ⓑ{I}W1.
#L1 #L2 * -L1 -L2
[ #L #K2 #W2 #H destruct
| #L1 #L2 #V #_ #K2 #W2 #H destruct
| #I #L1 #L2 #V1 #V2 #HL12 #K2 #W2 #H destruct /2 width=5/
]
qed-.

lemma lsubr_inv_abst2: ∀L1,K2,W2. L1 ⊑ K2.ⓛW2 →
                       ∃∃I,K1,W1. K1 ⊑ K2 & L1 = K1.ⓑ{I}W1.
/2 width=4 by lsubr_inv_abst2_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lsubr_fwd_length: ∀L1,L2. L1 ⊑ L2 → |L2| ≤ |L1|.
#L1 #L2 #H elim H -L1 -L2 // /2 width=1/
qed-.

lemma lsubr_fwd_ldrop2_abbr: ∀L1,L2. L1 ⊑ L2 →
                             ∀K2,W,i. ⇩[0, i] L2 ≡ K2. ⓓW →
                             ∃∃K1. K1 ⊑ K2 & ⇩[0, i] L1 ≡ K1. ⓓW.
#L1 #L2 #H elim H -L1 -L2
[ #L #K2 #W #i #H
  lapply (ldrop_inv_atom1 … H) -H #H destruct
| #L1 #L2 #V #HL12 #IHL12 #K2 #W #i #H
  elim (ldrop_inv_O1 … H) -H * #Hi #HLK2 destruct [ -IHL12 | -HL12 ]
  [ /2 width=3/
  | elim (IHL12 … HLK2) -IHL12 -HLK2 /3 width=3/
  ]
| #I #L1 #L2 #V1 #V2 #_ #IHL12 #K2 #W #i #H
  elim (ldrop_inv_O1 … H) -H * #Hi #HLK2 destruct
  elim (IHL12 … HLK2) -IHL12 -HLK2 /3 width=3/
]
qed-.