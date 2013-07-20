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

include "basic_2/substitution/lsubr.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR EXTENDED REDUCTION **********************)

inductive lsubx: relation lenv ≝
| lsubx_sort: ∀L. lsubx L (⋆)
| lsubx_bind: ∀I,L1,L2,V. lsubx L1 L2 → lsubx (L1.ⓑ{I}V) (L2.ⓑ{I}V)
| lsubx_abst: ∀L1,L2,V,W. lsubx L1 L2 → lsubx (L1.ⓓⓝW.V) (L2.ⓛW)
.

interpretation
  "local environment refinement (extended reduction)"
  'CrSubEqT L1 L2 = (lsubx L1 L2).

(* Basic properties *********************************************************)

lemma lsubx_refl: ∀L. L ⓝ⊑ L.
#L elim L -L // /2 width=1/
qed.

(* Basic inversion lemmas ***************************************************)

fact lsubx_inv_atom1_aux: ∀L1,L2. L1 ⓝ⊑ L2 → L1 = ⋆ → L2 = ⋆.
#L1 #L2 * -L1 -L2 //
[ #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #V #W #_ #H destruct
]
qed-.

lemma lsubx_inv_atom1: ∀L2. ⋆ ⓝ⊑ L2 → L2 = ⋆.
/2 width=3 by lsubx_inv_atom1_aux/ qed-.

fact lsubx_inv_abst1_aux: ∀L1,L2. L1 ⓝ⊑ L2 → ∀K1,W. L1 = K1.ⓛW →
                          L2 = ⋆ ∨ ∃∃K2. K1 ⓝ⊑ K2 & L2 = K2.ⓛW.
#L1 #L2 * -L1 -L2
[ #L #K1 #W #H destruct /2 width=1/
| #I #L1 #L2 #V #HL12 #K1 #W #H destruct /3 width=3/
| #L1 #L2 #V1 #V2 #_ #K1 #W #H destruct
]
qed-.

lemma lsubx_inv_abst1: ∀K1,L2,W. K1.ⓛW ⓝ⊑ L2 →
                       L2 = ⋆ ∨ ∃∃K2. K1 ⓝ⊑ K2 & L2 = K2.ⓛW.
/2 width=3 by lsubx_inv_abst1_aux/ qed-.

fact lsubx_inv_abbr2_aux: ∀L1,L2. L1 ⓝ⊑ L2 → ∀K2,W. L2 = K2.ⓓW →
                          ∃∃K1. K1 ⓝ⊑ K2 & L1 = K1.ⓓW.
#L1 #L2 * -L1 -L2
[ #L #K2 #W #H destruct
| #I #L1 #L2 #V #HL12 #K2 #W #H destruct /2 width=3/
| #L1 #L2 #V1 #V2 #_ #K2 #W #H destruct
]
qed-.

lemma lsubx_inv_abbr2: ∀L1,K2,W. L1 ⓝ⊑ K2.ⓓW →
                       ∃∃K1. K1 ⓝ⊑ K2 & L1 = K1.ⓓW.
/2 width=3 by lsubx_inv_abbr2_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lsubx_fwd_length: ∀L1,L2. L1 ⓝ⊑ L2 → |L2| ≤ |L1|.
#L1 #L2 #H elim H -L1 -L2 // /2 width=1/
qed-.

lemma lsubx_fwd_lsubr: ∀L1,L2. L1 ⓝ⊑ L2 → L1 ⊑ L2.
#L1 #L2 #H elim H -L1 -L2 // /2 width=1/
qed-.

lemma lsubx_fwd_ldrop2_bind: ∀L1,L2. L1 ⓝ⊑ L2 →
                             ∀I,K2,W,i. ⇩[0, i] L2 ≡ K2.ⓑ{I}W →
                             (∃∃K1. K1 ⓝ⊑ K2 & ⇩[0, i] L1 ≡ K1.ⓑ{I}W) ∨
                             ∃∃K1,V. K1 ⓝ⊑ K2 & ⇩[0, i] L1 ≡ K1.ⓓⓝW.V.
#L1 #L2 #H elim H -L1 -L2
[ #L #I #K2 #W #i #H
  elim (ldrop_inv_atom1 … H) -H #H destruct
| #J #L1 #L2 #V #HL12 #IHL12 #I #K2 #W #i #H
  elim (ldrop_inv_O1_pair1 … H) -H * #Hi #HLK2 destruct [ -IHL12 | -HL12 ]
  [ /3 width=3/
  | elim (IHL12 … HLK2) -IHL12 -HLK2 * /4 width=3/ /4 width=4/
  ]
| #L1 #L2 #V1 #V2 #HL12 #IHL12 #I #K2 #W #i #H
  elim (ldrop_inv_O1_pair1 … H) -H * #Hi #HLK2 destruct [ -IHL12 | -HL12 ]
  [ /3 width=4/
  | elim (IHL12 … HLK2) -IHL12 -HLK2 * /4 width=3/ /4 width=4/
  ]
]
qed-.
