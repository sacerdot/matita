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

(* LOCAL ENVIRONMENT REFINEMENT FOR SUBSTITUTION ****************************)

(* Auxiliary inversion lemmas ***********************************************)

fact lsubr_inv_abbr1_aux: ∀L1,L2. L1 ⊑ L2 → ∀K1,W. L1 = K1.ⓓW →
                          ∨∨ L2 = ⋆
                           | ∃∃K2. K1 ⊑ K2 & L2 = K2.ⓓW
                           | ∃∃K2,W2. K1 ⊑ K2 & L2 = K2.ⓛW2.
#L1 #L2 * -L1 -L2
[ #L #K1 #W #H destruct /2 width=1/
| #L1 #L2 #V #HL12 #K1 #W #H destruct /3 width=3/
| #I #L1 #L2 #V1 #V2 #HL12 #K1 #W #H destruct /3 width=4/
]
qed-.

lemma lsubr_inv_abbr1: ∀K1,L2,W. K1.ⓓW ⊑ L2 →
                       ∨∨ L2 = ⋆
                        | ∃∃K2. K1 ⊑ K2 & L2 = K2.ⓓW
                        | ∃∃K2,W2. K1 ⊑ K2 & L2 = K2.ⓛW2.
/2 width=3 by lsubr_inv_abbr1_aux/ qed-.

fact lsubr_inv_abst1_aux: ∀L1,L2. L1 ⊑ L2 → ∀K1,W1. L1 = K1.ⓛW1 →
                          L2 = ⋆ ∨
                          ∃∃K2,W2. K1 ⊑ K2 & L2 = K2.ⓛW2.
#L1 #L2 * -L1 -L2
[ #L #K1 #W1 #H destruct /2 width=1/
| #L1 #L2 #V #_ #K1 #W1 #H destruct
| #I #L1 #L2 #V1 #V2 #HL12 #K1 #W1 #H destruct /3 width=4/
]
qed-.

lemma lsubr_inv_abst1: ∀K1,L2,W1. K1.ⓛW1 ⊑ L2 →
                       L2 = ⋆ ∨
                       ∃∃K2,W2. K1 ⊑ K2 & L2 = K2.ⓛW2.
/2 width=4 by lsubr_inv_abst1_aux/ qed-.

(* Main properties **********************************************************)

theorem lsubr_trans: Transitive … lsubr.
#L1 #L #H elim H -L1 -L
[ #L1 #X #H
  lapply (lsubr_inv_atom1 … H) -H //
| #L1 #L #V #_ #IHL1 #X #H
  elim (lsubr_inv_abbr1 … H) -H // *
  #L2 [2: #V2 ] #HL2 #H destruct /3 width=1/
| #I #L1 #L #V1 #V #_ #IHL1 #X #H
  elim (lsubr_inv_abst1 … H) -H // *
  #L2 #V2 #HL2 #H destruct /3 width=1/
]
qed-.
