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
include "basic_2/grammar/lenv.ma".

(* RESTRICTED REFINEMENT FOR LOCAL ENVIRONMENTS *****************************)

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
