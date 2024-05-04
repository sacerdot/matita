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

include "static_2/notation/relations/approxeq_2.ma".
include "static_2/syntax/teqg.ma".

(* SORT-IRRELEVANT EQUIVALENCE ON TERMS *************************************)

definition teqx: relation term ≝
           teqg sfull.

interpretation
  "context-free sort-irrelevant equivalence (term)"
  'ApproxEq T1 T2 = (teqx T1 T2).

(* Basic properties *********************************************************)

lemma teqx_pair:
      ∀V1,V2. V1 ≅ V2 → ∀T1,T2. T1 ≅ T2 →
      ∀I. ②[I]V1.T1 ≅ ②[I]V2.T2.
/2 width=1 by teqg_pair/ qed.

lemma teqx_refl:
      reflexive … teqx.
/2 width=1 by teqg_refl/ qed.

lemma teqx_sym:
      symmetric … teqx.
/2 width=1 by teqg_sym/ qed-.

lemma teqg_teqx (S):
      ∀T1,T2. T1 ≛[S] T2 → T1 ≅ T2.
/2 width=3 by teqg_co/ qed.

(* Basic inversion lemmas ***************************************************)

lemma teqx_inv_sort1:
      ∀X2,s1. ⋆s1 ≅ X2 →
      ∃s2. X2 = ⋆s2.
#X1 #s1 #H elim (teqg_inv_sort1 … H) -H /2 width=2 by ex_intro/
qed-.
(*
lemma teqx_inv_lref1:
      ∀X,i. #i ≅ X → X = #i.
/2 width=5 by teqg_inv_lref1/ qed-.

lemma teqx_inv_gref1:
      ∀X,l. §l ≅ X → X = §l.
/2 width=5 by teqg_inv_gref1/ qed-.
*)
lemma teqx_inv_pair1:
      ∀I,V1,T1,X2. ②[I]V1.T1 ≅ X2 →
      ∃∃V2,T2. V1 ≅ V2 & T1 ≅ T2 & X2 = ②[I]V2.T2.
/2 width=3 by teqg_inv_pair1/ qed-.

lemma teqx_inv_sort2:
      ∀X1,s2. X1 ≅ ⋆s2 →
      ∃s1. X1 = ⋆s1.
#X1 #s2 #H elim (teqg_inv_sort2 … H) -H /2 width=2 by ex_intro/
qed-.

lemma teqx_inv_pair2:
      ∀I,X1,V2,T2. X1 ≅ ②[I]V2.T2 →
      ∃∃V1,T1. V1 ≅ V2 & T1 ≅ T2 & X1 = ②[I]V1.T1.
/2 width=1 by teqg_inv_pair2/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma teqx_inv_pair:
      ∀I1,I2,V1,V2,T1,T2. ②[I1]V1.T1 ≅ ②[I2]V2.T2 →
      ∧∧ I1 = I2 & V1 ≅ V2 & T1 ≅ T2.
/2 width=1 by teqg_inv_pair/ qed-.
(*
lemma teqx_inv_pair_xy_x:
      ∀I,V,T. ②[I]V.T ≅ V → ⊥.
/2 width=5 by teqg_inv_pair_xy_x/ qed-.

lemma teqx_inv_pair_xy_y:
      ∀I,T,V. ②[I]V.T ≅ T → ⊥.
/2 width=5 by teqg_inv_pair_xy_y/ qed-.
*)
(* Basic forward lemmas *****************************************************)
(*
lemma teqx_fwd_atom1:
      ∀I,Y. ⓪[I] ≅ Y → ∃J. Y = ⓪[J].
/2 width=3 by teqg_fwd_atom1/ qed-.
*)
(* Advanced properties ******************************************************)

lemma teqx_dec:
      ∀T1,T2. Decidable (T1 ≅ T2).
/3 width=1 by teqg_dec, or_introl/ qed-.

(* Negated inversion lemmas *************************************************)

lemma tneqx_inv_pair:
      ∀I1,I2,V1,V2,T1,T2.
      (②[I1]V1.T1 ≅ ②[I2]V2.T2 → ⊥) →
      ∨∨ I1 = I2 → ⊥
       | (V1 ≅ V2 → ⊥)
       | (T1 ≅ T2 → ⊥).
/3 width=1 by tneqg_inv_pair, or_introl/ qed-.
