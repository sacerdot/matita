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

include "ground_2/notation/relations/isid_1.ma".
include "ground_2/relocation/trace_after.ma".

(* RELOCATION TRACE *********************************************************)

definition isid: predicate trace ≝ λcs. ∥cs∥ = |cs|.

interpretation "test for identity (trace)"
   'IsId cs = (isid cs).

(* Basic properties *********************************************************)

lemma isid_empty: 𝐈⦃◊⦄.
// qed.

lemma isid_true: ∀cs. 𝐈⦃cs⦄ → 𝐈⦃Ⓣ @ cs⦄.
// qed.

(* Basic inversion lemmas ***************************************************)

lemma isid_inv_true: ∀cs. 𝐈⦃Ⓣ @ cs⦄ → 𝐈⦃cs⦄.
/2 width=1 by injective_S/ qed-.

lemma isid_inv_false: ∀cs. 𝐈⦃Ⓕ @ cs⦄ → ⊥.
/3 width=4 by colength_le, lt_le_false/ qed-.

lemma isid_inv_cons: ∀cs,b.  𝐈⦃b @ cs⦄ → 𝐈⦃cs⦄ ∧ b = Ⓣ.
#cs * #H /3 width=1 by isid_inv_true, conj/
elim (isid_inv_false … H)
qed-.

(* Properties on application ************************************************)

lemma isid_at: ∀cs. (∀i1,i2. @⦃i1, cs⦄ ≡ i2 → i1 = i2) → 𝐈⦃cs⦄.
#cs elim cs -cs // * /2 width=1 by/
qed.

(* Inversion lemmas on application ******************************************)

lemma isid_inv_at: ∀cs,i1,i2. @⦃i1, cs⦄ ≡ i2 → 𝐈⦃cs⦄ → i1 = i2.
#cs #i1 #i2 #H elim H -cs -i1 -i2 /4 width=1 by isid_inv_true, eq_f/
#cs #i1 #i2 #_ #IH #H elim (isid_inv_false … H)
qed-.

(* Properties on composition ************************************************)

lemma isid_after_sn: ∀cs1,cs2. cs1 ⊚ cs2 ≡ cs2 →  𝐈⦃cs1⦄ .
#cs1 #cs2 #H elim (after_inv_length … H) -H //
qed.

lemma isid_after_dx: ∀cs1,cs2. cs1 ⊚ cs2 ≡ cs1 →  𝐈⦃cs2⦄ .
#cs1 #cs2 #H elim (after_inv_length … H) -H //
qed.

(* Inversion lemmas on composition ******************************************)

lemma isid_inv_after_sn: ∀cs1,cs2,cs. cs1 ⊚ cs2 ≡ cs →  𝐈⦃cs1⦄ → cs = cs2.
#cs1 #cs2 #cs #H elim H -cs1 -cs2 -cs //
#cs1 #cs2 #cs #_ [ #b ] #IH #H
[ >IH -IH // | elim (isid_inv_false … H) ]
qed-.

lemma isid_inv_after_dx: ∀cs1,cs2,cs. cs1 ⊚ cs2 ≡ cs →  𝐈⦃cs2⦄ → cs = cs1.
#cs1 #cs2 #cs #H elim H -cs1 -cs2 -cs //
#cs1 #cs2 #cs #_ [ #b ] #IH #H
[ elim (isid_inv_cons … H) -H #H >IH -IH // | >IH -IH // ]
qed-.
