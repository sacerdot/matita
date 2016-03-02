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

include "ground_2/notation/relations/isuniform_1.ma".
include "ground_2/relocation/trace_isid.ma".

(* RELOCATION TRACE *********************************************************)

inductive isun: predicate trace ≝
| isun_id   : ∀t. 𝐈⦃t⦄ → isun t
| isun_false: ∀t. isun t → isun (Ⓕ@t)
.

interpretation "test for uniformity (trace)"
   'IsUniform t = (isun t).

(* Basic inversion lennas ***************************************************)

fact isun_inv_true_aux: ∀t. 𝐔⦃t⦄ → ∀u. t = Ⓣ@u → 𝐈⦃u⦄.
#t * -t
[ #t #Ht #u #H destruct /2 width=1 by isid_inv_true/
| #t #_ #u #H destruct
]
qed-.

lemma isun_inv_true: ∀t. 𝐔⦃Ⓣ@t⦄ → 𝐈⦃t⦄.
/2 width=3 by isun_inv_true_aux/ qed-.

fact isun_inv_false_aux: ∀t. 𝐔⦃t⦄ → ∀u. t = Ⓕ@u → 𝐔⦃u⦄.
#t * -t 
[ #t #Ht #u #H destruct elim (isid_inv_false … Ht)
| #t #Ht #u #H destruct //
]
qed-.

lemma isun_inv_false: ∀t. 𝐔⦃Ⓕ@t⦄ → 𝐔⦃t⦄.
/2 width=3 by isun_inv_false_aux/ qed-.
