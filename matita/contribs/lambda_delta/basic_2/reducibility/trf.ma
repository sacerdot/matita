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

include "basic_2/grammar/term_simple.ma".

(* CONTEXT-FREE REDUCIBLE TERMS *********************************************)

(* reducible terms *)
inductive trf: predicate term ≝
| trf_abst_sn: ∀V,T.   trf V → trf (ⓛV. T)
| trf_abst_dx: ∀V,T.   trf T → trf (ⓛV. T)
| trf_appl_sn: ∀V,T.   trf V → trf (ⓐV. T)
| trf_appl_dx: ∀V,T.   trf T → trf (ⓐV. T)
| trf_abbr   : ∀V,T.           trf (ⓓV. T)
| trf_cast   : ∀V,T.           trf (ⓣV. T)
| trf_beta   : ∀V,W,T. trf (ⓐV. ⓛW. T)
.

interpretation
   "context-free reducibility (term)"
   'Reducible T = (trf T).

(* Basic inversion lemmas ***************************************************)

fact trf_inv_atom_aux: ∀I,T. 𝐑⦃T⦄ → T =  ⓪{I} → ⊥.
#I #T * -T
[ #V #T #_ #H destruct
| #V #T #_ #H destruct
| #V #T #_ #H destruct
| #V #T #_ #H destruct
| #V #T #H destruct
| #V #T #H destruct
| #V #W #T #H destruct
]
qed.

lemma trf_inv_atom: ∀I. 𝐑⦃⓪{I}⦄ → ⊥.
/2 width=4/ qed-.

fact trf_inv_abst_aux: ∀W,U,T. 𝐑⦃T⦄ → T =  ⓛW. U → 𝐑⦃W⦄ ∨ 𝐑⦃U⦄.
#W #U #T * -T
[ #V #T #HV #H destruct /2 width=1/
| #V #T #HT #H destruct /2 width=1/
| #V #T #_ #H destruct
| #V #T #_ #H destruct
| #V #T #H destruct
| #V #T #H destruct
| #V #W0 #T #H destruct
]
qed.

lemma trf_inv_abst: ∀V,T. 𝐑⦃ⓛV.T⦄ → 𝐑⦃V⦄ ∨ 𝐑⦃T⦄.
/2 width=3/ qed-.

fact trf_inv_appl_aux: ∀W,U,T. 𝐑⦃T⦄ → T =  ⓐW. U →
                       ∨∨ 𝐑⦃W⦄ | 𝐑⦃U⦄ | (𝐒⦃U⦄ → ⊥).
#W #U #T * -T
[ #V #T #_ #H destruct
| #V #T #_ #H destruct
| #V #T #HV #H destruct /2 width=1/
| #V #T #HT #H destruct /2 width=1/
| #V #T #H destruct
| #V #T #H destruct
| #V #W0 #T #H destruct
  @or3_intro2 #H elim (simple_inv_bind … H)
]
qed.

lemma trf_inv_appl: ∀W,U. 𝐑⦃ⓐW.U⦄ → ∨∨ 𝐑⦃W⦄ | 𝐑⦃U⦄ | (𝐒⦃U⦄ → ⊥).
/2 width=3/ qed-.
