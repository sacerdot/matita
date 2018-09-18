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

include "static_2/notation/relations/positive_3.ma".
include "static_2/syntax/item_sd.ma".
include "static_2/syntax/term.ma".

(* DEGREE POSITIVITY ON TERMS ***********************************************)

inductive tdpos (h) (o): predicate term ≝
| tdpos_sort: ∀s,d. deg h o s (↑d) → tdpos h o (⋆s)
| tdpos_lref: ∀i. tdpos h o (#i)
| tdpos_gref: ∀l. tdpos h o (§l)
| tdpos_pair: ∀I,V,T. tdpos h o V → tdpos h o T → tdpos h o (②{I}V.T)
.

interpretation
   "context-free degree positivity (term)"
   'Positive h o T = (tdpos h o T).

(* Basic inversion lemmas ***************************************************)

fact tdpos_inv_sort_aux (h) (o): 
                        ∀X. 𝐏[h,o]⦃X⦄ → ∀s. X = ⋆s → ∃d. deg h o s (↑d).
#h #o #H *
[ #s #d #Hsd #x #H destruct /2 width=2 by ex_intro/
| #i #x #H destruct
| #l #x #H destruct
| #I #V #T #_ #_ #x #H destruct
]
qed-.

lemma tdpos_inv_sort (h) (o): ∀s. 𝐏[h,o]⦃⋆s⦄ → ∃d. deg h o s (↑d).
/2 width=3 by tdpos_inv_sort_aux/ qed-.

fact tdpos_inv_pair_aux (h) (o): ∀X. 𝐏[h,o]⦃X⦄ → ∀I,V,T. X = ②{I}V.T →
                                 ∧∧ 𝐏[h,o]⦃V⦄ & 𝐏[h,o]⦃T⦄.
#h #o #H *
[ #s #d #_ #Z #X1 #X2 #H destruct
| #i #Z #X1 #X2 #H destruct
| #l #Z #X1 #X2 #H destruct
| #I #V #T #HV #HT #Z #X1 #X2 #H destruct /2 width=1 by conj/
]
qed-.

lemma tdpos_inv_pair (h) (o): ∀I,V,T. 𝐏[h,o]⦃②{I}V.T⦄ →
                              ∧∧ 𝐏[h,o]⦃V⦄ & 𝐏[h,o]⦃T⦄.
/2 width=4 by tdpos_inv_pair_aux/ qed-.

(* Basic properties *********************************************************)

axiom tdpos_total (h): ∀T. ∃o. 𝐏[h,o]⦃T⦄.
