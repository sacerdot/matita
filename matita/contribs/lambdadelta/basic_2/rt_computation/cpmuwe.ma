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

include "basic_2/notation/relations/predevalwstar_6.ma".
include "basic_2/rt_computation/cnuw.ma".

(* T-UNBOUND WHD EVALUATION FOR T-BOUND RT-TRANSITION ON TERMS **************)

definition cpmuwe (h) (n) (G) (L): relation2 term term ≝
           λT1,T2. ∧∧ ❪G,L❫ ⊢ T1 ➡*[h,n] T2 & ❪G,L❫ ⊢ ➡𝐍𝐖*[h] T2.

interpretation "t-unbound whd evaluation for t-bound context-sensitive parallel rt-transition (term)"
   'PRedEvalWStar h n G L T1 T2 = (cpmuwe h n G L T1 T2).

definition R_cpmuwe (h) (G) (L) (T): predicate nat ≝
           λn. ∃U. ❪G,L❫ ⊢ T ➡*𝐍𝐖*[h,n] U.

(* Basic properties *********************************************************)

lemma cpmuwe_intro (h) (n) (G) (L):
      ∀T1,T2. ❪G,L❫ ⊢ T1 ➡*[h,n] T2 → ❪G,L❫ ⊢ ➡𝐍𝐖*[h] T2 → ❪G,L❫ ⊢ T1 ➡*𝐍𝐖*[h,n] T2.
/2 width=1 by conj/ qed.

(* Advanced properties ******************************************************)

lemma cpmuwe_sort (h) (n) (G) (L) (T):
      ∀s. ❪G,L❫ ⊢ T ➡*[h,n] ⋆s → ❪G,L❫ ⊢ T ➡*𝐍𝐖*[h,n] ⋆s.
/3 width=5 by cnuw_sort, cpmuwe_intro/ qed.

lemma cpmuwe_ctop (h) (n) (G) (T):
      ∀i. ❪G,⋆❫ ⊢ T ➡*[h,n] #i → ❪G,⋆❫ ⊢ T ➡*𝐍𝐖*[h,n] #i.
/3 width=5 by cnuw_ctop, cpmuwe_intro/ qed.

lemma cpmuwe_zero_unit (h) (n) (G) (L) (T):
      ∀I. ❪G,L.ⓤ[I]❫ ⊢ T ➡*[h,n] #0 → ❪G,L.ⓤ[I]❫ ⊢ T ➡*𝐍𝐖*[h,n] #0.
/3 width=6 by cnuw_zero_unit, cpmuwe_intro/ qed.

lemma cpmuwe_gref (h) (n) (G) (L) (T):
      ∀l. ❪G,L❫ ⊢ T ➡*[h,n] §l → ❪G,L❫ ⊢ T ➡*𝐍𝐖*[h,n] §l.
/3 width=5 by cnuw_gref, cpmuwe_intro/ qed.

(* Basic forward lemmas *****************************************************)

lemma cpmuwe_fwd_cpms (h) (n) (G) (L):
      ∀T1,T2. ❪G,L❫ ⊢ T1 ➡*𝐍𝐖*[h,n] T2 → ❪G,L❫ ⊢ T1 ➡*[h,n] T2.
#h #n #G #L #T1 #T2 * #HT12 #_ //
qed-.
