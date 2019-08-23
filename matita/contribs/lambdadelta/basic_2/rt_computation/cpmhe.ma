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

include "basic_2/notation/relations/predevalstar_6.ma".
include "basic_2/rt_transition/cnh.ma".
include "basic_2/rt_computation/cpms.ma".

(* HEAD T-UNBOUND EVALUATION FOR T-BOUND RT-TRANSITION ON TERMS *************)

definition cpmhe (h) (n) (G) (L): relation2 term term ≝
           λT1,T2. ∧∧ ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2 & ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃T2⦄.

interpretation "t-unbound evaluation for t-bound context-sensitive parallel rt-transition (term)"
   'PRedEvalStar h n G L T1 T2 = (cpmhe h n G L T1 T2).

definition R_cpmhe (h) (G) (L) (T): predicate nat ≝
           λn. ∃U. ⦃G,L⦄ ⊢ T ➡*[h,n] 𝐍*⦃U⦄.

(* Basic properties *********************************************************)

lemma cpmhe_intro (h) (n) (G) (L):
      ∀T1,T2. ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2 → ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃T2⦄ → ⦃G,L⦄ ⊢ T1 ➡*[h,n] 𝐍*⦃T2⦄.
/2 width=1 by conj/ qed.

(* Advanced properties ******************************************************)

lemma cpmhe_sort (h) (n) (G) (L) (T):
      ∀s. ⦃G,L⦄ ⊢ T ➡*[n,h] ⋆s → ⦃G,L⦄ ⊢ T ➡*[h,n] 𝐍*⦃⋆s⦄.
/3 width=5 by cnh_sort, cpmhe_intro/ qed.

lemma cpmhe_ctop (h) (n) (G) (T):
      ∀i. ⦃G,⋆⦄ ⊢ T ➡*[n,h] #i → ⦃G,⋆⦄ ⊢ T ➡*[h,n] 𝐍*⦃#i⦄.
/3 width=5 by cnh_ctop, cpmhe_intro/ qed.

lemma cpmhe_zero (h) (n) (G) (L) (T):
      ∀I. ⦃G,L.ⓤ{I}⦄ ⊢ T ➡*[n,h] #0 → ⦃G,L.ⓤ{I}⦄ ⊢ T ➡*[h,n] 𝐍*⦃#0⦄.
/3 width=6 by cnh_zero, cpmhe_intro/ qed.

lemma cpmhe_gref (h) (n) (G) (L) (T):
      ∀l. ⦃G,L⦄ ⊢ T ➡*[n,h] §l → ⦃G,L⦄ ⊢ T ➡*[h,n] 𝐍*⦃§l⦄.
/3 width=5 by cnh_gref, cpmhe_intro/ qed.

lemma cpmhe_abst (h) (n) (p) (G) (L) (T):
      ∀W,U. ⦃G,L⦄ ⊢ T ➡*[n,h] ⓛ{p}W.U → ⦃G,L⦄ ⊢ T ➡*[h,n] 𝐍*⦃ⓛ{p}W.U⦄.
/3 width=5 by cnh_abst, cpmhe_intro/ qed.

lemma cpmhe_abbr_neg (h) (n) (G) (L) (T):
      ∀V,U. ⦃G,L⦄ ⊢ T ➡*[n,h] -ⓓV.U → ⦃G,L⦄ ⊢ T ➡*[h,n] 𝐍*⦃-ⓓV.U⦄.
/3 width=5 by cnh_abbr_neg, cpmhe_intro/ qed.

(* Basic forward lemmas *****************************************************)

lemma cpmhe_fwd_cpms (h) (n) (G) (L):
      ∀T1,T2. ⦃G,L⦄ ⊢ T1 ➡*[h,n] 𝐍*⦃T2⦄ → ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2.
#h #n #G #L #T1 #T2 * #HT12 #_ //
qed-.
