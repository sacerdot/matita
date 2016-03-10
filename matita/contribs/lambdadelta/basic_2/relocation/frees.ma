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

include "ground_2/relocation/trace_sor.ma".
include "ground_2/relocation/trace_isun.ma".
include "basic_2/notation/relations/freestar_3.ma".
include "basic_2/grammar/lenv.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

inductive frees: relation3 lenv term trace ≝
| frees_atom: ∀I. frees (⋆) (⓪{I}) (◊)
| frees_sort: ∀I,L,V,s,t. frees L (⋆s) t →
              frees (L.ⓑ{I}V) (⋆s) (Ⓕ @ t)
| frees_zero: ∀I,L,V,t. frees L V t →
              frees (L.ⓑ{I}V) (#0) (Ⓣ @ t)
| frees_lref: ∀I,L,V,i,t. frees L (#i) t →
              frees (L.ⓑ{I}V) (#⫯i) (Ⓕ @ t)
| frees_gref: ∀I,L,V,p,t. frees L (§p) t →
              frees (L.ⓑ{I}V) (§p) (Ⓕ @ t)
| frees_bind: ∀I,L,V,T,t1,t2,t,b,a. frees L V t1 → frees (L.ⓑ{I}V) T (b @ t2) →
              t1 ⋓ t2 ≡ t → frees L (ⓑ{a,I}V.T) t
| frees_flat: ∀I,L,V,T,t1,t2,t. frees L V t1 → frees L T t2 →
              t1 ⋓ t2 ≡ t → frees L (ⓕ{I}V.T) t
.

interpretation
   "context-sensitive free variables (term)"
   'FreeStar L T t = (frees L T t).

(* Basic forward lemmas *****************************************************)

fact frees_fwd_sort_aux: ∀L,X,t. L ⊢ 𝐅*⦃X⦄ ≡ t → ∀x. X = ⋆x → 𝐔⦃t⦄.
#L #X #t #H elim H -L -X -t /3 width=2 by isun_id, isun_false/
[ #_ #L #V #t #_ #_ #x #H destruct
| #_ #L #_ #i #t #_ #_ #x #H destruct
| #I #L #V #T #t1 #t2 #t #b #a #_ #_ #_ #_ #_ #x #H destruct
| #I #L #V #T #t1 #t2 #t #_ #_ #_ #_ #_ #x #H destruct
]
qed-.

lemma frees_fwd_sort: ∀L,t,s. L ⊢ 𝐅*⦃⋆s⦄ ≡ t → 𝐔⦃t⦄.
/2 width=5 by frees_fwd_sort_aux/ qed-.

fact frees_fwd_gref_aux: ∀L,X,t. L ⊢ 𝐅*⦃X⦄ ≡ t → ∀x. X = §x → 𝐔⦃t⦄.
#L #X #t #H elim H -L -X -t /3 width=2 by isun_id, isun_false/
[ #_ #L #V #t #_ #_ #x #H destruct
| #_ #L #_ #i #t #_ #_ #x #H destruct
| #I #L #V #T #t1 #t2 #t #b #a #_ #_ #_ #_ #_ #x #H destruct
| #I #L #V #T #t1 #t2 #t #_ #_ #_ #_ #_ #x #H destruct
]
qed-.

lemma frees_fwd_gref: ∀L,t,p. L ⊢ 𝐅*⦃§p⦄ ≡ t → 𝐔⦃t⦄.
/2 width=5 by frees_fwd_gref_aux/ qed-.

(* Basic inversion lemmas ***************************************************)

fact frees_inv_zero_aux: ∀L,X,t. L ⊢ 𝐅*⦃X⦄ ≡ t → X = #0 →
                         (L = ⋆ ∧ t = ◊) ∨
                         ∃∃I,K,V,u. K ⊢ 𝐅*⦃V⦄ ≡ u & L = K.ⓑ{I}V & t = Ⓣ@u.
#L #X #t * -L -X -t
[ /3 width=1 by or_introl, conj/
| #I #L #V #s #t #_ #H destruct
| /3 width=7 by ex3_4_intro, or_intror/
| #I #L #V #i #t #_ #H destruct
| #I #L #V #p #t #_ #H destruct
| #I #L #V #T #t1 #t2 #t #b #a #_ #_ #_ #H destruct
| #I #L #V #T #t1 #t2 #t #_ #_ #_ #H destruct
]
qed-.

lemma frees_inv_zero: ∀L,t. L ⊢ 𝐅*⦃#0⦄ ≡ t →
                      (L = ⋆ ∧ t = ◊) ∨
                      ∃∃I,K,V,u. K ⊢ 𝐅*⦃V⦄ ≡ u & L = K.ⓑ{I}V & t = Ⓣ@u.
/2 width=3 by frees_inv_zero_aux/ qed-.

fact frees_inv_lref_aux: ∀L,X,t. L ⊢ 𝐅*⦃X⦄ ≡ t → ∀j. X = #(⫯j) →
                         (L = ⋆ ∧ t = ◊) ∨
                         ∃∃I,K,V,u. K ⊢ 𝐅*⦃#j⦄ ≡ u & L = K.ⓑ{I}V & t = Ⓕ@u.
#L #X #t * -L -X -t
[ /3 width=1 by or_introl, conj/
| #I #L #V #s #t #_ #j #H destruct
| #I #L #V #t #_ #j #H destruct
| #I #L #V #i #t #Ht #j #H destruct /3 width=7 by ex3_4_intro, or_intror/
| #I #L #V #p #t #_ #j #H destruct
| #I #L #V #T #t1 #t2 #t #b #a #_ #_ #_ #j #H destruct
| #I #L #V #T #t1 #t2 #t #_ #_ #_ #j #H destruct
]
qed-.

lemma frees_inv_lref: ∀L,i,t. L ⊢ 𝐅*⦃#(⫯i)⦄ ≡ t →
                      (L = ⋆ ∧ t = ◊) ∨
                      ∃∃I,K,V,u. K ⊢ 𝐅*⦃#i⦄ ≡ u & L = K.ⓑ{I}V & t = Ⓕ@u.
/2 width=3 by frees_inv_lref_aux/ qed-.
