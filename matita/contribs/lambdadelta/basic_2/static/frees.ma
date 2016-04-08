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

include "ground_2/relocation/rtmap_sor.ma".
include "basic_2/notation/relations/freestar_3.ma".
include "basic_2/grammar/lenv.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

inductive frees: relation3 lenv term rtmap ≝
| frees_atom: ∀I,f. 𝐈⦃f⦄ → frees (⋆) (⓪{I}) f
| frees_sort: ∀I,L,V,s,f. frees L (⋆s) f →
              frees (L.ⓑ{I}V) (⋆s) (↑f)
| frees_zero: ∀I,L,V,f. frees L V f →
              frees (L.ⓑ{I}V) (#0) (⫯f)
| frees_lref: ∀I,L,V,i,f. frees L (#i) f →
              frees (L.ⓑ{I}V) (#⫯i) (↑f)
| frees_gref: ∀I,L,V,p,f. frees L (§p) f →
              frees (L.ⓑ{I}V) (§p) (↑f)
| frees_bind: ∀I,L,V,T,a,f1,f2,f. frees L V f1 → frees (L.ⓑ{I}V) T f2 →
              f1 ⋓ ⫱f2 ≡ f → frees L (ⓑ{a,I}V.T) f
| frees_flat: ∀I,L,V,T,f1,f2,f. frees L V f1 → frees L T f2 →
              f1 ⋓ f2 ≡ f → frees L (ⓕ{I}V.T) f
.

interpretation
   "context-sensitive free variables (term)"
   'FreeStar L T t = (frees L T t).

(* Basic inversion lemmas ***************************************************)

fact frees_inv_atom_aux: ∀L,X,f. L ⊢ 𝐅*⦃X⦄ ≡ f → ∀J. L = ⋆ → X = ⓪{J} → 𝐈⦃f⦄.
#L #X #f #H elim H -L -X -f /3 width=3 by isid_push/
[5,6: #I #L #V #T [ #p ] #f1 #f2 #f #_ #_ #_ #_ #_ #J #_ #H destruct
|*: #I #L #V [1,3,4: #x ] #f #_ #_ #J #H destruct
]
qed-.

lemma frees_inv_atom: ∀I,f. ⋆ ⊢ 𝐅*⦃⓪{I}⦄ ≡ f → 𝐈⦃f⦄.
/2 width=6 by frees_inv_atom_aux/ qed-.

fact frees_inv_sort_aux: ∀L,X,f. L ⊢ 𝐅*⦃X⦄ ≡ f → ∀x. X = ⋆x → 𝐈⦃f⦄.
#L #X #f #H elim H -L -X -f /3 width=3 by isid_push/
[ #_ #L #V #f #_ #_ #x #H destruct
| #_ #L #_ #i #f #_ #_ #x #H destruct
| #I #L #V #T #p #f1 #f2 #f #_ #_ #_ #_ #_ #x #H destruct
| #I #L #V #T #f1 #f2 #f #_ #_ #_ #_ #_ #x #H destruct
]
qed-.

lemma frees_inv_sort: ∀L,s,f. L ⊢ 𝐅*⦃⋆s⦄ ≡ f → 𝐈⦃f⦄.
/2 width=5 by frees_inv_sort_aux/ qed-.

fact frees_inv_gref_aux: ∀L,X,f. L ⊢ 𝐅*⦃X⦄ ≡ f → ∀x. X = §x → 𝐈⦃f⦄.
#L #X #f #H elim H -L -X -f /3 width=3 by isid_push/
[ #_ #L #V #f #_ #_ #x #H destruct
| #_ #L #_ #i #f #_ #_ #x #H destruct
| #I #L #V #T #p #f1 #f2 #f #_ #_ #_ #_ #_ #x #H destruct
| #I #L #V #T #f1 #f2 #f #_ #_ #_ #_ #_ #x #H destruct
]
qed-.

lemma frees_inv_gref: ∀L,l,f. L ⊢ 𝐅*⦃§l⦄ ≡ f → 𝐈⦃f⦄.
/2 width=5 by frees_inv_gref_aux/ qed-.

fact frees_inv_zero_aux: ∀L,X,f. L ⊢ 𝐅*⦃X⦄ ≡ f → X = #0 →
                         (L = ⋆ ∧ 𝐈⦃f⦄) ∨
                         ∃∃I,K,V,g. K ⊢ 𝐅*⦃V⦄ ≡ g & L = K.ⓑ{I}V & f = ⫯g.
#L #X #f * -L -X -f
[ /3 width=1 by or_introl, conj/
| #I #L #V #s #f #_ #H destruct
| /3 width=7 by ex3_4_intro, or_intror/
| #I #L #V #i #f #_ #H destruct
| #I #L #V #l #f #_ #H destruct
| #I #L #V #T #p #f1 #f2 #f #_ #_ #_ #H destruct
| #I #L #V #T #f1 #f2 #f #_ #_ #_ #H destruct
]
qed-.

lemma frees_inv_zero: ∀L,f. L ⊢ 𝐅*⦃#0⦄ ≡ f →
                      (L = ⋆ ∧ 𝐈⦃f⦄) ∨
                      ∃∃I,K,V,g. K ⊢ 𝐅*⦃V⦄ ≡ g & L = K.ⓑ{I}V & f = ⫯g.
/2 width=3 by frees_inv_zero_aux/ qed-.

fact frees_inv_lref_aux: ∀L,X,f. L ⊢ 𝐅*⦃X⦄ ≡ f → ∀j. X = #(⫯j) →
                         (L = ⋆ ∧ 𝐈⦃f⦄) ∨
                         ∃∃I,K,V,g. K ⊢ 𝐅*⦃#j⦄ ≡ g & L = K.ⓑ{I}V & f = ↑g.
#L #X #f * -L -X -f
[ /3 width=1 by or_introl, conj/
| #I #L #V #s #f #_ #j #H destruct
| #I #L #V #f #_ #j #H destruct
| #I #L #V #i #f #Ht #j #H destruct /3 width=7 by ex3_4_intro, or_intror/
| #I #L #V #l #f #_ #j #H destruct
| #I #L #V #T #p #f1 #f2 #f #_ #_ #_ #j #H destruct
| #I #L #V #T #f1 #f2 #f #_ #_ #_ #j #H destruct
]
qed-.

lemma frees_inv_lref: ∀L,i,f. L ⊢ 𝐅*⦃#(⫯i)⦄ ≡ f →
                      (L = ⋆ ∧ 𝐈⦃f⦄) ∨
                      ∃∃I,K,V,g. K ⊢ 𝐅*⦃#i⦄ ≡ g & L = K.ⓑ{I}V & f = ↑g.
/2 width=3 by frees_inv_lref_aux/ qed-.

fact frees_inv_bind_aux: ∀L,X,f. L ⊢ 𝐅*⦃X⦄ ≡ f → ∀I,V,T,a. X = ⓑ{a,I}V.T →
                         ∃∃f1,f2. L ⊢ 𝐅*⦃V⦄ ≡ f1 & L.ⓑ{I}V ⊢ 𝐅*⦃T⦄ ≡ f2 & f1 ⋓ ⫱f2 ≡ f.
#L #X #f * -L -X -f
[ #I #f #_ #J #W #U #b #H destruct
| #I #L #V #s #f #_ #J #W #U #b #H destruct
| #I #L #V #f #_ #J #W #U #b #H destruct
| #I #L #V #i #f #_ #J #W #U #b #H destruct
| #I #L #V #l #f #_ #J #W #U #b #H destruct
| #I #L #V #T #p #f1 #f2 #f #HV #HT #Hf #J #W #U #b #H destruct /2 width=5 by ex3_2_intro/
| #I #L #V #T #f1 #f2 #f #_ #_ #_ #J #W #U #b #H destruct
]
qed-.

lemma frees_inv_bind: ∀I,L,V,T,a,f. L ⊢ 𝐅*⦃ⓑ{a,I}V.T⦄ ≡ f →
                      ∃∃f1,f2. L ⊢ 𝐅*⦃V⦄ ≡ f1 & L.ⓑ{I}V ⊢ 𝐅*⦃T⦄ ≡ f2 & f1 ⋓ ⫱f2 ≡ f.
/2 width=4 by frees_inv_bind_aux/ qed-.

fact frees_inv_flat_aux: ∀L,X,f. L ⊢ 𝐅*⦃X⦄ ≡ f → ∀I,V,T. X = ⓕ{I}V.T →
                         ∃∃f1,f2. L ⊢ 𝐅*⦃V⦄ ≡ f1 & L ⊢ 𝐅*⦃T⦄ ≡ f2 & f1 ⋓ f2 ≡ f.
#L #X #f * -L -X -f
[ #I #f #_ #J #W #U #H destruct
| #I #L #V #s #f #_ #J #W #U #H destruct
| #I #L #V #f #_ #J #W #U #H destruct
| #I #L #V #i #f #_ #J #W #U #H destruct
| #I #L #V #l #f #_ #J #W #U #H destruct
| #I #L #V #T #p #f1 #f2 #f #_ #_ #_ #J #W #U #H destruct
| #I #L #V #T #f1 #f2 #f #HV #HT #Hf #J #W #U #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma frees_inv_flat: ∀I,L,V,T,f. L ⊢ 𝐅*⦃ⓕ{I}V.T⦄ ≡ f →
                      ∃∃f1,f2. L ⊢ 𝐅*⦃V⦄ ≡ f1 & L ⊢ 𝐅*⦃T⦄ ≡ f2 & f1 ⋓ f2 ≡ f.
/2 width=4 by frees_inv_flat_aux/ qed-.

(* Basic forward lemmas ****************************************************)

lemma frees_fwd_isfin: ∀L,T,f. L ⊢ 𝐅*⦃T⦄ ≡ f → 𝐅⦃f⦄.
#L #T #f #H elim H -L -T -f
/3 width=5 by sor_isfin, isfin_isid, isfin_tl, isfin_push, isfin_next/
qed-.

(* Basic properties ********************************************************)

lemma frees_eq_repl_back: ∀L,T. eq_repl_back … (λf. L ⊢ 𝐅*⦃T⦄ ≡ f).
#L #T #f1 #H elim H -L -T -f1
[ /3 width=3 by frees_atom, isid_eq_repl_back/
| #I #L #V #s #f1 #_ #IH #f2 #Hf12
  elim (eq_inv_px … Hf12) -Hf12 /3 width=3 by frees_sort/
| #I #L #V #f1 #_ #IH #f2 #Hf12
  elim (eq_inv_nx … Hf12) -Hf12 /3 width=3 by frees_zero/
| #I #L #V #i #f1 #_ #IH #f2 #Hf12
  elim (eq_inv_px … Hf12) -Hf12 /3 width=3 by frees_lref/
| #I #L #V #l #f1 #_ #IH #f2 #Hf12
  elim (eq_inv_px … Hf12) -Hf12 /3 width=3 by frees_gref/
| /3 width=7 by frees_bind, sor_eq_repl_back3/
| /3 width=7 by frees_flat, sor_eq_repl_back3/
]
qed-.

lemma frees_eq_repl_fwd: ∀L,T. eq_repl_fwd … (λf. L ⊢ 𝐅*⦃T⦄ ≡ f).
#L #T @eq_repl_sym /2 width=3 by frees_eq_repl_back/
qed-.

lemma frees_sort_gen: ∀L,s,f. 𝐈⦃f⦄ → L ⊢ 𝐅*⦃⋆s⦄ ≡ f.
#L elim L -L
/4 width=3 by frees_eq_repl_back, frees_sort, frees_atom, eq_push_inv_isid/
qed.

lemma frees_gref_gen: ∀L,p,f. 𝐈⦃f⦄ → L ⊢ 𝐅*⦃§p⦄ ≡ f.
#L elim L -L
/4 width=3 by frees_eq_repl_back, frees_gref, frees_atom, eq_push_inv_isid/
qed.

(* Basic_2A1: removed theorems 27:
              frees_eq frees_be frees_inv
              frees_inv_sort frees_inv_gref frees_inv_lref frees_inv_lref_free
              frees_inv_lref_skip frees_inv_lref_ge frees_inv_lref_lt
              frees_inv_bind frees_inv_flat frees_inv_bind_O
              frees_lref_eq frees_lref_be frees_weak
              frees_bind_sn frees_bind_dx frees_flat_sn frees_flat_dx
              lreq_frees_trans frees_lreq_conf
              llor_atom llor_skip llor_total
              llor_tail_frees llor_tail_cofrees
*)
