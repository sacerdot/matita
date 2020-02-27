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

include "ground/relocation/rtmap_sor.ma".
include "static_2/notation/relations/freeplus_3.ma".
include "static_2/syntax/lenv.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

inductive frees: relation3 lenv term rtmap ≝
| frees_sort: ∀f,L,s. 𝐈❪f❫ → frees L (⋆s) f
| frees_atom: ∀f,i. 𝐈❪f❫ → frees (⋆) (#i) (⫯*[i]↑f)
| frees_pair: ∀f,I,L,V. frees L V f →
              frees (L.ⓑ[I]V) (#0) (↑f)
| frees_unit: ∀f,I,L. 𝐈❪f❫ → frees (L.ⓤ[I]) (#0) (↑f)
| frees_lref: ∀f,I,L,i. frees L (#i) f →
              frees (L.ⓘ[I]) (#↑i) (⫯f)
| frees_gref: ∀f,L,l. 𝐈❪f❫ → frees L (§l) f
| frees_bind: ∀f1,f2,f,p,I,L,V,T. frees L V f1 → frees (L.ⓑ[I]V) T f2 →
              f1 ⋓ ⫱f2 ≘ f → frees L (ⓑ[p,I]V.T) f
| frees_flat: ∀f1,f2,f,I,L,V,T. frees L V f1 → frees L T f2 →
              f1 ⋓ f2 ≘ f → frees L (ⓕ[I]V.T) f
.

interpretation
   "context-sensitive free variables (term)"
   'FreePlus L T f = (frees L T f).

(* Basic inversion lemmas ***************************************************)

fact frees_inv_sort_aux: ∀f,L,X. L ⊢ 𝐅+❪X❫ ≘ f → ∀x. X = ⋆x → 𝐈❪f❫.
#L #X #f #H elim H -f -L -X //
[ #f #i #_ #x #H destruct
| #f #_ #L #V #_ #_ #x #H destruct
| #f #_ #L #_ #x #H destruct
| #f #_ #L #i #_ #_ #x #H destruct
| #f1 #f2 #f #p #I #L #V #T #_ #_ #_ #_ #_ #x #H destruct
| #f1 #f2 #f #I #L #V #T #_ #_ #_ #_ #_ #x #H destruct
]
qed-.

lemma frees_inv_sort: ∀f,L,s. L ⊢ 𝐅+❪⋆s❫ ≘ f → 𝐈❪f❫.
/2 width=5 by frees_inv_sort_aux/ qed-.

fact frees_inv_atom_aux:
     ∀f,L,X. L ⊢ 𝐅+❪X❫ ≘ f → ∀i. L = ⋆ → X = #i →
     ∃∃g. 𝐈❪g❫ & f = ⫯*[i]↑g.
#f #L #X #H elim H -f -L -X
[ #f #L #s #_ #j #_ #H destruct
| #f #i #Hf #j #_ #H destruct /2 width=3 by ex2_intro/
| #f #I #L #V #_ #_ #j #H destruct
| #f #I #L #_ #j #H destruct
| #f #I #L #i #_ #_ #j #H destruct
| #f #L #l #_ #j #_ #H destruct
| #f1 #f2 #f #p #I #L #V #T #_ #_ #_ #_ #_ #j #_ #H destruct
| #f1 #f2 #f #I #L #V #T #_ #_ #_ #_ #_ #j #_ #H destruct
]
qed-.

lemma frees_inv_atom: ∀f,i. ⋆ ⊢ 𝐅+❪#i❫ ≘ f → ∃∃g. 𝐈❪g❫ & f = ⫯*[i]↑g.
/2 width=5 by frees_inv_atom_aux/ qed-.

fact frees_inv_pair_aux:
     ∀f,L,X. L ⊢ 𝐅+❪X❫ ≘ f → ∀I,K,V. L = K.ⓑ[I]V → X = #0 →
     ∃∃g. K ⊢ 𝐅+❪V❫ ≘ g & f = ↑g.
#f #L #X * -f -L -X
[ #f #L #s #_ #Z #Y #X #_ #H destruct
| #f #i #_ #Z #Y #X #H destruct
| #f #I #L #V #Hf #Z #Y #X #H #_ destruct /2 width=3 by ex2_intro/
| #f #I #L #_ #Z #Y #X #H destruct
| #f #I #L #i #_ #Z #Y #X #_ #H destruct
| #f #L #l #_ #Z #Y #X #_ #H destruct
| #f1 #f2 #f #p #I #L #V #T #_ #_ #_ #Z #Y #X #_ #H destruct
| #f1 #f2 #f #I #L #V #T #_ #_ #_ #Z #Y #X #_ #H destruct
]
qed-.

lemma frees_inv_pair: ∀f,I,K,V. K.ⓑ[I]V ⊢ 𝐅+❪#0❫ ≘ f → ∃∃g. K ⊢ 𝐅+❪V❫ ≘ g & f = ↑g.
/2 width=6 by frees_inv_pair_aux/ qed-.

fact frees_inv_unit_aux:
     ∀f,L,X. L ⊢ 𝐅+❪X❫ ≘ f → ∀I,K. L = K.ⓤ[I] → X = #0 →
     ∃∃g. 𝐈❪g❫ & f = ↑g.
#f #L #X * -f -L -X
[ #f #L #s #_ #Z #Y #_ #H destruct
| #f #i #_ #Z #Y #H destruct
| #f #I #L #V #_ #Z #Y #H destruct
| #f #I #L #Hf #Z #Y #H destruct /2 width=3 by ex2_intro/
| #f #I #L #i #_ #Z #Y #_ #H destruct
| #f #L #l #_ #Z #Y #_ #H destruct
| #f1 #f2 #f #p #I #L #V #T #_ #_ #_ #Z #Y #_ #H destruct
| #f1 #f2 #f #I #L #V #T #_ #_ #_ #Z #Y #_ #H destruct
]
qed-.

lemma frees_inv_unit: ∀f,I,K. K.ⓤ[I] ⊢ 𝐅+❪#0❫ ≘ f → ∃∃g. 𝐈❪g❫ & f = ↑g.
/2 width=7 by frees_inv_unit_aux/ qed-.

fact frees_inv_lref_aux:
     ∀f,L,X. L ⊢ 𝐅+❪X❫ ≘ f → ∀I,K,j. L = K.ⓘ[I] → X = #(↑j) →
     ∃∃g. K ⊢ 𝐅+❪#j❫ ≘ g & f = ⫯g.
#f #L #X * -f -L -X
[ #f #L #s #_ #Z #Y #j #_ #H destruct
| #f #i #_ #Z #Y #j #H destruct
| #f #I #L #V #_ #Z #Y #j #_ #H destruct
| #f #I #L #_ #Z #Y #j #_ #H destruct
| #f #I #L #i #Hf #Z #Y #j #H1 #H2 destruct /2 width=3 by ex2_intro/
| #f #L #l #_ #Z #Y #j #_ #H destruct
| #f1 #f2 #f #p #I #L #V #T #_ #_ #_ #Z #Y #j #_ #H destruct
| #f1 #f2 #f #I #L #V #T #_ #_ #_ #Z #Y #j #_ #H destruct
]
qed-.

lemma frees_inv_lref:
      ∀f,I,K,i. K.ⓘ[I] ⊢ 𝐅+❪#(↑i)❫ ≘ f →
      ∃∃g. K ⊢ 𝐅+❪#i❫ ≘ g & f = ⫯g.
/2 width=6 by frees_inv_lref_aux/ qed-.

fact frees_inv_gref_aux: ∀f,L,X. L ⊢ 𝐅+❪X❫ ≘ f → ∀x. X = §x → 𝐈❪f❫.
#f #L #X #H elim H -f -L -X //
[ #f #i #_ #x #H destruct
| #f #_ #L #V #_ #_ #x #H destruct
| #f #_ #L #_ #x #H destruct
| #f #_ #L #i #_ #_ #x #H destruct
| #f1 #f2 #f #p #I #L #V #T #_ #_ #_ #_ #_ #x #H destruct
| #f1 #f2 #f #I #L #V #T #_ #_ #_ #_ #_ #x #H destruct
]
qed-.

lemma frees_inv_gref: ∀f,L,l. L ⊢ 𝐅+❪§l❫ ≘ f → 𝐈❪f❫.
/2 width=5 by frees_inv_gref_aux/ qed-.

fact frees_inv_bind_aux:
     ∀f,L,X. L ⊢ 𝐅+❪X❫ ≘ f → ∀p,I,V,T. X = ⓑ[p,I]V.T →
     ∃∃f1,f2. L ⊢ 𝐅+❪V❫ ≘ f1 & L.ⓑ[I]V ⊢ 𝐅+❪T❫ ≘ f2 & f1 ⋓ ⫱f2 ≘ f.
#f #L #X * -f -L -X
[ #f #L #s #_ #q #J #W #U #H destruct
| #f #i #_ #q #J #W #U #H destruct
| #f #I #L #V #_ #q #J #W #U #H destruct
| #f #I #L #_ #q #J #W #U #H destruct
| #f #I #L #i #_ #q #J #W #U #H destruct
| #f #L #l #_ #q #J #W #U #H destruct
| #f1 #f2 #f #p #I #L #V #T #HV #HT #Hf #q #J #W #U #H destruct /2 width=5 by ex3_2_intro/
| #f1 #f2 #f #I #L #V #T #_ #_ #_ #q #J #W #U #H destruct
]
qed-.

lemma frees_inv_bind:
      ∀f,p,I,L,V,T. L ⊢ 𝐅+❪ⓑ[p,I]V.T❫ ≘ f →
      ∃∃f1,f2. L ⊢ 𝐅+❪V❫ ≘ f1 & L.ⓑ[I]V ⊢ 𝐅+❪T❫ ≘ f2 & f1 ⋓ ⫱f2 ≘ f.
/2 width=4 by frees_inv_bind_aux/ qed-.

fact frees_inv_flat_aux: ∀f,L,X. L ⊢ 𝐅+❪X❫ ≘ f → ∀I,V,T. X = ⓕ[I]V.T →
                         ∃∃f1,f2. L ⊢ 𝐅+❪V❫ ≘ f1 & L ⊢ 𝐅+❪T❫ ≘ f2 & f1 ⋓ f2 ≘ f.
#f #L #X * -f -L -X
[ #f #L #s #_ #J #W #U #H destruct
| #f #i #_ #J #W #U #H destruct
| #f #I #L #V #_ #J #W #U #H destruct
| #f #I #L #_ #J #W #U #H destruct
| #f #I #L #i #_ #J #W #U #H destruct
| #f #L #l #_ #J #W #U #H destruct
| #f1 #f2 #f #p #I #L #V #T #_ #_ #_ #J #W #U #H destruct
| #f1 #f2 #f #I #L #V #T #HV #HT #Hf #J #W #U #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma frees_inv_flat:
      ∀f,I,L,V,T. L ⊢ 𝐅+❪ⓕ[I]V.T❫ ≘ f →
      ∃∃f1,f2. L ⊢ 𝐅+❪V❫ ≘ f1 & L ⊢ 𝐅+❪T❫ ≘ f2 & f1 ⋓ f2 ≘ f.
/2 width=4 by frees_inv_flat_aux/ qed-.

(* Basic properties ********************************************************)

lemma frees_eq_repl_back: ∀L,T. eq_repl_back … (λf. L ⊢ 𝐅+❪T❫ ≘ f).
#L #T #f1 #H elim H -f1 -L -T
[ /3 width=3 by frees_sort, isid_eq_repl_back/
| #f1 #i #Hf1 #g2 #H
  elim (eq_inv_pushs_sn … H) -H #g #Hg #H destruct
  elim (eq_inv_nx … Hg) -Hg
  /3 width=3 by frees_atom, isid_eq_repl_back/
| #f1 #I #L #V #_ #IH #g2 #H
  elim (eq_inv_nx … H) -H
  /3 width=3 by frees_pair/
| #f1 #I #L #Hf1 #g2 #H
  elim (eq_inv_nx … H) -H
  /3 width=3 by frees_unit, isid_eq_repl_back/
| #f1 #I #L #i #_ #IH #g2 #H
  elim (eq_inv_px … H) -H /3 width=3 by frees_lref/
| /3 width=3 by frees_gref, isid_eq_repl_back/
| /3 width=7 by frees_bind, sor_eq_repl_back3/
| /3 width=7 by frees_flat, sor_eq_repl_back3/
]
qed-.

lemma frees_eq_repl_fwd: ∀L,T. eq_repl_fwd … (λf. L ⊢ 𝐅+❪T❫ ≘ f).
#L #T @eq_repl_sym /2 width=3 by frees_eq_repl_back/
qed-.

lemma frees_lref_push: ∀f,i. ⋆ ⊢ 𝐅+❪#i❫ ≘ f → ⋆ ⊢ 𝐅+❪#↑i❫ ≘ ⫯f.
#f #i #H
elim (frees_inv_atom … H) -H #g #Hg #H destruct
/2 width=1 by frees_atom/
qed.

(* Forward lemmas with test for finite colength *****************************)

lemma frees_fwd_isfin: ∀f,L,T. L ⊢ 𝐅+❪T❫ ≘ f → 𝐅❪f❫.
#f #L #T #H elim H -f -L -T
/4 width=5 by sor_isfin, isfin_isid, isfin_tl, isfin_pushs, isfin_push, isfin_next/
qed-.

(* Basic_2A1: removed theorems 30:
              frees_eq frees_be frees_inv
              frees_inv_sort frees_inv_gref frees_inv_lref frees_inv_lref_free
              frees_inv_lref_skip frees_inv_lref_ge frees_inv_lref_lt
              frees_inv_bind frees_inv_flat frees_inv_bind_O
              frees_lref_eq frees_lref_be frees_weak
              frees_bind_sn frees_bind_dx frees_flat_sn frees_flat_dx
              frees_lift_ge frees_inv_lift_be frees_inv_lift_ge
              lreq_frees_trans frees_lreq_conf
              llor_atom llor_skip llor_total
              llor_tail_frees llor_tail_cofrees
*)
