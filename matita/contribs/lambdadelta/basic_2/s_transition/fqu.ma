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

include "basic_2/notation/relations/supterm_6.ma".
include "basic_2/grammar/lenv.ma".
include "basic_2/grammar/genv.ma".
include "basic_2/relocation/lifts.ma".

(* SUPCLOSURE ***************************************************************)

(* activate genv *)
(* Note: frees_total requires fqu_drop for all atoms *)
inductive fqu: tri_relation genv lenv term ≝
| fqu_lref_O : ∀I,G,L,V. fqu G (L.ⓑ{I}V) (#0) G L V
| fqu_pair_sn: ∀I,G,L,V,T. fqu G L (②{I}V.T) G L V
| fqu_bind_dx: ∀p,I,G,L,V,T. fqu G L (ⓑ{p,I}V.T) G (L.ⓑ{I}V) T
| fqu_flat_dx: ∀I,G,L,V,T. fqu G L (ⓕ{I}V.T) G L T
| fqu_drop   : ∀I,I1,I2,G,L,V. ⬆*[1] ⓪{I2} ≡ ⓪{I1} →
               fqu G (L.ⓑ{I}V) (⓪{I1}) G L (⓪{I2})
.

interpretation
   "structural successor (closure)"
   'SupTerm G1 L1 T1 G2 L2 T2 = (fqu G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fqu_lref_S: ∀I,G,L,V,i. ⦃G, L.ⓑ{I}V, #(⫯i)⦄ ⊐ ⦃G, L, #(i)⦄.
/2 width=1 by fqu_drop/ qed.

(* Basic inversion lemmas ***************************************************)

fact fqu_inv_atom1_aux: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                        ∀I. L1 = ⋆ → T1 = ⓪{I} → ⊥.
#G1 #G2 #L1 #L2 #T1 #T2 * -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #T #J #H destruct
| #I #G #L #V #T #J #_ #H destruct
| #p #I #G #L #V #T #J #_ #H destruct
| #I #G #L #V #T #J  #_ #H destruct
| #I #I1 #I2 #G #L #V #_ #J #H destruct
]
qed-.

lemma fqu_inv_atom1: ∀I,G1,G2,L2,T2. ⦃G1, ⋆, ⓪{I}⦄ ⊐ ⦃G2, L2, T2⦄ → ⊥.
/2 width=10 by fqu_inv_atom1_aux/ qed-.

fact fqu_inv_sort1_aux: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                        ∀I,K,V,s. L1 = K.ⓑ{I}V → T1 = ⋆s →
                        ∧∧ G1 = G2 & L2 = K & T2 = ⋆s.
#G1 #G2 #L1 #L2 #T1 #T2 * -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #T #J #K #W #s #_ #H destruct
| #I #G #L #V #T #J #K #W #s #_ #H destruct
| #p #I #G #L #V #T #J #K #W #s #_ #H destruct
| #I #G #L #V #T #J #K #W #s #_ #H destruct
| #I #I1 #I2 #G #L #V #HI12 #J #K #W #s #H1 #H2 destruct
  lapply (lifts_inv_sort2 … HI12) -HI12 /2 width=1 by and3_intro/
]
qed-.

lemma fqu_inv_sort1: ∀I,G1,G2,K,L2,V,T2,s. ⦃G1, K.ⓑ{I}V, ⋆s⦄ ⊐ ⦃G2, L2, T2⦄ →
                     ∧∧ G1 = G2 & L2 = K & T2 = ⋆s.
/2 width=7 by fqu_inv_sort1_aux/ qed-.

fact fqu_inv_zero1_aux: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                        ∀I,K,V. L1 = K.ⓑ{I}V → T1 = #0 →
                        ∧∧ G1 = G2 & L2 = K & T2 = V.
#G1 #G2 #L1 #L2 #T1 #T2 * -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #T #J #K #W #H1 #H2 destruct /2 width=1 by and3_intro/
| #I #G #L #V #T #J #K #W #_ #H destruct
| #p #I #G #L #V #T #J #K #W #_ #H destruct
| #I #G #L #V #T #J #K #W #_ #H destruct
| #I #I1 #I2 #G #L #V #HI12 #J #K #W #H1 #H2 destruct
  elim (lifts_inv_lref2_uni_lt … HI12) -HI12 //
]
qed-.

lemma fqu_inv_zero1: ∀I,G1,G2,K,L2,V,T2. ⦃G1, K.ⓑ{I}V, #0⦄ ⊐ ⦃G2, L2, T2⦄ →
                     ∧∧ G1 = G2 & L2 = K & T2 = V.
/2 width=9 by fqu_inv_zero1_aux/ qed-.

fact fqu_inv_lref1_aux: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                        ∀I,K,V,i. L1 = K.ⓑ{I}V → T1 = #(⫯i) →
                        ∧∧ G1 = G2 & L2 = K & T2 = #i.
#G1 #G2 #L1 #L2 #T1 #T2 * -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #T #J #K #W #i #_ #H destruct
| #I #G #L #V #T #J #K #W #i #_ #H destruct
| #p #I #G #L #V #T #J #K #W #i #_ #H destruct
| #I #G #L #V #T #J #K #W #i #_ #H destruct
| #I #I1 #I2 #G #L #V #HI12 #J #K #W #i #H1 #H2 destruct
  lapply (lifts_inv_lref2_uni_ge … HI12) -HI12 /2 width=1 by and3_intro/
]
qed-.

lemma fqu_inv_lref1: ∀I,G1,G2,K,L2,V,T2,i. ⦃G1, K.ⓑ{I}V, #(⫯i)⦄ ⊐ ⦃G2, L2, T2⦄ →
                     ∧∧ G1 = G2 & L2 = K & T2 = #i.
/2 width=9 by fqu_inv_lref1_aux/ qed-.

fact fqu_inv_gref1_aux: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                        ∀I,K,V,l. L1 = K.ⓑ{I}V → T1 = §l →
                        ∧∧ G1 = G2 & L2 = K & T2 = §l.
#G1 #G2 #L1 #L2 #T1 #T2 * -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #T #J #K #W #l #_ #H destruct
| #I #G #L #V #T #J #K #W #l #_ #H destruct
| #p #I #G #L #V #T #J #K #W #l #_ #H destruct
| #I #G #L #V #T #J #K #W #l #_ #H destruct
| #I #I1 #I2 #G #L #V #HI12 #J #K #W #l #H1 #H2 destruct
  lapply (lifts_inv_gref2 … HI12) -HI12 /2 width=1 by and3_intro/
]
qed-.

lemma fqu_inv_gref1: ∀I,G1,G2,K,L2,V,T2,l. ⦃G1, K.ⓑ{I}V, §l⦄ ⊐ ⦃G2, L2, T2⦄ →
                     ∧∧ G1 = G2 & L2 = K & T2 = §l.
/2 width=7 by fqu_inv_gref1_aux/ qed-.

fact fqu_inv_bind1_aux: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                        ∀p,I,V1,U1. T1 = ⓑ{p,I}V1.U1 →
                        (∧∧ G1 = G2 & L1 = L2 & V1 = T2) ∨
                        (∧∧ G1 = G2 & L1.ⓑ{I}V1 = L2 & U1 = T2).
#G1 #G2 #L1 #L2 #T1 #T2 * -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #T #q #J #W #U #H destruct
| #I #G #L #V #T #q #J #W #U #H destruct /3 width=1 by and3_intro, or_introl/
| #p #I #G #L #V #T #q #J #W #U #H destruct /3 width=1 by and3_intro, or_intror/
| #I #G #L #V #T #q #J #W #U #H destruct
| #I #I1 #I2 #G #L #V #_ #q #J #W #U #H destruct
]
qed-.

lemma fqu_inv_bind1: ∀p,I,G1,G2,L1,L2,V1,U1,T2. ⦃G1, L1, ⓑ{p,I}V1.U1⦄ ⊐ ⦃G2, L2, T2⦄ →
                     (∧∧ G1 = G2 & L1 = L2 & V1 = T2) ∨
                     (∧∧ G1 = G2 & L1.ⓑ{I}V1 = L2 & U1 = T2).
/2 width=4 by fqu_inv_bind1_aux/ qed-.

fact fqu_inv_flat1_aux: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                        ∀I,V1,U1. T1 = ⓕ{I}V1.U1 →
                        (∧∧ G1 = G2 & L1 = L2 & V1 = T2) ∨
                        (∧∧ G1 = G2 & L1 = L2 & U1 = T2).
#G1 #G2 #L1 #L2 #T1 #T2 * -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #T #J #W #U #H destruct
| #I #G #L #V #T #J #W #U #H destruct /3 width=1 by and3_intro, or_introl/
| #p #I #G #L #V #T #J #W #U #H destruct
| #I #G #L #V #T #J #W #U #H destruct /3 width=1 by and3_intro, or_intror/
| #I #I1 #I2 #G #L #V #_ #J #W #U #H destruct
]
qed-.

lemma fqu_inv_flat1: ∀I,G1,G2,L1,L2,V1,U1,T2. ⦃G1, L1, ⓕ{I}V1.U1⦄ ⊐ ⦃G2, L2, T2⦄ →
                     (∧∧ G1 = G2 & L1 = L2 & V1 = T2) ∨
                     (∧∧ G1 = G2 & L1 = L2 & U1 = T2).
/2 width=4 by fqu_inv_flat1_aux/ qed-.

(* Basic_2A1: removed theorems 3:
              fqu_drop fqu_drop_lt fqu_lref_S_lt
*)
