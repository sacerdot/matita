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

include "ground_2/xoa/and_4.ma".
include "ground_2/xoa/ex_4_2.ma".
include "ground_2/xoa/or_4.ma".
include "static_2/notation/relations/supterm_6.ma".
include "static_2/notation/relations/supterm_7.ma".
include "static_2/syntax/lenv.ma".
include "static_2/syntax/genv.ma".
include "static_2/relocation/lifts.ma".

(* SUPCLOSURE ***************************************************************)

(* activate genv *)
(* Note: frees_total requires fqu_drop for all atoms
         fqu_cpx_trans requires fqu_drop for all terms
         frees_fqus_drops requires fqu_drop restricted on atoms
*)
inductive fqu (b:bool): tri_relation genv lenv term ≝
| fqu_lref_O : ∀I,G,L,V. fqu b G (L.ⓑ{I}V) (#0) G L V
| fqu_pair_sn: ∀I,G,L,V,T. fqu b G L (②{I}V.T) G L V
| fqu_bind_dx: ∀p,I,G,L,V,T. b = Ⓣ → fqu b G L (ⓑ{p,I}V.T) G (L.ⓑ{I}V) T
| fqu_clear  : ∀p,I,G,L,V,T. b = Ⓕ → fqu b G L (ⓑ{p,I}V.T) G (L.ⓧ) T
| fqu_flat_dx: ∀I,G,L,V,T. fqu b G L (ⓕ{I}V.T) G L T
| fqu_drop   : ∀I,G,L,T,U. ⇧*[1] T ≘ U → fqu b G (L.ⓘ{I}) U G L T
.

interpretation
   "extended structural successor (closure)"
   'SupTerm b G1 L1 T1 G2 L2 T2 = (fqu b G1 L1 T1 G2 L2 T2).

interpretation
   "structural successor (closure)"
   'SupTerm G1 L1 T1 G2 L2 T2 = (fqu true G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fqu_sort: ∀b,I,G,L,s. ⦃G,L.ⓘ{I},⋆s⦄ ⬂[b] ⦃G,L,⋆s⦄.
/2 width=1 by fqu_drop/ qed.

lemma fqu_lref_S: ∀b,I,G,L,i. ⦃G,L.ⓘ{I},#↑i⦄ ⬂[b] ⦃G,L,#i⦄.
/2 width=1 by fqu_drop/ qed.

lemma fqu_gref: ∀b,I,G,L,l. ⦃G,L.ⓘ{I},§l⦄ ⬂[b] ⦃G,L,§l⦄.
/2 width=1 by fqu_drop/ qed.

(* Basic inversion lemmas ***************************************************)

fact fqu_inv_sort1_aux: ∀b,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                        ∀s. T1 = ⋆s →
                        ∃∃J. G1 = G2 & L1 = L2.ⓘ{J} & T2 = ⋆s.
#b #G1 #G2 #L1 #L2 #T1 #T2 * -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #T #s #H destruct
| #I #G #L #V #T #s #H destruct
| #p #I #G #L #V #T #_ #s #H destruct
| #p #I #G #L #V #T #_ #s #H destruct
| #I #G #L #V #T #s #H destruct
| #I #G #L #T #U #HI12 #s #H destruct
  lapply (lifts_inv_sort2 … HI12) -HI12 /2 width=2 by ex3_intro/
]
qed-.

lemma fqu_inv_sort1: ∀b,G1,G2,L1,L2,T2,s. ⦃G1,L1,⋆s⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                     ∃∃J. G1 = G2 & L1 = L2.ⓘ{J} & T2 = ⋆s.
/2 width=4 by fqu_inv_sort1_aux/ qed-.

fact fqu_inv_lref1_aux: ∀b,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                        ∀i. T1 = #i →
                        (∃∃J,V. G1 = G2 & L1 = L2.ⓑ{J}V & T2 = V & i = 0) ∨
                        ∃∃J,j. G1 = G2 & L1 = L2.ⓘ{J} & T2 = #j & i = ↑j.
#b #G1 #G2 #L1 #L2 #T1 #T2 * -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #T #i #H destruct /3 width=4 by ex4_2_intro, or_introl/
| #I #G #L #V #T #i #H destruct
| #p #I #G #L #V #T #_ #i #H destruct
| #p #I #G #L #V #T #_ #i #H destruct
| #I #G #L #V #T #i #H destruct
| #I #G #L #T #U #HI12 #i #H destruct
  elim (lifts_inv_lref2_uni … HI12) -HI12 /3 width=3 by ex4_2_intro, or_intror/
]
qed-.

lemma fqu_inv_lref1: ∀b,G1,G2,L1,L2,T2,i. ⦃G1,L1,#i⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                     (∃∃J,V. G1 = G2 & L1 = L2.ⓑ{J}V & T2 = V & i = 0) ∨
                     ∃∃J,j. G1 = G2 & L1 = L2.ⓘ{J} & T2 = #j & i = ↑j.
/2 width=4 by fqu_inv_lref1_aux/ qed-.

fact fqu_inv_gref1_aux: ∀b,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                        ∀l. T1 = §l →
                        ∃∃J. G1 = G2 & L1 = L2.ⓘ{J} & T2 = §l.
#b #G1 #G2 #L1 #L2 #T1 #T2 * -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #T #l #H destruct
| #I #G #L #V #T #l #H destruct
| #p #I #G #L #V #T #_ #l #H destruct
| #p #I #G #L #V #T #_ #l #H destruct
| #I #G #L #V #T #s #H destruct
| #I #G #L #T #U #HI12 #l #H destruct
  lapply (lifts_inv_gref2 … HI12) -HI12 /2 width=3 by ex3_intro/
]
qed-.

lemma fqu_inv_gref1: ∀b,G1,G2,L1,L2,T2,l. ⦃G1,L1,§l⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                     ∃∃J. G1 = G2 & L1 = L2.ⓘ{J} & T2 = §l.
/2 width=4 by fqu_inv_gref1_aux/ qed-.

fact fqu_inv_bind1_aux: ∀b,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                        ∀p,I,V1,U1. T1 = ⓑ{p,I}V1.U1 →
                        ∨∨ ∧∧ G1 = G2 & L1 = L2 & V1 = T2
                         | ∧∧ G1 = G2 & L1.ⓑ{I}V1 = L2 & U1 = T2 & b = Ⓣ
                         | ∧∧ G1 = G2 & L1.ⓧ = L2 & U1 = T2 & b = Ⓕ
                         | ∃∃J. G1 = G2 & L1 = L2.ⓘ{J} & ⇧*[1] T2 ≘ ⓑ{p,I}V1.U1.
#b #G1 #G2 #L1 #L2 #T1 #T2 * -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #T #q #J #V0 #U0 #H destruct
| #I #G #L #V #T #q #J #V0 #U0 #H destruct /3 width=1 by and3_intro, or4_intro0/
| #p #I #G #L #V #T #Hb #q #J #V0 #U0 #H destruct /3 width=1 by and4_intro, or4_intro1/
| #p #I #G #L #V #T #Hb #q #J #V0 #U0 #H destruct /3 width=1 by and4_intro, or4_intro2/
| #I #G #L #V #T #q #J #V0 #U0 #H destruct
| #I #G #L #T #U #HTU #q #J #V0 #U0 #H destruct /3 width=2 by or4_intro3, ex3_intro/
]
qed-.

lemma fqu_inv_bind1: ∀b,p,I,G1,G2,L1,L2,V1,U1,T2. ⦃G1,L1,ⓑ{p,I}V1.U1⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                     ∨∨ ∧∧ G1 = G2 & L1 = L2 & V1 = T2
                      | ∧∧ G1 = G2 & L1.ⓑ{I}V1 = L2 & U1 = T2 & b = Ⓣ
                      | ∧∧ G1 = G2 & L1.ⓧ = L2 & U1 = T2 & b = Ⓕ
                      | ∃∃J. G1 = G2 & L1 = L2.ⓘ{J} & ⇧*[1] T2 ≘ ⓑ{p,I}V1.U1.
/2 width=4 by fqu_inv_bind1_aux/ qed-.

lemma fqu_inv_bind1_true: ∀p,I,G1,G2,L1,L2,V1,U1,T2. ⦃G1,L1,ⓑ{p,I}V1.U1⦄ ⬂ ⦃G2,L2,T2⦄ →
                          ∨∨ ∧∧ G1 = G2 & L1 = L2 & V1 = T2
                           | ∧∧ G1 = G2 & L1.ⓑ{I}V1 = L2 & U1 = T2
                           | ∃∃J. G1 = G2 & L1 = L2.ⓘ{J} & ⇧*[1] T2 ≘ ⓑ{p,I}V1.U1.
#p #I #G1 #G2 #L1 #L2 #V1 #U1 #T2 #H elim (fqu_inv_bind1 … H) -H
/3 width=1 by or3_intro0, or3_intro2/
* #HG #HL #HU #H destruct
/3 width=1 by and3_intro, or3_intro1/
qed-.

fact fqu_inv_flat1_aux: ∀b,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                        ∀I,V1,U1. T1 = ⓕ{I}V1.U1 →
                        ∨∨ ∧∧ G1 = G2 & L1 = L2 & V1 = T2
                         | ∧∧ G1 = G2 & L1 = L2 & U1 = T2
                         | ∃∃J. G1 = G2 & L1 = L2.ⓘ{J} & ⇧*[1] T2 ≘ ⓕ{I}V1.U1.
#b #G1 #G2 #L1 #L2 #T1 #T2 * -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #T #J #V0 #U0 #H destruct
| #I #G #L #V #T #J #V0 #U0 #H destruct /3 width=1 by and3_intro, or3_intro0/
| #p #I #G #L #V #T #_ #J #V0 #U0 #H destruct
| #p #I #G #L #V #T #_ #J #V0 #U0 #H destruct
| #I #G #L #V #T #J #V0 #U0 #H destruct /3 width=1 by and3_intro, or3_intro1/
| #I #G #L #T #U #HTU #J #V0 #U0 #H destruct /3 width=2 by or3_intro2, ex3_intro/
]
qed-.

lemma fqu_inv_flat1: ∀b,I,G1,G2,L1,L2,V1,U1,T2. ⦃G1,L1,ⓕ{I}V1.U1⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                     ∨∨ ∧∧ G1 = G2 & L1 = L2 & V1 = T2
                      | ∧∧ G1 = G2 & L1 = L2 & U1 = T2
                      | ∃∃J. G1 = G2 & L1 = L2.ⓘ{J} & ⇧*[1] T2 ≘ ⓕ{I}V1.U1.
/2 width=4 by fqu_inv_flat1_aux/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma fqu_inv_atom1: ∀b,I,G1,G2,L2,T2. ⦃G1,⋆,⓪{I}⦄ ⬂[b] ⦃G2,L2,T2⦄ → ⊥.
#b * #x #G1 #G2 #L2 #T2 #H
[ elim (fqu_inv_sort1 … H) | elim (fqu_inv_lref1 … H) * | elim (fqu_inv_gref1 … H) ] -H
#I [2: #V |3: #i ] #_ #H destruct
qed-.

lemma fqu_inv_sort1_bind: ∀b,I,G1,G2,K,L2,T2,s. ⦃G1,K.ⓘ{I},⋆s⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                          ∧∧ G1 = G2 & L2 = K & T2 = ⋆s.
#b #I #G1 #G2 #K #L2 #T2 #s #H elim (fqu_inv_sort1 … H) -H
#Z #X #H1 #H2 destruct /2 width=1 by and3_intro/
qed-.

lemma fqu_inv_zero1_pair: ∀b,I,G1,G2,K,L2,V,T2. ⦃G1,K.ⓑ{I}V,#0⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                          ∧∧ G1 = G2 & L2 = K & T2 = V.
#b #I #G1 #G2 #K #L2 #V #T2 #H elim (fqu_inv_lref1 … H) -H *
#Z #X #H1 #H2 #H3 #H4 destruct /2 width=1 by and3_intro/
qed-.

lemma fqu_inv_lref1_bind: ∀b,I,G1,G2,K,L2,T2,i. ⦃G1,K.ⓘ{I},#(↑i)⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                          ∧∧ G1 = G2 & L2 = K & T2 = #i.
#b #I #G1 #G2 #K #L2 #T2 #i #H elim (fqu_inv_lref1 … H) -H *
#Z #X #H1 #H2 #H3 #H4 destruct /2 width=1 by and3_intro/
qed-.

lemma fqu_inv_gref1_bind: ∀b,I,G1,G2,K,L2,T2,l. ⦃G1,K.ⓘ{I},§l⦄ ⬂[b] ⦃G2,L2,T2⦄ →
                          ∧∧ G1 = G2 & L2 = K & T2 = §l.
#b #I #G1 #G2 #K #L2 #T2 #l #H elim (fqu_inv_gref1 … H) -H
#Z #H1 #H2 #H3 destruct /2 width=1 by and3_intro/
qed-.

(* Basic_2A1: removed theorems 3:
              fqu_drop fqu_drop_lt fqu_lref_S_lt
*)
