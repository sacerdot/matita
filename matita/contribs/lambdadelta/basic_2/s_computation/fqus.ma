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

include "ground_2/lib/star.ma".
include "basic_2/notation/relations/suptermstar_6.ma".
include "basic_2/notation/relations/suptermstar_7.ma".
include "basic_2/s_transition/fquq.ma".

(* STAR-ITERATED SUPCLOSURE *************************************************)

definition fqus: bool → tri_relation genv lenv term ≝
                 λb. tri_TC … (fquq b).

interpretation "extended star-iterated structural successor (closure)"
   'SupTermStar b G1 L1 T1 G2 L2 T2 = (fqus b G1 L1 T1 G2 L2 T2).

interpretation "star-iterated structural successor (closure)"
   'SupTermStar G1 L1 T1 G2 L2 T2 = (fqus true G1 L1 T1 G2 L2 T2).

(* Basic eliminators ********************************************************)

lemma fqus_ind: ∀b,G1,L1,T1. ∀R:relation3 …. R G1 L1 T1 →
                (∀G,G2,L,L2,T,T2. ⦃G1, L1, T1⦄ ⊐*[b] ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊐⸮[b] ⦃G2, L2, T2⦄ → R G L T → R G2 L2 T2) →
                ∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊐*[b] ⦃G2, L2, T2⦄ → R G2 L2 T2.
#b #G1 #L1 #T1 #R #IH1 #IH2 #G2 #L2 #T2 #H
@(tri_TC_star_ind … IH1 IH2 G2 L2 T2 H) //
qed-.

lemma fqus_ind_dx: ∀b,G2,L2,T2. ∀R:relation3 …. R G2 L2 T2 →
                   (∀G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ⊐⸮[b] ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊐*[b] ⦃G2, L2, T2⦄ → R G L T → R G1 L1 T1) →
                   ∀G1,L1,T1. ⦃G1, L1, T1⦄ ⊐*[b] ⦃G2, L2, T2⦄ → R G1 L1 T1.
#b #G2 #L2 #T2 #R #IH1 #IH2 #G1 #L1 #T1 #H
@(tri_TC_star_ind_dx … IH1 IH2 G1 L1 T1 H) //
qed-.

(* Basic properties *********************************************************)

lemma fqus_refl: ∀b. tri_reflexive … (fqus b).
/2 width=1 by tri_inj/ qed.

lemma fquq_fqus: ∀b,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮[b] ⦃G2, L2, T2⦄ →
                 ⦃G1, L1, T1⦄ ⊐*[b] ⦃G2, L2, T2⦄.
/2 width=1 by tri_inj/ qed.

lemma fqus_strap1: ∀b,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊐*[b] ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ ⊐⸮[b] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊐*[b] ⦃G2, L2, T2⦄.
/2 width=5 by tri_step/ qed-.

lemma fqus_strap2: ∀b,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊐⸮[b] ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ ⊐*[b] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊐*[b] ⦃G2, L2, T2⦄.
/2 width=5 by tri_TC_strap/ qed-.

(* Basic inversion lemmas ***************************************************)

lemma fqus_inv_fqu_sn: ∀b,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐*[b] ⦃G2, L2, T2⦄ →
                       (∧∧ G1 = G2 & L1 = L2 & T1 = T2) ∨
                       ∃∃G,L,T. ⦃G1, L1, T1⦄ ⊐[b] ⦃G, L, T⦄ & ⦃G, L, T⦄ ⊐*[b] ⦃G2, L2, T2⦄.
#b #G1 #G2 #L1 #L2 #T1 #T2 #H12 @(fqus_ind_dx … H12) -G1 -L1 -T1 /3 width=1 by and3_intro, or_introl/
#G1 #G #L1 #L #T1 #T * /3 width=5 by ex2_3_intro, or_intror/
* #HG #HL #HT #_ destruct //
qed-.

lemma fqus_inv_sort1: ∀b,G1,G2,L1,L2,T2,s. ⦃G1, L1, ⋆s⦄ ⊐*[b] ⦃G2, L2, T2⦄ →
                      (∧∧ G1 = G2 & L1 = L2 & ⋆s = T2) ∨
                      ∃∃J,L. ⦃G1, L, ⋆s⦄ ⊐*[b] ⦃G2, L2, T2⦄ & L1 = L.ⓘ{J}.
#b #G1 #G2 #L1 #L2 #T2 #s #H elim (fqus_inv_fqu_sn … H) -H * /3 width=1 by and3_intro, or_introl/
#G #L #T #H elim (fqu_inv_sort1 … H) -H /3 width=4 by ex2_2_intro, or_intror/
qed-.

lemma fqus_inv_lref1: ∀b,G1,G2,L1,L2,T2,i. ⦃G1, L1, #i⦄ ⊐*[b] ⦃G2, L2, T2⦄ →
                      ∨∨ ∧∧ G1 = G2 & L1 = L2 & #i = T2
                       | ∃∃J,L,V. ⦃G1, L, V⦄ ⊐*[b] ⦃G2, L2, T2⦄ & L1 = L.ⓑ{J}V & i = 0
                       | ∃∃J,L,j. ⦃G1, L, #j⦄ ⊐*[b] ⦃G2, L2, T2⦄ & L1 = L.ⓘ{J} & i = ⫯j.
#b #G1 #G2 #L1 #L2 #T2 #i #H elim (fqus_inv_fqu_sn … H) -H * /3 width=1 by and3_intro, or3_intro0/
#G #L #T #H elim (fqu_inv_lref1 … H) -H * /3 width=7 by or3_intro1, or3_intro2, ex3_4_intro, ex3_3_intro/
qed-.

lemma fqus_inv_gref1: ∀b,G1,G2,L1,L2,T2,l. ⦃G1, L1, §l⦄ ⊐*[b] ⦃G2, L2, T2⦄ →
                      (∧∧ G1 = G2 & L1 = L2 & §l = T2) ∨
                      ∃∃J,L. ⦃G1, L, §l⦄ ⊐*[b] ⦃G2, L2, T2⦄ & L1 = L.ⓘ{J}.
#b #G1 #G2 #L1 #L2 #T2 #l #H elim (fqus_inv_fqu_sn … H) -H * /3 width=1 by and3_intro, or_introl/
#G #L #T #H elim (fqu_inv_gref1 … H) -H /3 width=4 by ex2_2_intro, or_intror/
qed-.

lemma fqus_inv_bind1: ∀b,p,I,G1,G2,L1,L2,V1,T1,T2. ⦃G1, L1, ⓑ{p,I}V1.T1⦄ ⊐*[b] ⦃G2, L2, T2⦄ →
                      ∨∨ ∧∧ G1 = G2 & L1 = L2 & ⓑ{p,I}V1.T1 = T2
                       | ⦃G1, L1, V1⦄ ⊐*[b] ⦃G2, L2, T2⦄
                       | ⦃G1, L1.ⓑ{I}V1, T1⦄ ⊐*[b] ⦃G2, L2, T2⦄
                       | ⦃G1, L1.ⓧ, T1⦄ ⊐*[b] ⦃G2, L2, T2⦄ ∧ b = Ⓕ
                       | ∃∃J,L,T. ⦃G1, L, T⦄ ⊐*[b] ⦃G2, L2, T2⦄ & ⬆*[1] T ≘ ⓑ{p,I}V1.T1 & L1 = L.ⓘ{J}.
#b #p #I #G1 #G2 #L1 #L2 #V1 #T1 #T2 #H elim (fqus_inv_fqu_sn … H) -H * /3 width=1 by and3_intro, or5_intro0/
#G #L #T #H elim (fqu_inv_bind1 … H) -H *
[4: #J ] #H1 #H2 #H3 [4: #Hb ] #H destruct
/3 width=6 by or5_intro1, or5_intro2, or5_intro3, or5_intro4, ex3_3_intro, conj/
qed-.


lemma fqus_inv_bind1_true: ∀p,I,G1,G2,L1,L2,V1,T1,T2. ⦃G1, L1, ⓑ{p,I}V1.T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                           ∨∨ ∧∧ G1 = G2 & L1 = L2 & ⓑ{p,I}V1.T1 = T2
                               | ⦃G1, L1, V1⦄ ⊐* ⦃G2, L2, T2⦄
                               | ⦃G1, L1.ⓑ{I}V1, T1⦄ ⊐* ⦃G2, L2, T2⦄
                               | ∃∃J,L,T. ⦃G1, L, T⦄ ⊐* ⦃G2, L2, T2⦄ & ⬆*[1] T ≘ ⓑ{p,I}V1.T1 & L1 = L.ⓘ{J}.
#p #I #G1 #G2 #L1 #L2 #V1 #T1 #T2 #H elim (fqus_inv_bind1 … H) -H [1,4: * ]
/3 width=1 by and3_intro, or4_intro0, or4_intro1, or4_intro2, or4_intro3, ex3_3_intro/
#_ #H destruct
qed-.

lemma fqus_inv_flat1: ∀b,I,G1,G2,L1,L2,V1,T1,T2. ⦃G1, L1, ⓕ{I}V1.T1⦄ ⊐*[b] ⦃G2, L2, T2⦄ →
                      ∨∨ ∧∧ G1 = G2 & L1 = L2 & ⓕ{I}V1.T1 = T2
                       | ⦃G1, L1, V1⦄ ⊐*[b] ⦃G2, L2, T2⦄
                       | ⦃G1, L1, T1⦄ ⊐*[b] ⦃G2, L2, T2⦄
                       | ∃∃J,L,T. ⦃G1, L, T⦄ ⊐*[b] ⦃G2, L2, T2⦄ & ⬆*[1] T ≘ ⓕ{I}V1.T1 & L1 = L.ⓘ{J}.
#b #I #G1 #G2 #L1 #L2 #V1 #T1 #T2 #H elim (fqus_inv_fqu_sn … H) -H * /3 width=1 by and3_intro, or4_intro0/
#G #L #T #H elim (fqu_inv_flat1 … H) -H *
[3: #J ] #H1 #H2 #H3 #H destruct
/3 width=6 by or4_intro1, or4_intro2, or4_intro3, ex3_3_intro/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma fqus_inv_atom1: ∀b,I,G1,G2,L2,T2. ⦃G1, ⋆, ⓪{I}⦄ ⊐*[b] ⦃G2, L2, T2⦄ →
                      ∧∧ G1 = G2 & ⋆ = L2 & ⓪{I} = T2.
#b #I #G1 #G2 #L2 #T2 #H elim (fqus_inv_fqu_sn … H) -H * /2 width=1 by and3_intro/
#G #L #T #H elim (fqu_inv_atom1 … H)
qed-.

lemma fqus_inv_sort1_bind: ∀b,I,G1,G2,L1,L2,T2,s. ⦃G1, L1.ⓘ{I}, ⋆s⦄ ⊐*[b] ⦃G2, L2, T2⦄ →
                           (∧∧ G1 = G2 & L1.ⓘ{I} = L2 & ⋆s = T2) ∨ ⦃G1, L1, ⋆s⦄ ⊐*[b] ⦃G2, L2, T2⦄.
#b #I #G1 #G2 #L1 #L2 #T2 #s #H elim (fqus_inv_fqu_sn … H) -H * /3 width=1 by and3_intro, or_introl/
#G #L #T #H elim (fqu_inv_sort1_bind … H) -H
#H1 #H2 #H3 #H destruct /2 width=1 by or_intror/
qed-.

lemma fqus_inv_zero1_pair: ∀b,I,G1,G2,L1,L2,V1,T2. ⦃G1, L1.ⓑ{I}V1, #0⦄ ⊐*[b] ⦃G2, L2, T2⦄ →
                           (∧∧ G1 = G2 & L1.ⓑ{I}V1 = L2 & #0 = T2) ∨ ⦃G1, L1, V1⦄ ⊐*[b] ⦃G2, L2, T2⦄.
#b #I #G1 #G2 #L1 #L2 #V1 #T2 #H elim (fqus_inv_fqu_sn … H) -H * /3 width=1 by and3_intro, or_introl/
#G #L #T #H elim (fqu_inv_zero1_pair … H) -H
#H1 #H2 #H3 #H destruct /2 width=1 by or_intror/
qed-.

lemma fqus_inv_lref1_bind: ∀b,I,G1,G2,L1,L2,T2,i. ⦃G1, L1.ⓘ{I}, #⫯i⦄ ⊐*[b] ⦃G2, L2, T2⦄ →
                           (∧∧ G1 = G2 & L1.ⓘ{I} = L2 & #(⫯i) = T2) ∨ ⦃G1, L1, #i⦄ ⊐*[b] ⦃G2, L2, T2⦄.
#b #I #G1 #G2 #L1 #L2 #T2 #i #H elim (fqus_inv_fqu_sn … H) -H * /3 width=1 by and3_intro, or_introl/
#G #L #T #H elim (fqu_inv_lref1_bind … H) -H
#H1 #H2 #H3 #H destruct /2 width=1 by or_intror/
qed-.

lemma fqus_inv_gref1_bind: ∀b,I,G1,G2,L1,L2,T2,l. ⦃G1, L1.ⓘ{I}, §l⦄ ⊐*[b] ⦃G2, L2, T2⦄ →
                           (∧∧ G1 = G2 & L1.ⓘ{I} = L2 & §l = T2) ∨ ⦃G1, L1, §l⦄ ⊐*[b] ⦃G2, L2, T2⦄.
#b #I #G1 #G2 #L1 #L2 #T2 #l #H elim (fqus_inv_fqu_sn … H) -H * /3 width=1 by and3_intro, or_introl/
#G #L #T #H elim (fqu_inv_gref1_bind … H) -H
#H1 #H2 #H3 #H destruct /2 width=1 by or_intror/
qed-.

(* Basic_2A1: removed theorems 1: fqus_drop *)
