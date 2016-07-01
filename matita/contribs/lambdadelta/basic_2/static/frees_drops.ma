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

include "ground_2/relocation/nstream_coafter.ma".
include "basic_2/relocation/drops_drops.ma".
include "basic_2/static/frees_frees.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Advanced properties ******************************************************)

lemma frees_lref_atom: ∀b,L,i. ⬇*[b, 𝐔❴i❵] L ≡ ⋆ →
                       ∀f. 𝐈⦃f⦄ → L ⊢ 𝐅*⦃#i⦄ ≡ f.
#b #L elim L -L /2 width=1 by frees_atom/
#L #I #V #IH *
[ #H lapply (drops_fwd_isid … H ?) -H // #H destruct
| /5 width=3 by frees_eq_repl_back, frees_lref, drops_inv_drop1, eq_push_inv_isid/
]
qed.

lemma frees_lref_pair: ∀f,K,V. K ⊢ 𝐅*⦃V⦄ ≡ f → 
                       ∀i,I,L. ⬇*[i] L ≡ K.ⓑ{I}V → L ⊢ 𝐅*⦃#i⦄ ≡ ↑*[i] ⫯f.
#f #K #V #Hf #i elim i -i
[ #I #L #H lapply (drops_fwd_isid … H ?) -H /2 width=1 by frees_zero/
| #i #IH #I #L #H elim (drops_inv_succ … H) -H /3 width=2 by frees_lref/
]
qed.

lemma frees_sort_pushs: ∀f,K,s. K ⊢ 𝐅*⦃⋆s⦄ ≡ f →
                        ∀i,L. ⬇*[i] L ≡ K → L ⊢ 𝐅*⦃⋆s⦄ ≡ ↑*[i] f.
#f #K #s #Hf #i elim i -i
[ #L #H lapply (drops_fwd_isid … H ?) -H //
| #i #IH #L #H elim (drops_inv_succ … H) -H /3 width=1 by frees_sort/
]
qed.

lemma frees_lref_pushs: ∀f,K,j. K ⊢ 𝐅*⦃#j⦄ ≡ f →
                        ∀i,L. ⬇*[i] L ≡ K → L ⊢ 𝐅*⦃#(i+j)⦄ ≡ ↑*[i] f.
#f #K #j #Hf #i elim i -i
[ #L #H lapply (drops_fwd_isid … H ?) -H //
| #i #IH #L #H elim (drops_inv_succ … H) -H
  #I #Y #V #HYK #H destruct /3 width=1 by frees_lref/
]
qed.

lemma frees_gref_pushs: ∀f,K,l. K ⊢ 𝐅*⦃§l⦄ ≡ f →
                        ∀i,L. ⬇*[i] L ≡ K → L ⊢ 𝐅*⦃§l⦄ ≡ ↑*[i] f.
#f #K #l #Hf #i elim i -i
[ #L #H lapply (drops_fwd_isid … H ?) -H //
| #i #IH #L #H elim (drops_inv_succ … H) -H /3 width=1 by frees_gref/
]
qed.

(* Advanced inversion lemmas ************************************************)

lemma frees_inv_lref_drops: ∀i,f,L. L ⊢ 𝐅*⦃#i⦄ ≡ f →
                            (⬇*[Ⓕ, 𝐔❴i❵] L ≡ ⋆ ∧ 𝐈⦃f⦄) ∨
                            ∃∃g,I,K,V. K ⊢ 𝐅*⦃V⦄ ≡ g &
                                       ⬇*[i] L ≡ K.ⓑ{I}V & f = ↑*[i] ⫯g.
#i elim i -i
[ #f #L #H elim (frees_inv_zero … H) -H *
  /4 width=7 by ex3_4_intro, or_introl, or_intror, conj, drops_refl/
| #i #IH #f #L #H elim (frees_inv_lref … H) -H * /3 width=1 by or_introl, conj/
  #g #I #K #V #Hg #H1 #H2 destruct
  elim (IH … Hg) -IH -Hg *
  [ /4 width=3 by or_introl, conj, isid_push, drops_drop/
  | /4 width=7 by drops_drop, ex3_4_intro, or_intror/
  ]
]
qed-.

(* Properties with generic slicing for local environments *******************)

lemma frees_lifts: ∀b,f1,K,T. K ⊢ 𝐅*⦃T⦄ ≡ f1 →
                   ∀f,L. ⬇*[b, f] L ≡ K → ∀U. ⬆*[f] T ≡ U →
                   ∀f2. f ~⊚ f1 ≡ f2 → L ⊢ 𝐅*⦃U⦄ ≡ f2.
#b #f1 #K #T #H lapply (frees_fwd_isfin … H) elim H -f1 -K -T
[ #f1 #I #Hf1 #_ #f #L #H1 #U #H2 #f2 #H3
  lapply (coafter_isid_inv_dx … H3 … Hf1) -f1 #Hf2
  elim (lifts_inv_atom1 … H2) -H2 *
  /2 width=1 by frees_sort_gen, frees_gref_gen/
  #i #j #Hij #H #H0 destruct
  elim (drops_inv_atom2 … H1) -H1 #n #g #H1 #Hf
  elim (after_at_fwd … Hij … Hf) -f #x #_ #Hj -g -i
  lapply (at_inv_uni … Hj) -Hj #H destruct
  /3 width=8 by frees_lref_atom, drops_trans/
| #f1 #I #K #V #s #_ #IH #Hf1 #f #L #H1 #U #H2 #f2 #H3
  lapply (isfin_fwd_push … Hf1 ??) -Hf1 [3: |*: // ] #Hf1
  lapply (lifts_inv_sort1 … H2) -H2 #H destruct
  elim (drops_split_trans_pair2 … H1) -H1 [ |*: // ] #Y #W #HLY #HYK #_
  elim (coafter_fwd_xpx_pushs … H3) [ |*: // ] #g2 #H2 destruct
  lapply (coafter_tls_succ … H3 ??) -H3 [3: |*: // ] #H3
  lapply (IH … HYK … H3) -IH -H3 -HYK [1,3: // | skip ]
  /3 width=5 by drops_isuni_fwd_drop2, frees_sort_pushs/
| #f1 #I #K #V #_ #IH #Hf1 #f #L #H1 #U #H2 #f2 #H3
  lapply (isfin_inv_next … Hf1 ??) -Hf1 [3: |*: // ] #Hf1
  lapply (lifts_inv_lref1 … H2) -H2 * #j #Hf #H destruct
  elim (drops_split_trans_pair2 … H1) -H1 [ |*: // ] #Y #W #HLY #HYK #HVW
  elim (coafter_fwd_xnx_pushs … H3) [ |*: // ] #g2 #H2 destruct
  lapply (coafter_tls_succ … H3 ??) -H3 [3: |*: // ]
  <tls_S in ⊢ (???%→?); <tls_pushs <tl_next_rew <tl_next_rew #H3
  lapply (IH … HYK … HVW … H3) -IH -H3 -HYK -HVW //
  /2 width=5 by frees_lref_pair/
| #f1 #I #K #V #i #_ #IH #Hf1 #f #L #H1 #U #H2 #f2 #H3
  lapply (isfin_fwd_push … Hf1 ??) -Hf1 [3: |*: // ] #Hf1
  lapply (lifts_inv_lref1 … H2) -H2 * #x #Hf #H destruct
  elim (at_inv_nxx … Hf) -Hf [ |*: // ] #j #Hf #H destruct
  elim (drops_split_trans_pair2 … H1) -H1 [ |*: // ] #Y #W #HLY #HYK #_
  elim (coafter_fwd_xpx_pushs … H3) [ |*: // ] #g2 #H2 destruct
  lapply (coafter_tls_succ … H3 ??) -H3 [3: |*: // ] <tls_pushs #H3
  lapply (drops_isuni_fwd_drop2 … HLY) -HLY // #HLY
  lapply (IH … HYK … H3) -IH -H3 -HYK [4: |*: /2 width=2 by lifts_lref/ ]
  >plus_S1 /2 width=3 by frees_lref_pushs/ (**) (* full auto fails *)
| #f1 #I #K #V #l #_ #IH #Hf1 #f #L #H1 #U #H2 #f2 #H3
  lapply (isfin_fwd_push … Hf1 ??) -Hf1 [3: |*: // ] #Hf1
  lapply (lifts_inv_gref1 … H2) -H2 #H destruct
  elim (drops_split_trans_pair2 … H1) -H1 [ |*: // ] #Y #W #HLY #HYK #_
  elim (coafter_fwd_xpx_pushs … H3) [ |*: // ] #g2 #H2 destruct
  lapply (coafter_tls_succ … H3 ??) -H3 [3: |*: // ] #H3
  lapply (IH … HYK … H3) -IH -H3 -HYK [1,3: // | skip ]
  /3 width=5 by drops_isuni_fwd_drop2, frees_gref_pushs/
| #f1V #f1T #f1 #p #I #K #V #T #_ #_ #H1f1 #IHV #IHT #H2f1 #f #L #H1 #Y #H2 #f2 #H3
  elim (sor_inv_isfin3 … H1f1) // #Hf1V #H
  lapply (isfin_inv_tl … H) -H
  elim (lifts_inv_bind1 … H2) -H2 #W #U #HVW #HTU #H destruct
  elim (coafter_sor … H3 … H1f1) /2 width=5 by coafter_isfin2_fwd/ -H3 -H1f1 #f2V #f2T #Hf2V #H
  elim (coafter_inv_tl1 … H) -H /4 width=5 by frees_bind, drops_skip/
| #f1V #f1T #f1 #I #K #V #T #_ #_ #H1f1 #IHV #IHT #H2f1 #f #L #H1 #Y #H2 #f2 #H3
  elim (sor_inv_isfin3 … H1f1) //
  elim (lifts_inv_flat1 … H2) -H2 #W #U #HVW #HTU #H destruct
  elim (coafter_sor … H3 … H1f1)
  /3 width=5 by coafter_isfin2_fwd, frees_flat/
]
qed-.

(* Forward lemmas with generic slicing for local environments ***************)

lemma frees_fwd_coafter: ∀b,f2,L,U. L ⊢ 𝐅*⦃U⦄ ≡ f2 →
                         ∀f,K. ⬇*[b, f] L ≡ K → ∀T. ⬆*[f] T ≡ U →
                         ∀f1. K ⊢ 𝐅*⦃T⦄ ≡ f1 → f ~⊚ f1 ≡ f2.
/4 width=11 by frees_lifts, frees_mono, coafter_eq_repl_back0/ qed-.

(* Inversion lemmas with generic slicing for local environments *************)

lemma frees_inv_lifts: ∀b,f2,L,U. L ⊢ 𝐅*⦃U⦄ ≡ f2 →
                       ∀f,K. ⬇*[b, f] L ≡ K → ∀T. ⬆*[f] T ≡ U →
                       ∀f1. f ~⊚ f1 ≡ f2 → K ⊢ 𝐅*⦃T⦄ ≡ f1.
#b #f2 #L #U #H lapply (frees_fwd_isfin … H) elim H -f2 -L -U
[ #f2 #I #Hf2 #_ #f #K #H1 #T #H2 #f1 #H3
  lapply (coafter_fwd_isid2 … H3 … Hf2) -H3 // -Hf2 #Hf1
  elim (drops_inv_atom1 … H1) -H1 #H #_ destruct
  elim (lifts_inv_atom2 … H2) -H2 * /2 width=3 by frees_atom/
| #f2 #I #L #W #s #_ #IH #Hf2 #f #Y #H1 #T #H2 #f1 #H3
  lapply (isfin_fwd_push … Hf2 ??) -Hf2 [3: |*: // ] #Hf2
  lapply (lifts_inv_sort2 … H2) -H2 #H destruct
  elim (coafter_inv_xxp … H3) -H3 [1,3: * |*: // ]
  [ #g #g1 #Hf2 #H #H0 destruct
    elim (drops_inv_skip1 … H1) -H1 #K #V #HLK #_ #H destruct
  | #g #Hf2 #H destruct
    lapply (drops_inv_drop1 … H1) -H1
  ] /3 width=4 by frees_sort/
| #f2 #I #L #W #_ #IH #Hf2 #f #Y #H1 #T #H2 #f1 #H3
  lapply (isfin_inv_next … Hf2 ??) -Hf2 [3: |*: // ] #Hf2
  elim (lifts_inv_lref2 … H2) -H2 #i #H2 #H destruct
  lapply (at_inv_xxp … H2 ?) -H2 // * #g #H #H0 destruct
  elim (drops_inv_skip1 … H1) -H1 #K #V #HLK #HVW #H destruct
  elim (coafter_inv_pxn … H3) -H3 [ |*: // ] #g1 #Hf2 #H destruct
  /3 width=4 by frees_zero/
| #f2 #I #L #W #j #_ #IH #Hf2 #f #Y #H1 #T #H2 #f1 #H3
  lapply (isfin_fwd_push … Hf2 ??) -Hf2 [3: |*: // ] #Hf2
  elim (lifts_inv_lref2 … H2) -H2 #x #H2 #H destruct
  elim (coafter_inv_xxp … H3) -H3 [1,3: * |*: // ]
  [ #g #g1 #Hf2 #H #H0 destruct
    elim (drops_inv_skip1 … H1) -H1 #K #V #HLK #HVW #H destruct
    elim (at_inv_xpn … H2) -H2 [ |*: // ] #j #Hg #H destruct
  | #g #Hf2 #H destruct
    lapply (drops_inv_drop1 … H1) -H1
    lapply (at_inv_xnn … H2 ????) -H2 [5: |*: // ]
  ] /4 width=4 by lifts_lref, frees_lref/
| #f2 #I #L #W #l #_ #IH #Hf2 #f #Y #H1 #T #H2 #f1 #H3
  lapply (isfin_fwd_push … Hf2 ??) -Hf2 [3: |*: // ] #Hf2
  lapply (lifts_inv_gref2 … H2) -H2 #H destruct
  elim (coafter_inv_xxp … H3) -H3 [1,3: * |*: // ]
  [ #g #g1 #Hf2 #H #H0 destruct
    elim (drops_inv_skip1 … H1) -H1 #K #V #HLK #_ #H destruct
  | #g #Hf2 #H destruct
    lapply (drops_inv_drop1 … H1) -H1
  ] /3 width=4 by frees_gref/
| #f2W #f2U #f2 #p #I #L #W #U #_ #_ #H1f2 #IHW #IHU #H2f2 #f #K #H1 #X #H2 #f1 #H3
  elim (sor_inv_isfin3 … H1f2) // #H1f2W #H
  lapply (isfin_inv_tl … H) -H
  elim (lifts_inv_bind2 … H2) -H2 #V #T #HVW #HTU #H destruct
  elim (coafter_inv_sor … H3 … H1f2) -H3 -H1f2 // #f1W #f1U #H2f2W #H
  elim (coafter_inv_tl0 … H) -H /4 width=5 by frees_bind, drops_skip/
| #f2W #f2U #f2 #I #L #W #U #_ #_ #H1f2 #IHW #IHU #H2f2 #f #K #H1 #X #H2 #f1 #H3
  elim (sor_inv_isfin3 … H1f2) //
  elim (lifts_inv_flat2 … H2) -H2 #V #T #HVW #HTU #H destruct
  elim (coafter_inv_sor … H3 … H1f2) -H3 -H1f2 /3 width=5 by frees_flat/
]
qed-.

lemma frees_inv_drops: ∀f2,L,U. L ⊢ 𝐅*⦃U⦄ ≡ f2 →
                       ∀f,K. ⬇*[Ⓣ, f] L ≡ K → ∀f1. f ~⊚ f1 ≡ f2 →
                       ∃∃T. K ⊢ 𝐅*⦃T⦄ ≡ f1 & ⬆*[f] T ≡ U.
#f2 #L #U #H lapply (frees_fwd_isfin … H) elim H -f2 -L -U
[ #f2 #I #Hf2 #_ #f #K #H1 #f1 #H2
  lapply (coafter_fwd_isid2 … H2 ??) -H2 // -Hf2 #Hf1
  elim (drops_inv_atom1 … H1) -H1 #H #Hf destruct
  /4 width=3 by frees_atom, lifts_refl, ex2_intro/
| #f2 #I #L #W #s #_ #IH #Hf2 #f #Y #H1 #f1 #H2
  lapply (isfin_fwd_push … Hf2 ??) -Hf2 [3: |*: // ] #Hf2
  elim (coafter_inv_xxp … H2) -H2 [1,3: * |*: // ]
  [ #g #g1 #Hf2 #H #H0 destruct
    elim (drops_inv_skip1 … H1) -H1 #K #V #HLK #_ #H destruct
  | #g #Hf2 #H destruct
    lapply (drops_inv_drop1 … H1) -H1 #HLK
  ]
  elim (IH … HLK … Hf2) -L // -f2 #X #Hg1 #HX
  lapply (lifts_inv_sort2 … HX) -HX #H destruct
  /3 width=3 by frees_sort, lifts_sort, ex2_intro/
| #f2 #I #L #W #_ #IH #Hf2 #f #Y #H1 #f1 #H2
  lapply (isfin_inv_next … Hf2 ??) -Hf2 [3: |*: // ] #Hf2
  elim (coafter_inv_xxn … H2) -H2 [ |*: // ] #g #g1 #Hf2 #H0 #H destruct
  elim (drops_inv_skip1 … H1) -H1 #K #V #HLK #HVW #H destruct
  elim (IH … HLK … Hf2) -L // -f2 #X #Hg1 #HX
  lapply (lifts_inj … HX … HVW) -W #H destruct
  /3 width=3 by frees_zero, lifts_lref, ex2_intro/
| #f2 #I #L #W #j #_ #IH #Hf2 #f #Y #H1 #f1 #H2
  lapply (isfin_fwd_push … Hf2 ??) -Hf2 [3: |*: // ] #Hf2
  elim (coafter_inv_xxp … H2) -H2 [1,3: * |*: // ]
  [ #g #g1 #Hf2 #H #H0 destruct
    elim (drops_inv_skip1 … H1) -H1 #K #V #HLK #_ #H destruct
  | #g #Hf2 #H destruct
    lapply (drops_inv_drop1 … H1) -H1 #HLK
  ]
  elim (IH … HLK … Hf2) -L // -f2 #X #Hg1 #HX
  elim (lifts_inv_lref2 … HX) -HX #i #Hij #H destruct
  /4 width=7 by frees_lref, lifts_lref, at_S1, at_next, ex2_intro/
| #f2 #I #L #W #l #_ #IH #Hf2 #f #Y #H1 #f1 #H2
  lapply (isfin_fwd_push … Hf2 ??) -Hf2 [3: |*: // ] #Hf2
  elim (coafter_inv_xxp … H2) -H2 [1,3: * |*: // ]
  [ #g #g1 #Hf2 #H #H0 destruct
    elim (drops_inv_skip1 … H1) -H1 #K #V #HLK #_ #H destruct
  | #g #Hf2 #H destruct
    lapply (drops_inv_drop1 … H1) -H1 #HLK
  ]
  elim (IH … HLK … Hf2) -L // -f2 #X #Hg1 #HX
  lapply (lifts_inv_gref2 … HX) -HX #H destruct
  /3 width=3 by frees_gref, lifts_gref, ex2_intro/
| #f2W #f2U #f2 #p #I #L #W #U #_ #_ #H1f2 #IHW #IHU #H2f2 #f #K #H1 #f1 #H2
  elim (sor_inv_isfin3 … H1f2) // #H1f2W #H
  lapply (isfin_inv_tl … H) -H #H1f2U
  elim (coafter_inv_sor … H2 … H1f2) -H2 -H1f2 // #f1W #f1U #H2f2W #H #Hf1
  elim (coafter_inv_tl0 … H) -H #g1 #H2f2U #H destruct
  elim (IHW … H1 … H2f2W) -IHW -H2f2W // -H1f2W #V #Hf1W #HVW
  elim (IHU … H2f2U) -IHU -H2f2U
  /3 width=5 by frees_bind, drops_skip, lifts_bind, ex2_intro/
| #f2W #f2U #f2 #I #L #W #U #_ #_ #H1f2 #IHW #IHU #H2f2 #f #K #H1 #f1 #H2
  elim (sor_inv_isfin3 … H1f2) // #H1f2W #H1f2U
  elim (coafter_inv_sor … H2 … H1f2) -H2 -H1f2 // #f1W #f1U #H2f2W #H2f2U #Hf1
  elim (IHW … H1 … H2f2W) -IHW -H2f2W // -H1f2W
  elim (IHU … H1 … H2f2U) -L -H2f2U
  /3 width=5 by frees_flat, lifts_flat, ex2_intro/
]
qed-.
