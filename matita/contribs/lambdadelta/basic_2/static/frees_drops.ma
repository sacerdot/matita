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

include "ground_2/relocation/rtmap_pushs.ma".
include "ground_2/relocation/rtmap_coafter.ma".
include "basic_2/relocation/lifts_lifts.ma".
include "basic_2/relocation/drops.ma".
include "basic_2/static/frees.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Advanced properties ******************************************************)

lemma frees_lref_atom: ∀L,i. ⬇*[Ⓕ, 𝐔❴i❵] L ≡ ⋆ → L ⊢ 𝐅*⦃#i⦄ ≡ 𝐈𝐝.
#L elim L -L /2 width=1 by frees_atom/
#L #I #V #IH *
[ #H lapply (drops_fwd_isid … H ?) -H // #H destruct
| /4 width=3 by frees_lref, drops_inv_drop1/
]
qed.

lemma frees_lref_pair: ∀f,K,V. K ⊢ 𝐅*⦃V⦄ ≡ f → 
                       ∀i,I,L. ⬇*[i] L ≡ K.ⓑ{I}V → L ⊢ 𝐅*⦃#i⦄ ≡ ↑*[i] ⫯f.
#f #K #V #Hf #i elim i -i
[ #I #L #H lapply (drops_fwd_isid … H ?) -H /2 width=1 by frees_zero/
| #i #IH #I #L #H elim (drops_inv_succ … H) -H /3 width=2 by frees_lref/
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

(* Inversion lemmas with generic slicing for local environments *************)

lemma frees_inv_lifts: ∀b,f2,L,U. L ⊢ 𝐅*⦃U⦄ ≡ f2 →
                       ∀f,K. ⬇*[b, f] L ≡ K → ∀T. ⬆*[f] T ≡ U →
                       ∀f1. f ~⊚ f1 ≡ f2 → K ⊢ 𝐅*⦃T⦄ ≡ f1.
#b #f2 #L #U #H lapply (frees_fwd_isfin … H) elim H -f2 -L -U
[ #f2 #I #Hf2 #_ #f #K #H1 #T #H2 #f1 #H3
  lapply (coafter_fwd_isid2 … H3 … Hf2) -H3 // -Hf2 #Hf1
  elim (drops_inv_atom1 … H1) -H1 #H #_ destruct
  elim (lifts_fwd_atom2 … H2) -H2
  /2 width=3 by frees_atom/
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
