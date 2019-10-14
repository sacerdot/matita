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

include "static_2/relocation/drops.ma".
include "static_2/relocation/lifts_lifts.ma".
include "basic_2/rt_conversion/cpce.ma".

(* CONTEXT-SENSITIVE PARALLEL ETA-CONVERSION FOR TERMS **********************)

(* Properties with uniform slicing for local environments *******************)

lemma cpce_eta_drops (h) (n) (G) (K):
      ∀p,W,V1,U. ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V1.U →
      ∀V2. ⦃G,K⦄ ⊢ V1 ⬌η[h] V2 →
      ∀i,L. ⇩*[i] L ≘ K.ⓛW →
      ∀W2. ⇧*[↑i] V2 ≘ W2 → ⦃G,L⦄ ⊢ #i ⬌η[h] +ⓛW2.ⓐ#0.#↑i.
#h #n #G #K #p #W #V1 #U #HWU #V2 #HV12 #i elim i -i
[ #L #HLK #W2 #HVW2
  >(drops_fwd_isid … HLK) -L [| // ] /2 width=8 by cpce_eta/
| #i #IH #L #HLK #W2 #HVW2
  elim (drops_inv_succ … HLK) -HLK #I #Y #HYK #H destruct
  elim (lifts_split_trans … HVW2 (𝐔❴↑i❵) (𝐔❴1❵)) [| // ] #X2 #HVX2 #HXW2 
  /5 width=7 by cpce_lref, lifts_push_lref, lifts_bind, lifts_flat/
]
qed.

lemma cpce_zero_drops (h) (G):
      ∀i,L. (∀n,p,K,W,V,U. ⇩*[i] L ≘ K.ⓛW → ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U → ⊥) →
      ⦃G,L⦄ ⊢ #i ⬌η[h] #i.
#h #G #i elim i -i
[ * [ #_ // ] #L #I #Hi
  /4 width=8 by cpce_zero, drops_refl/
| #i #IH * [ -IH #_ // ] #L #I #Hi
  /5 width=8 by cpce_lref, drops_drop/
]
qed.

(* Inversion lemmas with uniform slicing for local environments *************)

lemma cpce_inv_lref_sn_drops (h) (G) (i) (L):
      ∀X2. ⦃G,L⦄ ⊢ #i ⬌η[h] X2 →
      ∀I,K. ⇩*[i] L ≘ K.ⓘ{I} →
      ∨∨ ∧∧ ∀n,p,W,V,U. I = BPair Abst W → ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U → ⊥ & #i = X2
       | ∃∃n,p,W,V1,V2,W2,U. ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V1.U & ⦃G,K⦄ ⊢ V1 ⬌η[h] V2
                           & ⇧*[↑i] V2 ≘ W2 & I = BPair Abst W & +ⓛW2.ⓐ#0.#(↑i) = X2.
#h #G #i elim i -i
[ #L #X2 #HX2 #I #K #HLK
  lapply (drops_fwd_isid … HLK ?) -HLK [ // ] #H destruct
  /2 width=1 by cpce_inv_zero_sn/
| #i #IH #L0 #X0 #HX0 #J #K #H0
  elim (drops_inv_succ … H0) -H0 #I #L #HLK #H destruct
  elim (cpce_inv_lref_sn … HX0) -HX0 #X2 #HX2 #HX20
  elim (IH … HX2 … HLK) -IH -I -L *
  [ #HJ #H destruct
    lapply (lifts_inv_lref1_uni … HX20) -HX20 #H destruct
    /4 width=7 by or_introl, conj/
  | #n #p #W #V1 #V2 #W2 #U #HWU #HV12 #HVW2 #H1 #H2 destruct
    elim (lifts_inv_bind1 … HX20) -HX20 #X2 #X #HWX2 #HX #H destruct
    elim (lifts_inv_flat1 … HX) -HX #X0 #X1 #H0 #H1 #H destruct
    lapply (lifts_inv_push_zero_sn … H0) -H0 #H destruct
    elim (lifts_inv_push_succ_sn … H1) -H1 #j #Hj #H destruct
    lapply (lifts_inv_lref1_uni … Hj) -Hj #H destruct
    /4 width=12 by lifts_trans_uni, ex5_7_intro, or_intror/
  ]
]
qed-.

lemma cpce_inv_zero_sn_drops (h) (G) (i) (L):
      ∀X2. ⦃G,L⦄ ⊢ #i ⬌η[h] X2 →
      ∀I,K. ⇩*[i] L ≘ K.ⓘ{I} →
      (∀n,p,W,V,U. I = BPair Abst W → ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U → ⊥) →
      #i = X2.
#h #G #i #L #X2 #HX2 #I #K #HLK #HI
elim (cpce_inv_lref_sn_drops … HX2 … HLK) -L *
[ #_ #H //
| #n #p #W #V1 #V2 #W2 #U #HWU #_ #_ #H destruct
  elim (HI … HWU) -n -p -K -X2 -V1 -V2 -W2 -U -i //
]
qed-.
