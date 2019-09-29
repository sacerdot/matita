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
include "basic_2/rt_conversion/cpce.ma".

(* CONTEXT-SENSITIVE PARALLEL ETA-CONVERSION FOR TERMS **********************)

(* Properties with uniform slicing for local environments *******************)

lemma cpce_eta_drops (h) (n) (G) (K):
      ∀p,W,V1,U. ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V1.U →
      ∀V2. ⦃G,K⦄ ⊢ V1 ⬌η[h] V2 →
      ∀i,L. ⬇*[i] L ≘ K.ⓛW →
      ∀W2. ⬆*[↑i] V2 ≘ W2 → ⦃G,L⦄ ⊢ #i ⬌η[h] +ⓛW2.ⓐ#0.#↑i.
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
      ∀i,L. (∀n,p,K,W,V,U. ⬇*[i] L ≘ K.ⓛW → ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V.U → ⊥) →
      ⦃G,L⦄ ⊢ #i ⬌η[h] #i.
#h #G #i elim i -i
[ * [ #_ // ] #L #I #Hi
  /4 width=8 by cpce_zero, drops_refl/
| #i #IH * [ -IH #_ // ] #L #I #Hi
  /5 width=8 by cpce_lref, drops_drop/
]
qed.
