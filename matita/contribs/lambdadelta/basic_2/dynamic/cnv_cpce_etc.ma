include "basic_2/dynamic/cnv_cpce.ma".

(*
lemma cpce_inv_eta_drops (h) (n) (G) (L) (i):
      ∀X. ⦃G,L⦄ ⊢ #i ⬌η[h] X →
      ∀K,W. ⇩*[i] L ≘ K.ⓛW →
      ∀p,V1,U. ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V1.U →
      ∀V2. ⦃G,K⦄ ⊢ V1 ⬌η[h] V2 →
      ∀W2. ⇧*[↑i] V2 ≘ W2 → X = +ⓛW2.ⓐ#0.#↑i.
*)


theorem cpce_mono_cnv (h) (a) (G) (L):
        ∀T. ⦃G,L⦄ ⊢ T ![h,a] →
        ∀T1. ⦃G,L⦄ ⊢ T ⬌η[h] T1 → ∀T2. ⦃G,L⦄ ⊢ T ⬌η[h] T2 → T1 = T2.
#h #a #G #L #T #HT  
