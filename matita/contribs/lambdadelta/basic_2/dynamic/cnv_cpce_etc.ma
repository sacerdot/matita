include "basic_2/dynamic/cnv_cpce.ma".

lemma pippo (h) (a) (G) (L0):
      ∀T0. ⦃G,L0⦄ ⊢ T0 ![h,a] →
      ∀n,T1. ⦃G,L0⦄ ⊢ T0 ➡[n,h] T1 → ∀T2. ⦃G,L0⦄ ⊢ T0 ⬌η[h] T2 →
      ∀L1. ⦃G,L0⦄ ⊢ ➡[h] L1 →
      ∃∃T. ⦃G,L1⦄ ⊢ T1 ⬌η[h] T & ⦃G,L0⦄ ⊢ T2 ➡[n,h] T. 
#h #a #G #L0 * *
[ #s #_ #n #X1 #HX1 #X2 #HX2 #L1 #HL01
  elim (cpm_inv_sort1 … HX1) -HX1 #H #Hn destruct
  lapply (cpce_inv_sort_sn … HX2) -HX2 #H destruct
  /3 width=3 by cpce_sort, cpm_sort, ex2_intro/
| #i #_ #n #X1 #HX1 #X2 #HX2 #L1 #HL01
  elim (drops_F_uni L0 i)
  [
  | *    

(*
lemma cpce_inv_eta_drops (h) (n) (G) (L) (i):
      ∀X. ⦃G,L⦄ ⊢ #i ⬌η[h] X →
      ∀K,W. ⇩*[i] L ≘ K.ⓛW →
      ∀p,V1,U. ⦃G,K⦄ ⊢ W ➡*[n,h] ⓛ{p}V1.U →
      ∀V2. ⦃G,K⦄ ⊢ V1 ⬌η[h] V2 →
      ∀W2. ⇧*[↑i] V2 ≘ W2 → X = +ⓛW2.ⓐ#0.#↑i.

theorem cpce_mono_cnv (h) (a) (G) (L):
        ∀T. ⦃G,L⦄ ⊢ T ![h,a] →
        ∀T1. ⦃G,L⦄ ⊢ T ⬌η[h] T1 → ∀T2. ⦃G,L⦄ ⊢ T ⬌η[h] T2 → T1 = T2.
#h #a #G #L #T #HT
*)
