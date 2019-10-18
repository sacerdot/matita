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

include "basic_2/dynamic/cnv_cpce.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

definition IH (h) (a): relation3 genv lenv term ≝
           λG,L0,T0. ⦃G,L0⦄ ⊢ T0 ![h,a] →
           ∀n,T1. ⦃G,L0⦄ ⊢ T0 ➡[n,h] T1 → ∀T2. ⦃G,L0⦄ ⊢ T0 ⬌η[h] T2 →
           ∀L1. ⦃G,L0⦄ ⊢ ➡[h] L1 →
           ∃∃T. ⦃G,L1⦄ ⊢ T1 ⬌η[h] T & ⦃G,L0⦄ ⊢ T2 ➡[n,h] T.

lemma pippo_aux (h) (a) (G0) (L0) (T0):
                (∀G,L,T. ⦃G0,L0,T0⦄ >[h] ⦃G,L,T⦄ → IH h a G L T) →
                IH h a G0 L0 T0.
#h #a #G0 #L0 * *
[ #s #_ #_ #n #X1 #HX1 #X2 #HX2 #L1 #HL01
  elim (cpm_inv_sort1 … HX1) -HX1 #H #Hn destruct
  lapply (cpce_inv_sort_sn … HX2) -HX2 #H destruct
  /3 width=3 by cpce_sort, cpm_sort, ex2_intro/
| #i #IH #Hi #n #X1 #HX1 #X2 #HX2 #L1 #HL01
  elim (cnv_inv_lref_drops … Hi) -Hi #I #K0 #W0 #HLK0 #HW0
  elim (lpr_drops_conf … HLK0 … HL01) [| // ] #Y1 #H1 #HLK1
  elim (lex_inv_pair_sn … H1) -H1 #K1 #W1 #HK01 #HW01 #H destruct
  elim (cpce_inv_lref_sn_drops_bind … HX2 … HLK0) -HX2 *
  [ #HI #H destruct
    elim (cpm_inv_lref1_drops … HX1) -HX1 *
    [ #H1 #H2 destruct -HW0 -HLK0 -IH
      @(ex2_intro … (#i)) [| // ]
      @cpce_zero_drops #n #p #Y1 #X1 #V1 #U1 #HLY1 #HWU1
      lapply (drops_mono … HLY1 … HLK1) -L1 #H2 destruct
      /4 width=12 by lpr_cpms_trans, cpms_step_sn/
    | #Y0 #W0 #W1 #HLY0 #HW01 #HWX1 -HI -HW0 -IH
      lapply (drops_mono … HLY0 … HLK0) -HLY0 #H destruct
      @(ex2_intro … X1) [| /2 width=6 by cpm_delta_drops/ ]

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
