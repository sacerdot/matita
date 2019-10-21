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

include "basic_2/rt_transition/lpr_drops.ma".
include "basic_2/rt_computation/cpms_lpr.ma".
include "basic_2/rt_computation/fpbg_fqup.ma".
include "basic_2/rt_conversion/cpce_drops.ma".
include "basic_2/rt_conversion/lpce_drops.ma".
include "basic_2/dynamic/cnv_drops.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

definition IH (h) (a): relation3 genv lenv term ≝
           λG,L0,T0. ⦃G,L0⦄ ⊢ T0 ![h,a] →
           ∀n,T1. ⦃G,L0⦄ ⊢ T0 ➡[n,h] T1 → ∀T2. ⦃G,L0⦄ ⊢ T0 ⬌η[h] T2 →
           ∀L1. ⦃G,L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G,L0⦄ ⊢ ⬌η[h] L2 →
           ∃∃T. ⦃G,L1⦄ ⊢ T1 ⬌η[h] T & ⦃G,L2⦄ ⊢ T2 ➡[n,h] T.

(* Properties with eta-conversion for full local environments ***************)  

lemma pippo_aux (h) (a) (G0) (L0) (T0):
                (∀G,L,T. ⦃G0,L0,T0⦄ >[h] ⦃G,L,T⦄ → IH h a G L T) →
                IH h a G0 L0 T0.
#h #a #G0 #L0 * *
[ #s #_ #_ #n #X1 #HX1 #X2 #HX2 #L1 #HL01 #L2 #HL02
  elim (cpm_inv_sort1 … HX1) -HX1 #H #Hn destruct
  lapply (cpce_inv_sort_sn … HX2) -HX2 #H destruct
  /3 width=3 by cpce_sort, cpm_sort, ex2_intro/
| #i #IH #Hi #n #X1 #HX1 #X2 #HX2 #L1 #HL01 #L2 #HL02
  elim (cnv_inv_lref_drops … Hi) -Hi #I #K0 #W0 #HLK0 #HW0
  elim (lpr_drops_conf … HLK0 … HL01) [| // ] #Y1 #H1 #HLK1
  elim (lpr_inv_pair_sn … H1) -H1 #K1 #W1 #HK01 #HW01 #H destruct
  elim (lpce_drops_conf … HLK0 … HL02) [| // ] #Y2 #H2 #HLK2
  elim (lpce_inv_pair_sn … H2) -H2 #K2 #W2 #HK02 #HW02 #H destruct
  elim (cpm_inv_lref1_drops … HX1) -HX1 *
  [ #H1 #H2 destruct
    elim (cpce_inv_lref_sn_drops_pair … HX2 … HLK0) -HX2 *
    [ #H1 #H2 destruct -L0 -K0 -W0
      /3 width=3 by cpce_ldef_drops, ex2_intro/
    | #H1 #HW #H2 destruct -L0 -W2 -HW0 -HK02
      @(ex2_intro … (#i)) [| // ]
      @(cpce_ldec_drops … HLK1) -HLK1 #n #p #V0 #U0 #HWU0
      /4 width=10 by lpr_cpms_trans, cpms_step_sn/
    | #n #p #W01 #W02 #V0 #V01 #V02 #U0 #H1 #HWU0 #HW001 #HW012 #HV001 #HV012 #H2 destruct 
    ]
  | lapply (drops_isuni_fwd_drop2 … HLK1) [ // ] -W1 #HLK1
    #Y0 #X0 #W1 #HLY0 #HW01 #HWX1 -HL01 -HL02
    lapply (drops_mono … HLY0 … HLK0) -HLY0 #H destruct
    lapply (cpce_inv_lref_sn_drops_ldef … HX2 … HLK0) -HX2 #H destruct
    elim (IH … HW0 … HW01 … HW02 … HK01 … HK02)
    [| /3 width=2 by fqup_fpbg, fqup_lref/ ] -L0 -K0 #W #HW1 #HW2
    elim (lifts_total W (𝐔❴↑i❵)) #V #HWV
    /3 width=9 by cpce_lifts_bi, cpm_delta_drops, ex2_intro/
  | lapply (drops_isuni_fwd_drop2 … HLK1) [ // ] -W1 #HLK1
    #m #Y0 #X0 #W1 #HLY0 #HW01 #HWX1 #H destruct -HL01 -HL02
    lapply (drops_mono … HLY0 … HLK0) -HLY0 #H destruct
    elim (cpce_inv_lref_sn_drops_ldec … HX2 … HLK0) -HX2 *
    [ #_ #H destruct
      elim (IH … HW0 … HW01 … HW02 … HK01 … HK02)
      [| /3 width=2 by fqup_fpbg, fqup_lref/ ] -L0 -K0 #W #HW1 #HW2
      elim (lifts_total W (𝐔❴↑i❵)) #V #HWV
      /3 width=9 by cpce_lifts_bi, cpm_ell_drops, ex2_intro/
    | lapply (drops_isuni_fwd_drop2 … HLK2) [ // ] -W2 #HLK2
      #n #p #W01 #W02 #V0 #V01 #V02 #U0 #_ #HW001 #HW012 #_ #_ #H destruct -V0 -V01 -U0
      elim (IH … HW0 … HW01 … HW001 … HK01 … HK02)
      [| /3 width=2 by fqup_fpbg, fqup_lref/ ] -L0 -K0 #W #HW1 #HW2
      elim (lifts_total W (𝐔❴↑i❵)) #V #HWV
      /4 width=11 by cpce_lifts_bi, cpm_lifts_bi, cpm_ee, ex2_intro/
    ]
  ]
| #l #_ #_ #n #X1 #HX1 #X2 #HX2 #L1 #HL01 #L2 #HL02
  elim (cpm_inv_gref1 … HX1) -HX1 #H1 #H2 destruct
  lapply (cpce_inv_gref_sn … HX2) -HX2 #H destruct
  /3 width=3 by cpce_gref, cpr_refl, ex2_intro/

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
