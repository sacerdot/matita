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

include "basic_2/dynamic/cnv_cpm_tdeq_trans.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Properties with restricted rt-computation for terms **********************)

fact cpms_tdneq_fwd_step_sn_aux (a) (h) (n) (G) (L) (T1):
     ∀T2. ⦃G, L⦄ ⊢ T1 ➡*[n,h] T2 → ⦃G, L⦄ ⊢ T1 ![a,h] → (T1 ≛ T2 → ⊥) →
     (∀G0,L0,T0. ⦃G,L,T1⦄ >[h] ⦃G0,L0,T0⦄ → IH_cnv_cpms_conf_lpr a h G0 L0 T0) →
     (∀G0,L0,T0. ⦃G,L,T1⦄ >[h] ⦃G0,L0,T0⦄ → IH_cnv_cpm_trans_lpr a h G0 L0 T0) →
     ∃∃n1,n2,T0. ⦃G, L⦄ ⊢ T1 ➡[n1,h] T0 & T1 ≛ T0 → ⊥ & ⦃G, L⦄ ⊢ T0 ➡*[n2,h] T2 & n1+n2 = n.
#a #h #n #G #L #T1 #T2 #H
@(cpms_ind_sn … H) -n -T1
[ #_ #H2T2 elim H2T2 -H2T2 //
| #n1 #n2 #T1 #T #H1T1 #H1T2 #IH #H0T1 #H2T12 #IH2 #IH1
  elim (tdeq_dec T1 T) #H2T1
  [ elim (tdeq_dec T T2) #H2T2
    [ -IH -IH2 -IH1 -H0T1 /4 width=7 by tdeq_trans, ex4_3_intro/
    | lapply (cnv_cpm_trans_lpr_aux … IH2 IH1 … H1T1 L ?) [6:|*: // ] -H1T2 -H2T12 #H0T
      elim (IH H0T H2T2) [|*: /4 width=5 by cpm_fpbq, fpbq_fpbg_trans/ ] -IH -IH2 -H0T -H2T2 (**)
      #m1 #m2 #T0 #H1T0 #H2T0 #H1T02 #H destruct
      elim (cnv_cpm_tdeq_cpm_trans_aux … IH1 … H0T1 … H1T1 H2T1 … H1T0) -IH1 -H0T1 -H1T1 -H1T0
      #T3 #H1T13 #H1T30 #H2T30
      @(ex4_3_intro … H1T13) /4 width=3 by cpms_step_sn, tdeq_canc_sn/ (**) (* explicit constructor *)
    ]
  | -IH -IH2 -IH1 -H2T12 /3 width=7 by tdeq_trans, ex4_3_intro/
  ]
]
qed-.

fact cpms_tdeq_ind_sn (a) (h) (G) (L) (T2) (Q:relation2 …):
     (⦃G, L⦄ ⊢ T2 ![a,h] → Q 0 T2) →
     (∀n1,n2,T1,T. ⦃G,L⦄ ⊢ T1 ➡[n1,h] T → ⦃G, L⦄ ⊢ T1 ![a,h] → T1 ≛ T → ⦃G, L⦄ ⊢ T ➡*[n2,h] T2 → ⦃G, L⦄ ⊢ T ![a,h] → T ≛ T2 → Q n2 T → Q (n1+n2) T1) →
     ∀n,T1. ⦃G, L⦄ ⊢ T1 ➡*[n,h] T2 → ⦃G, L⦄ ⊢ T1 ![a,h] → T1 ≛ T2 →
     (∀G0,L0,T0. ⦃G,L,T1⦄ >[h] ⦃G0,L0,T0⦄ → IH_cnv_cpms_conf_lpr a h G0 L0 T0) →
     (∀G0,L0,T0. ⦃G,L,T1⦄ >[h] ⦃G0,L0,T0⦄ → IH_cnv_cpm_trans_lpr a h G0 L0 T0) → 
     Q n T1.
#a #h #G #L #T2 #Q #IB1 #IB2 #n #T1 #H
@(cpms_ind_sn … H) -n -T1
[ -IB2 #H0T2 #_ #_ #_ /2 width=1 by/
| #n1 #n2 #T1 #T #H1T1 #H1T2 #IH #H0T1 #H2T12 #IH2 #IH1 -IB1
  elim (tdeq_dec T1 T) #H2T1
  [ lapply (cnv_cpm_trans_lpr_aux … IH2 IH1 … H1T1 L ?) [6:|*: // ] #H0T
    lapply (tdeq_canc_sn … H2T1 … H2T12) -H2T12 #H2T2
    /6 width=7 by cpm_fpbq, fpbq_fpbg_trans/ (**)
  | -IB2 -IH -IH2 -IH1
    elim (cnv_fpbg_refl_false … H0T1) -a -Q
    /3 width=8 by cpm_tdneq_cpm_cpms_tdeq_sym_fwd_fpbg/
  ]
]
qed-.
