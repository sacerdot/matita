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

include "basic_2/rt_transition/rpx_reqx.ma".
include "basic_2/rt_computation/cpxs.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS *************)

(* Properties with sort-irrelevant equivalence for terms ********************)

lemma teqx_cpxs_trans (G) (L) (T):
      ∀T1. T1 ≛ T → ∀T2. ❪G,L❫ ⊢ T ⬈* T2 → ❪G,L❫ ⊢ T1 ⬈* T2.
#G #L #T #T1 #HT1 #T2 #HT2 @(cpxs_ind … HT2) -T2
[ /3 width=1 by teqx_cpx, cpx_cpxs/
| /2 width=3 by cpxs_strap1/
]
qed-.

(* Note: this requires teqx to be symmetric *)
(* Nasic_2A1: uses: cpxs_neq_inv_step_sn *)
lemma cpxs_tneqx_fwd_step_sn (G) (L):
      ∀T1,T2. ❪G,L❫ ⊢ T1 ⬈* T2 → (T1 ≛ T2 → ⊥) →
      ∃∃T. ❪G,L❫ ⊢ T1 ⬈ T & T1 ≛ T → ⊥ & ❪G,L❫ ⊢ T ⬈* T2.
#G #L #T1 #T2 #H @(cpxs_ind_dx … H) -T1
[ #H elim H -H //
| #T1 #T0 #HT10 #HT02 #IH #HnT12
  elim (teqx_dec T1 T0) [ -HT10 -HT02 #HT10 | -IH #HnT10 ]
  [ elim IH -IH /3 width=3 by teqx_trans/ -HnT12
    #T #HT0 #HnT0 #HT2
    lapply (teqx_cpx_trans … HT10 … HT0) -HT0 #HT1
    /4 width=4 by teqx_canc_sn, ex3_intro/
  | /3 width=4 by ex3_intro/
  ]
]
qed-.
