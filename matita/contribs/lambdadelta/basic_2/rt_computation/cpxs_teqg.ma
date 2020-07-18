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

include "basic_2/rt_transition/rpx_reqg.ma".
include "basic_2/rt_computation/cpxs.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS *************)

(* Properties with generic equivalence for terms ****************************)

lemma teqg_cpxs_trans (S) (G) (L) (T):
      reflexive … S → symmetric … S →
      ∀T1. T1 ≛[S] T → ∀T2. ❪G,L❫ ⊢ T ⬈* T2 → ❪G,L❫ ⊢ T1 ⬈* T2.
#S #H1S #H2S #G #L #T #T1 #HT1 #T2 #HT2 @(cpxs_ind … HT2) -T2
[ /3 width=4 by teqg_cpx, cpx_cpxs/
| /2 width=3 by cpxs_strap1/
]
qed-.

(* Note: this requires teqg to be symmetric *)
(* Nasic_2A1: uses: cpxs_neq_inv_step_sn *)
lemma cpxs_tneqg_fwd_step_sn (S) (G) (L):
      reflexive … S → symmetric … S → Transitive … S →
      (∀s1,s2. Decidable (S s1 s2)) →
      ∀T1,T2. ❪G,L❫ ⊢ T1 ⬈* T2 → (T1 ≛[S] T2 → ⊥) →
      ∃∃T. ❪G,L❫ ⊢ T1 ⬈ T & T1 ≛[S] T → ⊥ & ❪G,L❫ ⊢ T ⬈* T2.
#S #G #L #H1S #H2S #H3S #H4S #T1 #T2 #H @(cpxs_ind_dx … H) -T1
[ #H elim H -H /2 width=1 by teqg_refl/
| #T1 #T0 #HT10 #HT02 #IH #HnT12
  elim (teqg_dec S … T1 T0) // [ -HT10 -HT02 #HT10 | -IH #HnT10 ]
  [ elim IH -IH /3 width=3 by teqg_trans/ -HnT12
    #T #HT0 #HnT0 #HT2
    lapply (teqg_cpx_trans … HT10 … HT0) // -HT0 #HT1
    /4 width=4 by teqg_canc_sn, ex3_intro/
  | /3 width=4 by ex3_intro/
  ]
]
qed-.
