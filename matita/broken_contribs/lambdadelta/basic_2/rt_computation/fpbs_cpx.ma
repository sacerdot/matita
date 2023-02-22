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

include "basic_2/rt_computation/lpxs_cpxs.ma".
include "basic_2/rt_computation/fpbs_lpxs.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Properties with extended context-sensitive parallel rt-transition ********)

(* Basic_2A1: uses: fpbs_cpx_trans_neq *)
lemma fpbs_cpx_tneqg_trans (S):
      reflexive … S → symmetric … S → Transitive … S →
      (∀s1,s2. Decidable (S s1 s2)) →
      ∀G1,G2,L1,L2,T1,T2. ❨G1,L1,T1❩ ≥ ❨G2,L2,T2❩ →
      ∀U2. ❨G2,L2❩ ⊢ T2 ⬈ U2 → (T2 ≛[S] U2 → ⊥) →
      ∃∃U1. ❨G1,L1❩ ⊢ T1 ⬈ U1 & T1 ≛[S] U1 → ⊥ & ❨G1,L1,U1❩ ≥ ❨G2,L2,U2❩.
#S #H1S #H2S #H3S #H4S #G1 #G2 #L1 #L2 #T1 #T2 #H #U2 #HTU2 #HnTU2
elim (fpbs_inv_star S … H) -H // #G0 #L0 #L3 #T0 #T3 #HT10 #H10 #HL03 #H32
lapply (feqg_cpx_trans_cpx … H32 … HTU2) // #HTU32
lapply (feqg_tneqg_trans … H32 … HnTU2) -HnTU2 // #HnTU34
lapply (feqg_cpx_trans_feqg … H32 … HTU2) // -T2 #H32
lapply (lpxs_cpx_trans … HTU32 … HL03) -HTU32 #HTU32
elim (fqus_cpxs_trans_tneqg … H10 … HTU32 HnTU34) -T3 #T2 #HT02 #HnT02 #H2
elim (teqg_dec S … T1 T0) [ #H10 | -HnT02 #HnT10 | // ]
[ lapply (cpxs_trans … HT10 … HT02) -HT10 -HT02 #HT12
  elim (cpxs_tneqg_fwd_step_sn … HT12)
  [2,7: /3 width=3 by teqg_canc_sn/ ] -T0 -HT12 /2 width=1 by sfull_dec/
  /3 width=15 by fpbs_intro_star, ex3_intro/
| elim (cpxs_tneqg_fwd_step_sn … HT10 … HnT10) -HT10 -HnT10 /2 width=1 by sfull_dec/
  /4 width=15 by fpbs_intro_star, cpxs_trans, ex3_intro/
]
qed-.
