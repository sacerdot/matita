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

include "static_2/relocation/lifts_tueq.ma".
include "basic_2/rt_transition/cpm.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Properties with tail sort-irrelevant equivalence on terms ****************)

lemma cpm_tueq_conf (h) (n) (G) (L) (T0):
      ∀T1.  ⦃G,L⦄ ⊢ T0 ➡[n,h] T1 → ∀T2. T0 ≅ T2 →
      ∃∃T. ⦃G,L⦄ ⊢ T2 ➡[n,h] T & T1 ≅ T.
#h #n #G #L #T0 #T1 #H @(cpm_ind … H) -G -L -T0 -T1 -n
[ /2 width=3 by ex2_intro/
| #G #L #s0 #X2 #H2
  elim (tueq_inv_sort1 … H2) -H2 #s2 #H destruct
  /3 width=3 by tueq_sort, ex2_intro/
| #n #G #K0 #V0 #V1 #W1 #_ #IH #HVW1 #X2 #H2
  >(tueq_inv_lref1 … H2) -X2
  elim (IH V0) [| // ] -IH #V #HV0 #HV1
  elim (tueq_lifts_sn … HV1 … HVW1) -V1
  /3 width=3 by cpm_delta, ex2_intro/
| #n #G #K0 #V0 #V1 #W1 #_ #IH #HVW1 #X2 #H2
  >(tueq_inv_lref1 … H2) -X2
  elim (IH V0) [| // ] -IH #V #HV0 #HV1
  elim (tueq_lifts_sn … HV1 … HVW1) -V1
  /3 width=3 by cpm_ell, ex2_intro/
| #n #I #G #K0 #V1 #W1 #i #_ #IH #HVW1 #X2 #H2
  >(tueq_inv_lref1 … H2) -X2
  elim (IH (#i)) [| // ] -IH #V #HV0 #HV1
  elim (tueq_lifts_sn … HV1 … HVW1) -V1
  /3 width=3 by cpm_lref, ex2_intro/
| #n #p #I #G #L #V0 #V1 #T0 #T1 #HV01 #_ #_ #IHT #X2 #H2
  elim (tueq_inv_bind1 … H2) -H2 #T2 #HT02 #H destruct
  elim (IHT … HT02) -T0 #T #HT2 #HT1
  /3 width=3 by cpm_bind, tueq_bind, ex2_intro/
| #n #G #L #V0 #V1 #T0 #T1 #HV10 #_ #_ #IHT #X2 #H2
  elim (tueq_inv_appl1 … H2) -H2 #T2 #HT02 #H destruct
  elim (IHT … HT02) -T0 #T #HT2 #HT1
  /3 width=3 by cpm_appl, tueq_appl, ex2_intro/
| #n #G #L #V0 #V1 #T0 #T1 #_ #_ #IHV #IHT #X2 #H2
  elim (tueq_inv_cast1 … H2) -H2 #V2 #T2 #HV02 #HT02 #H destruct
  elim (IHV … HV02) -V0 #V #HV2 #HV1
  elim (IHT … HT02) -T0 #T #HT2 #HT1
  /3 width=5 by cpm_cast, tueq_cast, ex2_intro/
| #n #G #L #V0 #U0 #T0 #T1 #HTU0 #_ #IH #X2 #H2
  elim (tueq_inv_bind1 … H2) -H2 #U2 #HU02 #H destruct
  elim (tueq_inv_lifts_sn … HU02 … HTU0) -U0 #T2 #HTU2 #HT02
  elim (IH … HT02) -T0 #T #HT2 #HT1
  /3 width=3 by cpm_zeta, ex2_intro/
| #n #G #L #V0 #T0 #T1 #_ #IH #X2 #H2
  elim (tueq_inv_cast1 … H2) -H2 #V2 #T2 #_ #HT02 #H destruct
  elim (IH … HT02) -V0 -T0
  /3 width=3 by cpm_eps, ex2_intro/
| #n #G #L #V0 #T0 #T1 #_ #IH #X2 #H2
  elim (tueq_inv_cast1 … H2) -H2 #V2 #T2 #HV02 #_ #H destruct
  elim (IH … HV02) -V0 -T1
  /3 width=3 by cpm_ee, ex2_intro/
| #n #p #G #L #V0 #V1 #W0 #W1 #T0 #T1 #HV01 #HW01 #_ #_ #_ #IHT #X2 #H2
  elim (tueq_inv_appl1 … H2) -H2 #X #H2 #H destruct
  elim (tueq_inv_bind1 … H2) -H2 #T2 #HT02 #H destruct
  elim (IHT … HT02) -T0
  /4 width=3 by cpm_beta, tueq_cast, tueq_bind, ex2_intro/
| #n #p #G #L #V0 #V1 #U1 #W0 #W1 #T0 #T1 #HV01 #HW01 #_ #_ #_ #IHT #HVU1 #X2 #H2
  elim (tueq_inv_appl1 … H2) -H2 #X #H2 #H destruct
  elim (tueq_inv_bind1 … H2) -H2 #T2 #HT02 #H destruct
  elim (IHT … HT02) -T0 #T #HT2 #HT1
  /4 width=3 by cpm_theta, tueq_appl, tueq_bind, ex2_intro/
]
qed-.

lemma tueq_cpm_trans (h) (n) (G) (L) (T0):
      ∀T1. T1 ≅ T0 → ∀T2.  ⦃G,L⦄ ⊢ T0 ➡[n,h] T2 →
      ∃∃T. ⦃G,L⦄ ⊢ T1 ➡[n,h] T & T ≅ T2.
#h #n #G #L #T0 #T1 #HT10 #T2 #HT02
elim (cpm_tueq_conf … HT02 T1)
/3 width=3 by tueq_sym, ex2_intro/
qed-.
