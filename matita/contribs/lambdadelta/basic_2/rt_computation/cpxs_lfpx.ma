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

include "basic_2/rt_transition/lfpx_fsle.ma".
include "basic_2/rt_computation/cpxs_drops.ma".
include "basic_2/rt_computation/cpxs_cpxs.ma".

(* UNCOUNTED CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS ************)

(* Properties with uncounted parallel rt-transition on referred entries *****)

lemma lfpx_cpxs_conf: ∀h,G. s_r_confluent1 … (cpxs h G) (lfpx h G).
/3 width=5 by lfpx_cpx_conf, s_r_conf1_LTC1/ qed-.

lemma lfpx_cpx_trans: ∀h,G. s_r_transitive … (cpx h G) (lfpx h G).
#h #G #L2 #T1 #T2 #H @(cpx_ind … H) -G -L2 -T1 -T2 //
[ #G #L2 #s1 #L1 #H elim (lfpx_inv_sort … H) -H * /2 width=1 by cpx_cpxs/
| #I #G #L2 #V #V2 #W2 #_ #IH #HVW2 #Y1 #H
  elim (lfpx_inv_zero_pair_dx … H) -H #L1 #V1 #HL1 #HV1 #H destruct
  /5 width=3 by lfpx_cpx_conf, cpxs_delta, cpxs_strap2/
| #I2 #G #L2 #V2 #W2 #i #_ #IH #HVW2 #Y1 #H
  elim (lfpx_inv_lref_bind_dx … H) -H #I1 #L1 #HL1 #H destruct
  /4 width=3 by cpxs_lref, cpxs_strap2/
| #p #I #G #L2 #V #V2 #T #T2 #_ #_ #IHV #IHT #L1 #H
  elim (lfpx_inv_bind … H) -H /3 width=1 by cpxs_bind/
| #I #G #L2 #V #V2 #T #T2 #_ #_ #IHV #IHT #L1 #H
  elim (lfpx_inv_flat … H) -H /3 width=1 by cpxs_flat/
| #G #L2 #V #T #T2 #T0 #_ #IH #HT02 #L1 #H
  elim (lfpx_inv_bind … H) -H /3 width=3 by cpxs_zeta/
| #G #L2 #V #T #T2 #_ #IH #L1 #H
  elim (lfpx_inv_flat … H) -H /3 width=1 by cpxs_eps/
| #G #L2 #V #V2 #T #_ #IH #L1 #H
  elim (lfpx_inv_flat … H) -H /3 width=1 by cpxs_ee/
| #p #G #L2 #V #V2 #W #W2 #T #T2 #_ #_ #_ #IHV #IHW #IHT #L1 #H
  elim (lfpx_inv_flat … H) -H #HV #H
  elim (lfpx_inv_bind … H) -H /3 width=1 by cpxs_beta/
| #p #G #L2 #V #V2 #V0 #W #W2 #T #T2 #_ #_ #_ #IHV #IHW #IHT #HV20 #L1 #H
  elim (lfpx_inv_flat … H) -H #HV #H
  elim (lfpx_inv_bind … H) -H /3 width=3 by cpxs_theta/
]
qed.

lemma lfpx_cpxs_trans: ∀h,G. s_rs_transitive … (cpx h G) (lfpx h G).
/3 width=6 by lfpx_cpx_conf, lfpx_cpx_trans, s_r_trans_LTC1/
qed-.

(* Advanced properties ******************************************************)

lemma cpx_bind2: ∀h,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ⬈[h] V2 →
                 ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ⬈[h] T2 →
                 ∀p. ⦃G, L⦄ ⊢ ⓑ{p,I}V1.T1 ⬈*[h] ⓑ{p,I}V2.T2.
/4 width=5 by lfpx_cpx_trans, cpxs_bind_dx, lfpx_pair_refl/ qed.

lemma cpxs_bind2_dx: ∀h,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ⬈[h] V2 →
                     ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ⬈*[h] T2 →
                     ∀p. ⦃G, L⦄ ⊢ ⓑ{p,I}V1.T1 ⬈*[h] ⓑ{p,I}V2.T2.
/4 width=5 by lfpx_cpxs_trans, cpxs_bind_dx, lfpx_pair_refl/ qed.
