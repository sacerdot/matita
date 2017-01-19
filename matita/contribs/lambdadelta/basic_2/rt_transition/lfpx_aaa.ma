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

include "basic_2/static/aaa_drops.ma".
include "basic_2/static/lsuba_aaa.ma".
include "basic_2/rt_transition/lfpx_fqup.ma".

(* UNCOUNTED PARALLEL RT-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES *****)

(* Properties with atomic arity assignment for terms ************************)

(* Note: lemma 500 *)
(* Basic_2A1: was: cpx_lpx_aaa_conf *)
lemma cpx_aaa_conf_lfpx: ∀h,G,L1,T1,A. ⦃G, L1⦄ ⊢ T1 ⁝ A →
                         ∀T2. ⦃G, L1⦄ ⊢ T1 ⬈[h] T2 →
                         ∀L2. ⦃G, L1⦄ ⊢ ⬈[h, T1] L2 → ⦃G, L2⦄ ⊢ T2 ⁝ A.
#h #G #L1 #T1 #A #H elim H -G -L1 -T1 -A
[ #G #L1 #s #X2 #HX
  elim (cpx_inv_sort1 … HX) -HX //
| #I #G #L1 #V1 #B #_ #IH #X2 #HX #Y #HY
  elim (lfpx_inv_zero_pair_sn … HY) -HY #L2 #V2 #HL12 #HV12 #H destruct
  elim (cpx_inv_zero1_pair … HX) -HX
  [ #H destruct /3 width=1 by aaa_zero/
  | -HV12 * /4 width=7 by aaa_lifts, drops_refl, drops_drop/
  ]
| #I #G #L1 #V1 #B #i #_ #IH #X2 #HX #Y #HY
  elim (lfpx_inv_lref_pair_sn … HY) -HY #L2 #W2 #HL12 #H destruct
  elim (cpx_inv_lref1_pair … HX) -HX
  [ #H destruct /3 width=1 by aaa_lref/
  | * /4 width=7 by aaa_lifts, drops_refl, drops_drop/
  ]
| #p #G #L1 #V1 #T1 #B #A #_ #_ #IHV #IHT #X2 #HX #L2 #HL12
  elim (lfpx_inv_bind … HL12) -HL12 #HV #HT
  elim (cpx_inv_abbr1 … HX) -HX *
  [ #V2 #T2 #HV12 #HT12 #H destruct
    /4 width=2 by lfpx_pair_repl_dx, aaa_abbr/
  | #T2 #HT12 #HXT2 #H destruct -IHV
    /4 width=7 by aaa_inv_lifts, drops_drop, drops_refl/
  ]
| #p #G #L1 #V1 #T1 #B #A #_ #_ #IHV #IHT #X2 #H #L2 #HL12
  elim (lfpx_inv_bind … HL12) -HL12 #HV #HT
  elim (cpx_inv_abst1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  /4 width=2 by lfpx_pair_repl_dx, aaa_abst/
| #G #L1 #V1 #T1 #B #A #_ #_ #IHV #IHT #X2 #H #L2 #HL12
  elim (lfpx_inv_flat … HL12) -HL12 #HV #HT
  elim (cpx_inv_appl1 … H) -H *
  [ #V2 #T2 #HV12 #HT12 #H destruct /3 width=3 by aaa_appl/
  | #q #V2 #W1 #W2 #U1 #U2 #HV12 #HW12 #HU12 #H1 #H2 destruct
    lapply (IHV … HV12 … HV) -IHV -HV12 -HV #HV2
    lapply (IHT (ⓛ{q}W2.U2) … HT) -IHT -HT /2 width=1 by cpx_bind/ -L1 #H
    elim (aaa_inv_abst … H) -H #B0 #A0 #HW1 #HU2 #H destruct
    /5 width=6 by lsuba_aaa_trans, lsuba_beta, aaa_abbr, aaa_cast/
  | #q #V #V2 #W1 #W2 #U1 #U2 #HV1 #HV2 #HW12 #HU12 #H1 #H2 destruct
    lapply (aaa_lifts G L2 … B … (L2.ⓓW2) … HV2) -HV2 /3 width=2 by drops_drop, drops_refl/ #HV2
    lapply (IHT (ⓓ{q}W2.U2) … HT) -IHT -HT /2 width=1 by cpx_bind/ -L1 #H
    elim (aaa_inv_abbr … H) -H /3 width=3 by aaa_abbr, aaa_appl/
  ]
| #G #L1 #V1 #T1 #A #_ #_ #IHV #IHT #X2 #HX #L2 #HL12
  elim (lfpx_inv_flat … HL12) -HL12 #HV #HT
  elim (cpx_inv_cast1 … HX) -HX
  [ * #V2 #T2 #HV12 #HT12 #H destruct ] /3 width=1 by aaa_cast/
]
qed-.

lemma cpx_aaa_conf: ∀h,G,L,T1,A. ⦃G, L⦄ ⊢ T1 ⁝ A →
                    ∀T2. ⦃G, L⦄ ⊢ T1 ⬈[h] T2 → ⦃G, L⦄ ⊢ T2 ⁝ A.
/2 width=6 by cpx_aaa_conf_lfpx/ qed-.

lemma lfpx_aaa_conf: ∀h,G,L1,T,A. ⦃G, L1⦄ ⊢ T ⁝ A →
                     ∀L2. ⦃G, L1⦄ ⊢ ⬈[h, T] L2 → ⦃G, L2⦄ ⊢ T ⁝ A.
/2 width=6 by cpx_aaa_conf_lfpx/ qed-.
