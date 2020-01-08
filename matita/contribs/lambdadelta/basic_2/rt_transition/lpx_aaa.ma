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

include "static_2/static/aaa_drops.ma".
include "static_2/static/lsuba_aaa.ma".
include "basic_2/rt_transition/lpx_drops.ma".

(* UNBOUND PARALLEL RT-TRANSITION FOR FULL LOCAL ENVIRONMENTS ***************)

(* Properties with atomic arity assignment for terms ************************)

(* Note: lemma 500 *)
(* Basic_2A1: was: cpx_lpx_aaa_conf *)
lemma cpx_aaa_conf_lpx (h): ∀G,L1,T1,A. ❪G,L1❫ ⊢ T1 ⁝ A →
                            ∀T2. ❪G,L1❫ ⊢ T1 ⬈[h] T2 →
                            ∀L2. ❪G,L1❫ ⊢ ⬈[h] L2 → ❪G,L2❫ ⊢ T2 ⁝ A.
#h #G #L1 #T1 #A #H elim H -G -L1 -T1 -A
[ #G #L1 #s #X #H
  elim (cpx_inv_sort1 … H) -H #H destruct //
| #I #G #K1 #V1 #B #_ #IH #X #HX #Y #HY
  elim (lpx_inv_pair_sn … HY) -HY #K2 #V2 #HK12 #HV12 #H destruct
  elim (cpx_inv_zero1_pair … HX) -HX
  [ #H destruct /3 width=1 by aaa_zero/
  | * #V #HV1 #HVX -HV12
    /4 width=7 by aaa_lifts, drops_refl, drops_drop, true/
  ]
| #I1 #G #K1 #A #i #_ #IH #X #HX #Y #HY
  elim (lpx_inv_bind_sn … HY) -HY #I2 #K2 #HK12 #_ #H destruct
  elim (cpx_inv_lref1_bind … HX) -HX
  [ #H destruct /3 width=1 by aaa_lref/
  | * #T #HT #HTX
    /4 width=7 by aaa_lifts, drops_refl, drops_drop, true/
  ]
| #p #G #L1 #V1 #T1 #B #A #_ #_ #IHV1 #IHT1 #X #H #L2 #HL12
  elim (cpx_inv_abbr1 … H) -H *
  [ #V2 #T2 #HV12 #HT12 #H destruct /4 width=2 by lpx_pair, aaa_abbr/
  | #X1 #HXT1 #HX1 #H destruct -IHV1
    elim (cpx_lifts_sn … HX1 (Ⓣ) … (L1.ⓓV1) … HXT1) -X1
    /4 width=7 by lpx_pair, aaa_inv_lifts, drops_refl, drops_drop/
  ]
| #p #G #L1 #V1 #T1 #B #A #_ #_ #IHV1 #IHT1 #X #H #L2 #HL12
  elim (cpx_inv_abst1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  /4 width=1 by lpx_pair, aaa_abst/
| #G #L1 #V1 #T1 #B #A #_ #_ #IHV1 #IHT1 #X #H #L2 #HL12
  elim (cpx_inv_appl1 … H) -H *
  [ #V2 #T2 #HV12 #HT12 #H destruct /3 width=3 by aaa_appl/
  | #q #V2 #W1 #W2 #U1 #U2 #HV12 #HW12 #HU12 #H1 #H2 destruct
    lapply (IHV1 … HV12 … HL12) -IHV1 -HV12 #HV2
    lapply (IHT1 (ⓛ[q]W2.U2) … HL12) -IHT1 /2 width=1 by cpx_bind/ -L1 #H
    elim (aaa_inv_abst … H) -H #B0 #A0 #HW1 #HU2 #H destruct
    /5 width=6 by lsuba_aaa_trans, lsuba_beta, aaa_abbr, aaa_cast/
  | #q #V #V2 #W1 #W2 #U1 #U2 #HV1 #HV2 #HW12 #HU12 #H1 #H2 destruct
    lapply (aaa_lifts G L2 … B … (L2.ⓓW2) … HV2) -HV2 /3 width=2 by drops_refl, drops_drop/ #HV2
    lapply (IHT1 (ⓓ[q]W2.U2) … HL12) -IHT1 /2 width=1 by cpx_bind/ -L1 #H
    elim (aaa_inv_abbr … H) -H /3 width=3 by aaa_abbr, aaa_appl/
  ]
| #G #L1 #V1 #T1 #A #_ #_ #IHV1 #IHT1 #X #H #L2 #HL12
  elim (cpx_inv_cast1 … H) -H
  [ * #V2 #T2 #HV12 #HT12 #H destruct /3 width=1 by aaa_cast/
  | -IHV1 /2 width=1 by/
  | -IHT1 /2 width=1 by/
  ]
]
qed-.

lemma cpx_aaa_conf (h): ∀G,L. Conf3 … (aaa G L) (cpx h G L).
/2 width=7 by cpx_aaa_conf_lpx/ qed-.

lemma lpx_aaa_conf (h): ∀G,T. Conf3 … (λL. aaa G L T) (lpx h G).
/2 width=7 by cpx_aaa_conf_lpx/ qed-.
