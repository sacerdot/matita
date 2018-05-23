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

include "basic_2/static/fsle_drops.ma".
include "basic_2/static/lfxs_fsle.ma".
include "basic_2/rt_transition/lfpx_length.ma".
include "basic_2/rt_transition/lfpx_fqup.ma".

(* UNBOUND PARALLEL RT-TRANSITION FOR REFERRED LOCAL ENVIRONMENTS ***********)

(* Forward lemmas with free variables inclusion for restricted closures *****)

(* Note: "⦃L2, T1⦄ ⊆ ⦃L2, T0⦄" does not hold *)
(* Note: Take L0 = K0.ⓓ(ⓝW.V), L2 = K0.ⓓW, T0 = #0, T1 = ⬆*[1]V *)
(* Note: This invalidates lfpxs_cpx_conf: "∀h,G. s_r_confluent1 … (cpx h G) (lfpxs h G)" *)
lemma lfpx_cpx_conf_fsge (h) (G): ∀L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ⬈[h] T1 →
                                  ∀L2. ⦃G, L0⦄ ⊢⬈[h, T0] L2 → ⦃L2, T1⦄ ⊆ ⦃L0, T0⦄.
#h #G0 #L0 #T0 @(fqup_wf_ind_eq (Ⓕ) … G0 L0 T0) -G0 -L0 -T0
#G #L #T #IH #G0 #L0 * *
[ #s #HG #HL #HT #X #HX #Y #HY destruct -IH
  elim (cpx_inv_sort1 … HX) -HX #H destruct
  lapply (lfpx_fwd_length … HY) -HY #H0
  /2 width=1 by fsle_sort_bi/
| * [| #i ] #HG #HL #HT #X #HX #Y #HY destruct
  [ elim (cpx_inv_zero1 … HX) -HX
    [ #H destruct
      elim (lfpx_inv_zero_length … HY) -HY *
      [ #H1 #H2 destruct -IH //
      | #I #K0 #K2 #V0 #V2 #HK02 #HV02 #H1 #H2 destruct
        lapply (lfpx_fwd_length … HK02) #H0
        /4 width=4 by fsle_pair_bi, fqu_fqup, fqu_lref_O/
      | #I #K0 #K2 #HK02 #H1 #H2 destruct -IH
        /2 width=1 by fsle_unit_bi/
      ]
    | * #I0 #K0 #V0 #V1 #HV01 #HV1X #H destruct
      elim (lfpx_inv_zero_pair_sn … HY) -HY #K2 #V2 #HK02 #HV02 #H destruct
      lapply (lfpx_fwd_length … HK02) #H0
      /4 width=4 by fsle_lifts_SO_sn, fqu_fqup, fqu_lref_O/
    ]
  | elim (cpx_inv_lref1 … HX) -HX
    [ #H destruct
      elim (lfpx_inv_lref … HY) -HY *
      [ #H0 #H1 destruct //
      | #I0 #I2 #K0 #K2 #HK02 #H1 #H2 destruct
        lapply (lfpx_fwd_length … HK02) #H0
        /4 width=5 by fsle_lifts_SO, fqu_fqup/
      ]
    | * #I0 #K0 #V1 #HV1 #HV1X #H0 destruct
      elim (lfpx_inv_lref_bind_sn … HY) -HY #I2 #K2 #HK02 #H destruct
      lapply (lfpx_fwd_length … HK02) #H0
      /4 width=5 by fsle_lifts_SO, fqu_fqup/
    ]
  ]
| #l #HG #HL #HT #X #HX #Y #HY destruct -IH
  >(cpx_inv_gref1 … HX) -X
  lapply (lfpx_fwd_length … HY) -HY #H0
  /2 width=1 by fsle_gref_bi/
| #p #I #V0 #T0 #HG #HL #HT #X #HX #Y #HY destruct
  elim (lfpx_inv_bind … V0 ? HY) -HY #HV0 #HT0
  elim (cpx_inv_bind1 … HX) -HX *
  [ #V1 #T1 #HV01 #HT01 #H destruct
    lapply (lfpx_fwd_length … HV0) #H0
    /4 width=6 by fsle_bind_eq, fsle_fwd_pair_sn/
  | #T #HT #HXT #H1 #H2 destruct
    lapply (lfpx_fwd_length … HV0) #H0
    /3 width=8 by fsle_inv_lifts_sn/
  ]
| #I #V0 #X0 #HG #HL #HT #X #HX #Y #HY destruct
  elim (lfxs_inv_flat … HY) -HY #HV0 #HX0
  elim (cpx_inv_flat1 … HX) -HX *
  [ #V1 #T1 #HV01 #HT01 #H destruct
    /3 width=4 by fsle_flat/
  | #HX #H destruct
    /4 width=4 by fsle_flat_dx_dx/
  | #HX #H destruct
    /4 width=4 by fsle_flat_dx_sn/
  | #p #V1 #W0 #W1 #T0 #T1 #HV01 #HW01 #HT01 #H1 #H2 #H3 destruct
    elim (lfpx_inv_bind … W0 ? HX0) -HX0 #HW0 #HT0
    lapply (lfpx_fwd_length … HV0) #H0
    lapply (IH … HV01 … HV0) -HV01 -HV0 // #HV
    lapply (IH … HW01 … HW0) -HW01 -HW0 // #HW
    lapply (IH … HT01 … HT0) -HT01 -HT0 -IH // #HT
    lapply (fsle_fwd_pair_sn … HT) -HT #HT
    @fsle_bind_sn_ge //
    [ /4 width=1 by fsle_flat_sn, fsle_flat_dx_dx, fsle_flat_dx_sn, fsle_bind_dx_sn/
    | /3 width=1 by fsle_flat_dx_dx, fsle_shift/
    ]
  | #p #V1 #X1 #W0 #W1 #T0 #T1 #HV01 #HVX1 #HW01 #HT01 #H1 #H2 #H3 destruct
    elim (lfpx_inv_bind … W0 ? HX0) -HX0 #HW0 #HT0
    lapply (lfpx_fwd_length … HV0) #H0
    lapply (IH … HV01 … HV0) -HV01 -HV0 // #HV
    lapply (IH … HW01 … HW0) -HW01 -HW0 // #HW
    lapply (IH … HT01 … HT0) -HT01 -HT0 -IH // #HT
    lapply (fsle_fwd_pair_sn … HT) -HT #HT
    @fsle_bind_sn_ge //
    [ /3 width=1 by fsle_flat_dx_dx, fsle_bind_dx_sn/
    | /4 width=3 by fsle_flat_sn, fsle_flat_dx_sn, fsle_flat_dx_dx, fsle_shift, fsle_lifts_sn/
    ]
  ]
]
qed-.

lemma lfpx_fsge_comp (h) (G): lfxs_fsge_compatible (cpx h G).
/2 width=4 by lfpx_cpx_conf_fsge/ qed-.

(**) (* this section concerns cpx *)
(* Properties with generic extension on referred entries ********************)

(* Basic_2A1: uses: cpx_frees_trans *)
lemma cpx_fsge_comp (h) (G): R_fsge_compatible (cpx h G).
/2 width=4 by lfpx_cpx_conf_fsge/ qed-.

(* Note: lemma 1000 *)
(* Basic_2A1: uses: cpx_llpx_sn_conf *)
lemma cpx_lfxs_conf (R) (h) (G): s_r_confluent1 … (cpx h G) (lfxs R).
/3 width=3 by fsge_lfxs_trans, cpx_fsge_comp/ qed-.

(* Advanced properties ******************************************************)

lemma lfpx_cpx_conf (h) (G): s_r_confluent1 … (cpx h G) (lfpx h G).
/2 width=5 by cpx_lfxs_conf/ qed-.

lemma lfpx_cpx_conf_fsge_dx (h) (G): ∀L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ⬈[h] T1 →
                                     ∀L2. ⦃G, L0⦄ ⊢⬈[h, T0] L2 → ⦃L2, T1⦄ ⊆ ⦃L0, T1⦄.
/3 width=5 by lfpx_cpx_conf, lfpx_fsge_comp/ qed-.
