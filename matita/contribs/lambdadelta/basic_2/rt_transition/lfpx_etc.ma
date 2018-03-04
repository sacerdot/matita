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
(*
lemma R_fle_comp_LTC: ∀R. R_fle_compatible R → R_fle_compatible (LTC … R).
#R #HR #L #T1 #T2 #H elim H -T2
/3 width=3 by fle_trans_dx/
qed-.
*)

(* Note: "⦃L2, T1⦄ ⊆ ⦃L0, T1⦄" may not hold *)
axiom lfpx_cpx_conf_fsle4: ∀h,G,L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ⬈[h] T1 →
                           ∀L2. ⦃G, L0⦄ ⊢⬈[h, T0] L2 → ⦃L2, T1⦄ ⊆ ⦃L0, T1⦄.
(*
#h #G0 #L0 #T0 @(fqup_wf_ind_eq (Ⓕ) … G0 L0 T0) -G0 -L0 -T0
#G #L #T #IH #G0 #L0 * *
[ #s #HG #HL #HT #X #HX #Y #HY destruct -IH
  lapply (lfxs_fwd_length … HY) -HY #H0
  elim (cpx_inv_sort1 … HX) -HX #H destruct
  /3 width=1 by fsle_sort_length, and3_intro/
| * [| #i ] #HG #HL #HT #X #HX #Y #HY destruct
  [ elim (cpx_inv_zero1 … HX) -HX
    [ #H destruct
      elim (lfxs_inv_zero … HY) -HY *
      [ #H1 #H2 destruct -IH /2 width=1 by and3_intro/
      | #I #K0 #K2 #V0 #V2 #HK02 #HV02 #H1 #H2 destruct
        lapply (lfxs_fwd_length … HK02) #HK
        elim H2R -H2R #H2R
        [ <(H2R G0) in HV02; -H2R #HV02
          elim (IH … HV02 … HK02) /2 width=2 by fqu_fqup, fqu_lref_O/ -IH -HV02 -HK02 #H1V #H2V #_
          /4 width=1 by fsle_trans_tc, fsle_zero_bi, and3_intro/
        | lapply (H2R … HV02 … HK02) -H2R -HV02 -HK02 -IH #HKV20
          /3 width=1 by fsle_zero_bi, and3_intro/
        ]
      | #f #I #K0 #K2 #Hf #HK02 #H1 #H2 destruct
      ]
    | * #I0 #K0 #V0 #V1 #HV01 #HV1X #H destruct
      elim (lfxs_inv_zero_pair_sn … HY) -HY #K2 #V2 #HK02 #HV02 #H destruct
    ]
  | elim (cpx_inv_lref1 … HX) -HX
    [ #H destruct
      elim (lfxs_inv_lref … HY) -HY *
      [ #H0 #H1 destruct /2 width=1 by and3_intro/
      | #I0 #I2 #K0 #K2 #HK02 #H1 #H2 destruct
        lapply (lfxs_fwd_length … HK02) #HK
        elim (IH … HK02) [|*: /2 width=4 by fqu_fqup/ ] -IH -HK02
        /3 width=5 by and3_intro, fsle_lifts_SO/
      ]
    | * #I0 #K0 #V1 #HV1 #HV1X #H0 destruct
      elim (lfxs_inv_lref_bind_sn … HY) -HY #I2 #K2 #HK02 #H destruct
      lapply (lfxs_fwd_length … HK02) #HK
      elim (IH … HK02) [|*: /2 width=4 by fqu_fqup/ ] -IH -HV1 -HK02
      /3 width=5 by fsle_lifts_SO, and3_intro/
    ]
  ]
| #l #HG #HL #HT #X #HX #Y #HY destruct -IH
  lapply (lfxs_fwd_length … HY) -HY #H0
  >(cpx_inv_gref1 … HX) -X
  /3 width=1 by fsle_gref_length, and3_intro/
| #p #I #V0 #T0 #HG #HL #HT #X #HX #Y #HY destruct
  lapply (lfxs_fwd_length … HY) #H0
  elim (lfxs_inv_bind … V0 ? HY) -HY // #HV0 #HT0
  elim (cpx_inv_bind1 … HX) -HX *
  [ #V1 #T1 #HV01 #HT01 #H destruct
    elim (IH … HV01 … HV0) -HV01 -HV0 // #H1V #H2V #H3V
    elim (IH … HT01 … HT0) -HT01 -HT0 -IH // #H1T #H2T #H3T
    /4 width=3 by fsle_bind_eq, fsle_fwd_pair_sn, and3_intro/
  | #T #HT #HXT #H1 #H2 destruct
    elim (IH G0 … V0… V0 … HV0) -HV0 // #H1V #H2V #H3V
    elim (IH … HT … HT0) -HT -HT0 -IH // #H1T #H2T #H3T
    /3 width=5 by fsle_bind, fsle_inv_lifts_sn, and3_intro/
  ]
| #I #V0 #X0 #HG #HL #HT #X #HX #Y #HY destruct
  elim (lfxs_inv_flat … HY) -HY #HV0 #HX0
  elim (cpx_inv_flat1 … HX) -HX *
  [ #V1 #T1 #HV01 #HT01 #H destruct
    elim (IH … HV01 … HV0) -HV01 -HV0 // #H1V #H2V #H3V
    elim (IH … HT01 … HX0) -HT01 -HX0 -IH // #H1T #H2T #H3T
    /3 width=3 by fsle_flat, and3_intro/
  | #HX #H destruct
    elim (IH G0 … V0… V0 … HV0) -HV0 // #H1V #H2V #H3V
    elim (IH … HX … HX0) -HX -HX0 -IH // #H1T #H2T #H3T
    /4 width=3 by fsle_flat_sn, fsle_flat_dx_dx, fsle_flat_dx_sn, and3_intro/
  | #HX #H destruct
    elim (IH … HX … HV0) -HX -HV0 // #H1V #H2V #H3V
    elim (IH G0 … X0… X0 … HX0) -HX0 -IH // #H1T #H2T #H3T
    /4 width=3 by fsle_flat_sn, fsle_flat_dx_dx, fsle_flat_dx_sn, and3_intro/
  | #p #V1 #W0 #W1 #T0 #T1 #HV01 #HW01 #HT01 #H1 #H2 #H3 destruct
    elim (lfxs_inv_bind … W0 ? HX0) -HX0 // #HW0 #HT0
    elim (IH … HV01 … HV0) -HV01 -HV0 // #H1V #H2V #H3V
    elim (IH … HW01 … HW0) -HW01 -HW0 // #H1W #H2W #H3W
    elim (IH … HT01 … HT0) -HT01 -HT0 -IH // #H1T #H2T #H3T
    lapply (fsle_fwd_pair_sn … H2T) -H2T #H2T
    lapply (fsle_fwd_pair_sn … H3T) -H3T #H3T
    @and3_intro [ /3 width=5 by fsle_flat, fsle_bind/ ] (**) (* full auto too slow *)
    @fsle_bind_sn_ge /4 width=1 by fsle_shift, fsle_flat_sn, fsle_flat_dx_dx, fsle_flat_dx_sn, fsle_bind_dx_sn/
  | #p #V1 #X1 #W0 #W1 #T0 #T1 #HV01 #HVX1 #HW01 #HT01 #H1 #H2 #H3 destruct
    elim (lfxs_inv_bind … W0 ? HX0) -HX0 // #HW0 #HT0
    elim (IH … HV01 … HV0) -HV01 -HV0 // #H1V #H2V #H3V
    elim (IH … HW01 … HW0) -HW01 -HW0 // #H1W #H2W #H3W
    elim (IH … HT01 … HT0) -HT01 -HT0 -IH // #H1T #H2T #H3T
    lapply (fsle_fwd_pair_sn … H2T) -H2T #H2T
    lapply (fsle_fwd_pair_sn … H3T) -H3T #H3T
    @and3_intro[ /3 width=5 by fsle_flat, fsle_bind/ ] (**) (* full auto too slow *)
    @fsle_bind_sn_ge //
    [1,3: /3 width=1 by fsle_flat_dx_dx, fsle_bind_dx_sn/
    |2,4: /4 width=3 by fsle_flat_sn, fsle_flat_dx_sn, fsle_flat_dx_dx, fsle_shift, fsle_lifts_sn/
    ]
  ]
]
*)
