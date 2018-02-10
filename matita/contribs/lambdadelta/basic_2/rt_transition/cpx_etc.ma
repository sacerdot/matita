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

include "basic_2/static/fle_drops.ma".
include "basic_2/static/fle_fqup.ma".
include "basic_2/static/fle_lsubf.ma".
include "basic_2/static/fle_fle.ma".
include "basic_2/static/lfxs_length.ma".
include "basic_2/rt_transition/cpx.ma".

(* UNCOUNTED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS *************)

(* Properties with context-sensitive free variables *************************)

(* Note: "⦃L2, T1⦄ ⊆ ⦃L0, T1⦄" may not hold *)
axiom cpx_lfxs_conf_fle: ∀R. c_reflexive … R →
                         ∀h,G,L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ⬈[h] T1 →
                         ∀L2. L0 ⪤*[R, T0] L2 →
                         ∧∧ ⦃L2, T0⦄ ⊆ ⦃L0, T0⦄ & ⦃L2, T1⦄ ⊆ ⦃L2, T0⦄
                          & ⦃L0, T1⦄ ⊆ ⦃L0, T0⦄.
(*
#R #HR #h #G #L0 #T0 @(fqup_wf_ind_eq (Ⓕ) … G L0 T0) -G -L0 -T0
#G #L #T #IH #G0 #L0 * *
[ #s #HG #HL #HT #X #HX #Y #HY destruct -IH
  lapply (lfxs_fwd_length … HY) -HY #H0
  elim (cpx_inv_sort1 … HX) -HX #H destruct
  /3 width=1 by fle_sort_length, and3_intro/
| * [| #i ] #HG #HL #HT #X #HX #Y #HY destruct
  [ elim (cpx_inv_zero1 … HX) -HX
    [ #H destruct
      elim (lfxs_inv_zero … HY) -HY *
      [ #H1 #H2 destruct -IH /2 width=1 by and3_intro/
      | #I #K0 #K2 #V0 #V2 #HK02 #HV02 #H1 #H2 destruct
        elim (IH … HK02) [4,5: /2 width=2 by fqu_fqup, fqu_lref_O/ ]
   
    lapply (lfxs_fwd_length … HY) -HY #H0
    /3 width=1 by fle_lref_length, and3_intro/
  | * #I0 #K0 #V0 #V1 #HLK0 #HV01 #HX  

  elim (lfxs_inv_lref … HY) -HY // #HV0 #HT0

| #l #HG #HL #HT #X #HX #Y #HY destruct -IH
  lapply (lfxs_fwd_length … HY) -HY #H0
  >(cpx_inv_gref1 … HX) -X
  /3 width=1 by fle_gref_length, and3_intro/
| #p #I #V0 #T0 #HG #HL #HT #X #HX #Y #HY destruct
  lapply (lfxs_fwd_length … HY) #H0
  elim (lfxs_inv_bind … V0 ? HY) -HY // #HV0 #HT0
  elim (cpx_inv_bind1 … HX) -HX *
  [ #V1 #T1 #HV01 #HT01 #H destruct
    elim (IH … HV01 … HV0) -HV01 -HV0 // #H1V #H2V #H3V
    elim (IH … HT01 … HT0) -HT01 -HT0 -IH // #H1T #H2T #H3T
    /4 width=3 by fle_bind_eq, fle_fwd_pair_sn, and3_intro/
  | #T #HT #HXT #H1 #H2 destruct
    elim (IH G0 … V0… V0 … HV0) -HV0 // #H1V #H2V #H3V
    elim (IH … HT … HT0) -HT -HT0 -IH // #H1T #H2T #H3T
    /3 width=5 by fle_bind, fle_inv_lifts_sn, and3_intro/
  ]
| #I #V0 #X0 #HG #HL #HT #X #HX #Y #HY destruct
  elim (lfxs_inv_flat … HY) -HY #HV0 #HX0
  elim (cpx_inv_flat1 … HX) -HX *
  [ #V1 #T1 #HV01 #HT01 #H destruct
    elim (IH … HV01 … HV0) -HV01 -HV0 // #H1V #H2V #H3V
    elim (IH … HT01 … HX0) -HT01 -HX0 -IH // #H1T #H2T #H3T
    /3 width=3 by fle_flat, and3_intro/
  | #HX #H destruct
    elim (IH G0 … V0… V0 … HV0) -HV0 // #H1V #H2V #H3V
    elim (IH … HX … HX0) -HX -HX0 -IH // #H1T #H2T #H3T
    /4 width=3 by fle_flat_sn, fle_flat_dx_dx, fle_flat_dx_sn, and3_intro/
  | #HX #H destruct
    elim (IH … HX … HV0) -HX -HV0 // #H1V #H2V #H3V
    elim (IH G0 … X0… X0 … HX0) -HX0 -IH // #H1T #H2T #H3T
    /4 width=3 by fle_flat_sn, fle_flat_dx_dx, fle_flat_dx_sn, and3_intro/
  | #p #V1 #W0 #W1 #T0 #T1 #HV01 #HW01 #HT01 #H1 #H2 #H3 destruct
    elim (lfxs_inv_bind … W0 ? HX0) -HX0 // #HW0 #HT0
    elim (IH … HV01 … HV0) -HV01 -HV0 // #H1V #H2V #H3V
    elim (IH … HW01 … HW0) -HW01 -HW0 // #H1W #H2W #H3W
    elim (IH … HT01 … HT0) -HT01 -HT0 -IH // #H1T #H2T #H3T
    lapply (fle_fwd_pair_sn … H2T) -H2T #H2T
    lapply (fle_fwd_pair_sn … H3T) -H3T #H3T
    @and3_intro [ /3 width=5 by fle_flat, fle_bind/ ] (**) (* full auto too slow *)
    @fle_bind_sn_ge /4 width=1 by fle_shift, fle_flat_sn, fle_flat_dx_dx, fle_flat_dx_sn, fle_bind_dx_sn/
  | #p #V1 #X1 #W0 #W1 #T0 #T1 #HV01 #HVX1 #HW01 #HT01 #H1 #H2 #H3 destruct
    elim (lfxs_inv_bind … W0 ? HX0) -HX0 // #HW0 #HT0
    elim (IH … HV01 … HV0) -HV01 -HV0 // #H1V #H2V #H3V
    elim (IH … HW01 … HW0) -HW01 -HW0 // #H1W #H2W #H3W
    elim (IH … HT01 … HT0) -HT01 -HT0 -IH // #H1T #H2T #H3T
    lapply (fle_fwd_pair_sn … H2T) -H2T #H2T
    lapply (fle_fwd_pair_sn … H3T) -H3T #H3T
    @and3_intro[ /3 width=5 by fle_flat, fle_bind/ ] (**) (* full auto too slow *)
    @fle_bind_sn_ge //
    [1,3: /3 width=1 by fle_flat_dx_dx, fle_bind_dx_sn/
    |2,4: /4 width=3 by fle_flat_sn, fle_flat_dx_sn, fle_flat_dx_dx, fle_shift, fle_lifts_sn/
    ]
  ]
]
*)