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
include "basic_2/static/fle_fle.ma".
include "basic_2/static/lfxs.ma".
include "basic_2/rt_transition/cpx.ma".

axiom fle_pair_sn: ∀L,V1,V2. ⦃L, V1⦄ ⊆ ⦃L, V2⦄ →
                   ∀I1,I2,T. ⦃L.ⓑ{I1}V1, T⦄ ⊆ ⦃L.ⓑ{I2}V2, T⦄.
(*
axiom fle_elim_flat: ∀L1,L2,V1,T2. ⦃L1, V1⦄ ⊆ ⦃L2, T2⦄ → ∀T1. ⦃L1, T1⦄ ⊆ ⦃L2, T2⦄ →
                     ∀I. ⦃L1, ⓕ{I}V1.T1⦄ ⊆ ⦃L2, T2⦄.

axiom fle_elim_bind: 
                     ∀p,I1,I2,J1,J2,L,V,W,T. ⦃L, ⓑ{p,I1}ⓕ{J1}V.W.T⦄ ⊆ ⦃L, ⓕ{J2}V.ⓑ{p,I2}W.T⦄.
*)
(* UNCOUNTED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS *************)

(* Properties with context-sensitive free variables *************************)

(* Note: "⦃L2, T1⦄ ⊆ ⦃L0, T1⦄" may not hold *)
axiom cpx_lfxs_conf_gen: ∀R. c_reflexive … R →
                         ∀h,G,L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ⬈[h] T1 →
                         ∀L2. L0 ⪤*[R, T0] L2 →
                         ∧∧ ⦃L2, T0⦄ ⊆ ⦃L0, T0⦄ & ⦃L2, T1⦄ ⊆ ⦃L2, T0⦄
                          & ⦃L0, T1⦄ ⊆ ⦃L0, T0⦄.
(*
#R #HR #h #G #L0 #T0 @(fqup_wf_ind_eq (Ⓕ) … G L0 T0) -G -L0 -T0
#G #L #T #IH #G0 #L0 * *
[ #s #HG #HL #HT #X #HX #Y #_ destruct -IH
  elim (cpx_inv_sort1 … HX) -HX #H destruct
  /2 width=1 by and3_intro/
|
| #l #HG #HL #HT #X #HX #Y #_ destruct -IH
  >(cpx_inv_gref1 … HX) -X
  /2 width=1 by and3_intro/
| #p #I #V0 #T0 #HG #HL #HT #X #HX #Y #HY destruct
  elim (lfxs_inv_bind … V0 ? HY) -HY // #HV0 #HT0
  elim (cpx_inv_bind1 … HX) -HX *
  [ #V1 #T1 #HV01 #HT01 #H destruct
    elim (IH … HV01 … HV0) -HV01 -HV0 // #H1V #H2V #H3V
    elim (IH … HT01 … HT0) -HT01 -HT0 -IH // #H1T #H2T #H3T
    /5 width=4 by fle_pair_sn, fle_trans, fle_bind, and3_intro/
  | #T #HT #HXT #H1 #H2 destruct
    elim (IH G0 … V0… V0 … HV0) -HV0 // #H1V #H2V #H3V
    elim (IH … HT … HT0) -HT -HT0 -IH // #H1T #H2T #H3T
    /4 width=7 by fle_bind_dx, fle_trans, fle_bind, and3_intro/
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
    /4 width=4 by fle_trans, fle_flat, and3_intro/
  | #HX #H destruct
    elim (IH … HX … HV0) -HX -HV0 // #H1V #H2V #H3V
    elim (IH G0 … X0… X0 … HX0) -HX0 -IH // #H1T #H2T #H3T
    /4 width=4 by fle_trans, fle_flat, and3_intro/
  | #p #V1 #W0 #W1 #T0 #T1 #HV01 #HW01 #HT01 #H1 #H2 #H3 destruct
    elim (lfxs_inv_bind … W0 ? HX0) -HX0 // #HW0 #HT0
    elim (IH … HV01 … HV0) -HV01 -HV0 // #H1V #H2V #H3V
    elim (IH … HW01 … HW0) -HW01 -HW0 // #H1W #H2W #H3W
    elim (IH … HT01 … HT0) -HT01 -HT0 -IH // #H1T #H2T #H3T
    @and3_intro
    [ /3 width=5 by fle_flat, fle_bind/
    | @(fle_trans)
      [4: @(fle_flat … H2V) [2: @(fle_bind … H2T) // | skip | @Appl ]
      |1,2: skip
      | @(fle_trans) [3: @fle_elim_bind  
    
     … H2T) // 
    
    // |1,2: skip
    | /2 width=1 by fle_bind_dx/      
*)
