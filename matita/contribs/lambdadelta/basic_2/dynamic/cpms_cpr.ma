
include "basic_2/rt_computation/cpms_lpr.ma".
(*
lemma cpm_lsubr_trans (h) (n) (G) (L1) (T1):
      ∀T2. ⦃G,L1⦄ ⊢ T1 ➡[↑n,h] T2 → ∀L2. L1 ⫃ L2 →
      ∃∃T0. ⦃G,L2⦄ ⊢ T1 ➡[↑n,h] T0 & ⦃G,L2⦄ ⊢ T0 ➡*[h] T2.
#h #m #G #L1 #T1 #T2
@(insert_eq_0 … (↑m)) #n #H
@(cpm_ind … H) -n -G -L1 -T1 -T2
[ 
|
| #n #G #K1 #V1 #V2 #W2 #_ #IH #HVW2 #Hm #L2 #H destruct
  elim (lsubr_inv_bind1 … H) -H *
  [ #K2 #HK #H destruct
    elim (IH … HK) -K1 [| // ] #V0 #HV10 #HV02
    elim (lifts_total V0 (𝐔❴1❵)) #W0 #HVW0
    lapply (cpms_lifts_bi … HV02 (Ⓣ) … (K2.ⓓV1) … HVW0 … HVW2) -V2
    [ /3 width=2 by drops_refl, drops_drop/ ] #HW02
    /3 width=3 by cpm_delta, ex2_intro/
  | #K2 #VX #WX #HK #H1 #H2 destruct
    elim (IH … HK) -K1 [| // ] #X0 #H1 #H2
    elim (cpm_inv_cast1 … H1) -H1 [ * || * ]
    [ #W0 #V0 #HW0 #HV0 #H destruct
        @(ex2_intro … (#0)) [ // | 
  | #I1 #I2 #K2 #VX #HK #H1 #H2 destruct   
    
|
|
| #n #p #I #G #L1 #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #L2 #HL
  elim (IHV … HL) -IHV #V0 #HV01 #HV02
  elim (IHT (L2.ⓑ{I}V1)) [| /2 width=1 by lsubr_bind/ ] -L1 #T0 #HT10 #HT02
  @(ex2_intro … (ⓑ{p,I}V1.T0)) /3 width=3 by cprs_step_sn, cpms_bind, cpm_bind/ (**) (* full auto a bit slow *)
| 
|
|  //   
*)
(*
lemma cpr_cpm_trans_swap_lsubr_lpr (h) (G) (L1) (T1):
      ∀T. ⦃G,L1⦄ ⊢ T1 ➡[h] T → ∀L. L ⫃ L1 →
      ∀L2. ⦃G,L⦄ ⊢ ➡[h] L2 → ∀n2,T2. ⦃G,L2⦄ ⊢ T ➡[n2,h] T2 →
      ∃∃T0. ⦃G,L⦄ ⊢ T1 ➡[n2,h] T0 & ⦃G,L⦄ ⊢ T0 ➡*[h] T2.
#h #G #L1 #T1 @(fqup_wf_ind_eq (Ⓣ) … G L1 T1) -G -L1 -T1
#G0 #L0 #T0 #IH #G #L1 * [| * [| * ]]
[ (*
  #I #HG #HL #HT #X #H1 #L2 #HL12 #m2 #X2 #H2 destruct
  elim (cpr_inv_atom1 … H1) -H1 [|*: * ]
  [ #H destruct
    elim (cpm_inv_atom1 … H2) -H2 *
    [ #H1 #H2 destruct /3 width=3 by cpm_cpms, ex2_intro/
    | #s #H1 #H2 #H3 destruct /2 width=3 by ex2_intro/
    | #K2 #V #V2 #HV2 #HVT2 #H1 #H2 destruct
      elim (lpr_inv_pair_dx … HL12) -HL12 #K1 #V1 #HK12 #HV1 #H destruct
      elim (IH … HV1 … HK12 … HV2) -K2 -V -IH
      [| /2 width=1 by fqu_fqup, fqu_lref_O/ ] #V0 #HV10 #HV02
      elim (lifts_total V0 (𝐔❴1❵)) #T0 #HVT0
      lapply (cpms_lifts_bi … HV02 (Ⓣ) … (K1.ⓓV1) … HVT0 … HVT2) -V2
      [ /3 width=2 by drops_refl, drops_drop/ ] #HT02
      /3 width=3 by cpm_delta, ex2_intro/
    | #n2 #K2 #W #W2 #HW2 #HWT2 #H1 #H2 #H3 destruct
      elim (lpr_inv_pair_dx … HL12) -HL12 #K1 #W1 #HK12 #HW1 #H destruct
      elim (IH … HW1 … HK12 … HW2) -K2 -W -IH
      [| /2 width=1 by fqu_fqup, fqu_lref_O/ ] #W0 #HW10 #HW02
      elim (lifts_total W0 (𝐔❴1❵)) #T0 #HWT0
      lapply (cpms_lifts_bi … HW02 (Ⓣ) … (K1.ⓛW1) … HWT0 … HWT2) -W2
      [ /3 width=2 by drops_refl, drops_drop/ ] #HT02
      /3 width=3 by cpm_ell, ex2_intro/
    | #I2 #K2 #T2 #i #HT2 #HTU2 #H1 #H2 destruct
      elim (lpr_inv_bind_dx … HL12) -HL12 #I1 #K1 #HK12 #_ #H destruct
      elim (IH … (#i) … HK12 … HT2) -I2 -K2 -IH
      [|*: /2 width=1 by fqu_fqup/ ] #T0 #HT10 #HT02
      elim (lifts_total T0 (𝐔❴1❵)) #U0 #HTU0
      lapply (cpms_lifts_bi … HT02 (Ⓣ) … (K1.ⓘ{I1}) … HTU0 … HTU2) -T2
      [ /3 width=2 by drops_refl, drops_drop/ ] #HU02
      /3 width=3 by cpm_lref, ex2_intro/
    ]
  | #K1 #V1 #V #HV1 #HVT #H1 #H2 destruct
    elim (lpr_inv_pair_sn … HL12) -HL12 #K2 #V0 #HK12 #_ #H destruct
    elim (cpm_inv_lifts_sn … H2 (Ⓣ) … HVT) -X
    [|*: /3 width=2 by drops_refl, drops_drop/ ] -V0 #V2 #HVT2 #HV2
    elim (IH … HV1 … HK12 … HV2) -K2 -V -IH
    [| /2 width=1 by fqu_fqup, fqu_lref_O/ ] #V0 #HV10 #HV02
    elim (lifts_total V0 (𝐔❴1❵)) #T0 #HVT0
    lapply (cpms_lifts_bi … HV02 (Ⓣ) … (K1.ⓓV1) … HVT0 … HVT2) -V2
    [ /3 width=2 by drops_refl, drops_drop/ ] #HT02
    /3 width=3 by cpm_delta, ex2_intro/
  | #I1 #K1 #T #i #HT1 #HTU #H1 #H2 destruct
    elim (lpr_inv_bind_sn … HL12) -HL12 #I2 #K2 #HK12 #_ #H destruct
    elim (cpm_inv_lifts_sn … H2 (Ⓣ) … HTU) -X
    [|*: /3 width=2 by drops_refl, drops_drop/ ] -I2 #T2 #HTU2 #HT2
    elim (IH … HT1 … HK12 … HT2) -K2 -T -IH
    [| /2 width=1 by fqu_fqup/ ] #T0 #HT10 #HT02
    elim (lifts_total T0 (𝐔❴1❵)) #U0 #HTU0
    lapply (cpms_lifts_bi … HT02 (Ⓣ) … (K1.ⓘ{I1}) … HTU0 … HTU2) -T2
    [ /3 width=2 by drops_refl, drops_drop/ ] #HU02
    /3 width=3 by cpm_lref, ex2_intro/
  ]
*)
| (*
  #p #I #V1 #T1 #HG #HL #HT #X #H1 #L2 #HL12 #n2 #X2 #H2
  elim (cpm_inv_bind1 … H1) -H1 *
  [ #V #T #HV1 #HT1 #H destruct
    elim (cpm_inv_bind1 … H2) -H2 *
    [ #V2 #T2 #HV2 #HT2 #H destruct
      elim (IH … HT1 … HT2) -T
      [|*: /2 width=1 by lpr_pair/ ] #T0 #HT10 #HT02
      elim (IH … HV1 … HL12 … HV2) -L2 -V -IH
      [| // ] #V0 #HV10 #HV02
      /4 width=7 by cpms_bind, cpms_step_sn, cpm_bind, ex2_intro/
    | #X #HXT #HX2 #H1 #H2 destruct
      elim (cpm_lifts_sn … HX2 (Ⓣ) … (L2.ⓓV) … HXT) -HX2
      [| /3 width=2 by drops_refl, drops_drop/ ] #T2 #HXT2 #HT2
      elim (IH … HT1 … HT2) -HT2 -IH
      [|*: /2 width=1 by lpr_pair/ ] -L2 #T0 #HT10 #HT02
      /3 width=6 by cpms_zeta_dx, cpm_bind, ex2_intro/
    ]
  | #X1 #HXT1 #HX1 #H1 #H2 destruct
    elim (IH … HX1 … HL12 … H2) -L2 -X -IH
    [| /2 width=1 by fqup_zeta/ ] #X0 #HX10 #HX02
    /3 width=3 by cpm_zeta, ex2_intro/
  ]
*)
| #V1 #T1 #HG #HL #HT #X #H1 #L #HL1 #L2 #HL2 #m2 #X2 #H2 destruct
  elim (cpm_inv_appl1 … H1) -H1 *
  [ (*
    #V #T #HV1 #HT1 #H destruct
    elim (cpm_inv_appl1 … H2) -H2 *
    [ #V2 #T2 #HV2 #HT2 #H destruct
      elim (IH … HV1 … HL12 … HV2) -V [| // ] #V0 #HV10 #HV02
      elim (IH … HT1 … HL12 … HT2) -L2 -T -IH [| // ] #T0 #HT10 #HT02
      /3 width=5 by cpms_appl, cpm_appl, ex2_intro/
    | #q #V2 #WX #W2 #TX #T2 #HV2 #HW2 #HT2 #H1 #H2 destruct
      elim (IH … HV1 … HL12 … HV2) -V [| // ] #V0 #HV10 #HV02
      elim (IH … HT1 … HL12 m2 (ⓛ{q}W2.T2)) -IH -HT1
      [|*: /2 width=1 by cpm_bind/ ] -L2 -WX -TX #T0 #HT10 #HT02
      /4 width=9 by cprs_step_dx, cpms_appl, cpm_beta, cpm_appl, ex2_intro/
    | #q #V2 #U2 #WX #W2 #TX #T2 #HV2 #HVU2 #HW2 #HT2 #H1 #H2 destruct
      elim (IH … HV1 … HL12 … HV2) -V [| // ] #V0 #HV10 #HV02
      elim (IH … HT1 … HL12 m2 (ⓓ{q}W2.T2)) -IH -HT1
      [|*: /2 width=1 by cpm_bind/ ] -L2 -WX -TX #T0 #HT10 #HT02
      /4 width=11 by cprs_step_dx, cpms_appl, cpm_theta, cpm_appl, ex2_intro/
    ]
    *)
  | #p #V #W1 #W #TX1 #T #HV1 #HW1 #HT1 #H1 #H3 destruct
    elim (cpm_inv_abbr1 … H2) -H2 *
    [ #X3 #T2 #H2 #HT2 #H destruct
      elim (cpr_inv_cast1 … H2) -H2 [ * ]
      [ #W2 #V2 #HW2 #HV2 #H destruct
        elim (IH … HT1 (L.ⓓⓝW1.V1) … HT2) -T
        [|*: /4 width=3 by lsubr_beta, lpr_pair, cpm_cast, lsubr_cpm_trans/ ] #T0 #HT10 #HT02
        elim (IH … HV1 … HL1 … HL2 … HV2) -V [| // ] #V0 #HV10 #HV02
        elim (IH … HW1 … HL1 … HL2 … HW2) -L2 -W -IH [| // ] #W0 #HW10 #HW02
        @(ex2_intro … (ⓓ{p}ⓝW1.V1.T0))
        [ @cpm_beta //
          
           /2 width=1 by cpm_beta/
      | /3 width=7 by cprs_step_dx, cpms_appl, cpm_beta/
      
       @cprs_step_dx [| @(cpms_appl … HT02 … HV02) | /2 width=1 by cpm_beta/
      @cpms_beta
*)
