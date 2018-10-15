
include "basic_2/rt_computation/cpms_lpr.ma".

theorem cpr_cpm_trans_swap_lpr (h) (G) (L1) (T1):
        ∀T. ⦃G,L1⦄ ⊢ T1 ➡[h] T → ∀L2. ⦃G,L1⦄ ⊢ ➡[h] L2 → ∀n2,T2. ⦃G,L2⦄ ⊢ T ➡[n2,h] T2 →
        ∃∃T0. ⦃G,L1⦄ ⊢ T1 ➡[n2,h] T0 & ⦃G,L1⦄ ⊢ T0 ➡*[h] T2.
#h #G #L1 #T1 #T #H
@(cpr_ind … H) -G -L1 -T1 -T
[ (* #I #G #L1 #L2 #HL12 #n2 #T2 #HT2 /2 width=3 by ex2_intro/ *)
| (*
  #G #K #V1 #V #W #_ #IH #HVW #n2 #T2 #HT2
  elim (cpm_inv_lifts_sn … HT2 (Ⓣ) … HVW) -W
  [|*: /3 width=2 by drops_refl, drops_drop/ ] #V2 #HVT2 #HV2
  elim (IH … HV2) -V #V0 #HV10 #HV02
  elim (lifts_total V0 (𝐔❴1❵)) #T0 #HVT0
  lapply (cpm_lifts_bi … HV02 (Ⓣ) … (K.ⓓV1) … HVT0 … HVT2) -V2
  [ /3 width=2 by drops_refl, drops_drop/ ] #HT02
  /3 width=3 by cpm_delta, ex2_intro/
*)
| (*
  #I #G #K #T #U #i #_ #IH #HTU #n2 #U2 #HU2
  elim (cpm_inv_lifts_sn … HU2 (Ⓣ) … HTU) -U
  [|*: /3 width=2 by drops_refl, drops_drop/ ] #T2 #HTU2 #HT2
  elim (IH … HT2) -T #T0 #HT0 #HT02
  elim (lifts_total T0 (𝐔❴1❵)) #U0 #HTU0
  lapply (cpm_lifts_bi … HT02 (Ⓣ) … (K.ⓘ{I}) … HTU0 … HTU2) -T2
  [ /3 width=2 by drops_refl, drops_drop/ ] #HU02
  /3 width=3 by cpm_lref, ex2_intro/
*)
| #p #I #G #L1 #V1 #V #T1 #T #HV1 #_ #_ #IHT #L2 #HL12 #n2 #X2 #H
  elim (cpm_inv_bind1 … H) -H *
  [ #V2 #T2 #HV2 #HT2 #H destruct
    elim (IHT … HT2) -T [| /2 width=1 by lpr_pair/ ] #T0 #HT10 #HT02
    lapply (lpr_cpm_trans … HV2 … HL12) -L2 #HV2
    /4 width=7 by cpms_bind, cpms_step_sn, cpm_bind, ex2_intro/
  | #X #HXT #HX2 #H1 #H2 destruct
    elim (cpm_lifts_sn … HX2 (Ⓣ) … (L2.ⓓV) … HXT) -HX2
    [| /3 width=2 by drops_refl, drops_drop/ ] #T2 #HXT2 #HT2
    elim (IHT … HT2) -HT2 -IHT [| /2 width=1 by lpr_pair/ ] #T0 #HT10 #HT02
    /3 width=6 by cpms_zeta_dx, cpm_bind, ex2_intro/
  ]
|