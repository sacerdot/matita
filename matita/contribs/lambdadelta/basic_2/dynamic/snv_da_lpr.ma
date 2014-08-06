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

include "basic_2/static/lsubd_da.ma".
include "basic_2/dynamic/snv_aaa.ma".
include "basic_2/dynamic/snv_scpes.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Properties on degree assignment for terms ********************************)

fact da_cpr_lpr_aux: ∀h,g,G0,L0,T0.
                     (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_lstas h g G1 L1 T1) →
                     (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_snv_cpr_lpr h g G1 L1 T1) →
                     (∀G1,L1,T1. ⦃G0, L0, T0⦄ >≡[h, g] ⦃G1, L1, T1⦄ → IH_da_cpr_lpr h g G1 L1 T1) →
                     ∀G1,L1,T1. G0 = G1 → L0 = L1 → T0 = T1 → IH_da_cpr_lpr h g G1 L1 T1.
#h #g #G0 #L0 #T0 #IH3 #IH2 #IH1 #G1 #L1 * * [|||| * ]
[ #k #_ #_ #_ #_ #l #H2 #X3 #H3 #L2 #_ -IH3 -IH2 -IH1
  lapply (da_inv_sort … H2) -H2
  lapply (cpr_inv_sort1 … H3) -H3 #H destruct /2 width=1 by da_sort/
| #i #HG0 #HL0 #HT0 #H1 #l #H2 #X3 #H3 #L2 #HL12 destruct -IH3 -IH2
  elim (snv_inv_lref … H1) -H1 #I0 #K0 #X0 #H #HX0
  elim (da_inv_lref … H2) -H2 * #K1 [ #V1 | #W1 #l1 ] #HLK1 [ #HV1 | #HW1 #H ] destruct
  lapply (drop_mono … H … HLK1) -H #H destruct
  elim (cpr_inv_lref1 … H3) -H3
  [1,3: #H destruct
    lapply (fqup_lref … G1 … HLK1)
    elim (lpr_drop_conf … HLK1 … HL12) -HLK1 -HL12 #X #H #HLK2
    elim (lpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
    /4 width=10 by da_ldef, da_ldec, fqup_fpbg/
  |2,4: * #K0 #V0 #W0 #H #HVW0 #HW0
    lapply (drop_mono … H … HLK1) -H #H destruct
    lapply (fqup_lref … G1 … HLK1)
    elim (lpr_drop_conf … HLK1 … HL12) -HLK1 -HL12 #X #H #HLK2
    elim (lpr_inv_pair1 … H) -H #K2 #V2 #HK12 #_ #H destruct
    lapply (drop_fwd_drop2 … HLK2) -V2
    /4 width=8 by da_lift, fqup_fpbg/
  ]
| #p #_ #_ #HT0 #H1 destruct -IH3 -IH2 -IH1
  elim (snv_inv_gref … H1)
| #a #I #V1 #T1 #HG0 #HL0 #HT0 #H1 #l #H2 #X3 #H3 #L2 #HL12 destruct -IH2
  elim (snv_inv_bind … H1) -H1 #_ #HT1
  lapply (da_inv_bind … H2) -H2
  elim (cpr_inv_bind1 … H3) -H3 *
  [ #V2 #T2 #HV12 #HT12 #H destruct
    /4 width=9 by da_bind, fqup_fpbg, lpr_pair/
  | #T2 #HT12 #HT2 #H1 #H2 destruct
    /4 width=11 by da_inv_lift, fqup_fpbg, lpr_pair, drop_drop/
  ]
| #V1 #T1 #HG0 #HL0 #HT0 #H1 #l #H2 #X3 #H3 #L2 #HL12 destruct
  elim (snv_inv_appl … H1) -H1 #b1 #W1 #U1 #l1 #HV1 #HT1 #HVW1 #HTU1
  lapply (da_inv_flat … H2) -H2 #Hl
  elim (cpr_inv_appl1 … H3) -H3 *
  [ #V2 #T2 #HV12 #HT12 #H destruct -IH3 -IH2 /4 width=7 by da_flat, fqup_fpbg/
  | #b #V2 #W #W2 #U #U2 #HV12 #HW2 #HU2 #H1 #H2 destruct
    elim (snv_inv_bind … HT1) -HT1 #HW #HU
    lapply (da_inv_bind … Hl) -Hl #Hl
    elim (scpds_inv_abst1 … HTU1) -HTU1 #W3 #U3 #HW3 #_ #H destruct -U3 -l1
    elim (snv_fwd_da … HV1) #l1 #Hl1
    elim (snv_fwd_da … HW) #l0 #Hl0
    lapply (scpds_div … W … 0 … HVW1) /2 width=2 by cprs_scpds/ -W3 #H
    elim (da_scpes_aux … IH3 IH2 IH1 … Hl0 … Hl1 … H) -IH3 -IH2 -H /2 width=1 by fqup_fpbg/ #_ #H1
    <minus_n_O #H destruct >(plus_minus_m_m l1 1) in Hl1; // -H1 #Hl1
    lapply (IH1 … HV1 … Hl1 … HV12 … HL12) -HV1 -Hl1 -HV12 [ /2 by fqup_fpbg/ ]
    lapply (IH1 … Hl0 … HW2 … HL12) -Hl0 /2 width=1 by fqup_fpbg/ -HW
    lapply (IH1 … HU … Hl … HU2 (L2.ⓛW2) ?) -IH1 -HU -Hl -HU2 [1,2: /2 by fqup_fpbg, lpr_pair/ ] -HL12 -HW2
    /4 width=6 by da_bind, lsubd_da_trans, lsubd_beta/
  | #b #V0 #V2 #W #W2 #U #U2 #HV10 #HV02 #HW2 #HU2 #H1 #H2 destruct -IH3 -IH2 -b1 -V0 -W1 -U1 -l1 -HV1
    elim (snv_inv_bind … HT1) -HT1 #_
    lapply (da_inv_bind … Hl) -Hl
    /5 width=9 by da_bind, da_flat, fqup_fpbg, lpr_pair/
  ]
| #W1 #T1 #HG0 #HL0 #HT0 #H1 #l #H2 #X3 #H3 #L2 #HL12 destruct -IH3 -IH2
  elim (snv_inv_cast … H1) -H1 #U1 #HW1 #HT1 #HWU1 #HTU1
  lapply (da_inv_flat … H2) -H2 #Hl
  elim (cpr_inv_cast1 … H3) -H3
  [ * #W2 #T2 #HW12 #HT12 #H destruct /4 width=7 by da_flat, fqup_fpbg/
  | /3 width=7 by fqup_fpbg/
  ]
]
qed-.
