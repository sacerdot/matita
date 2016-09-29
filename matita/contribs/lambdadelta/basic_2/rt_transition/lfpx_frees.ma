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

include "basic_2/relocation/drops_lexs.ma".
include "basic_2/s_computation/fqup_weight.ma".
include "basic_2/static/frees_drops.ma".
include "basic_2/rt_transition/cpx_drops.ma".

(* UNCOUNTED PARALLEL RT-TRANSITION FOR LOCAL ENV.S ON REFERRED ENTRIES *****)

(* Properties with context-sensitive free variables *************************)

axiom pippo: ∀RN,RP,L1,i. ⬇*[Ⓕ, 𝐔❴i❵] L1 ≡ ⋆ → 
             ∀f,L2. L1 ⦻*[RN, RP, f] L2 →
             ⬇*[Ⓕ, 𝐔❴i❵] L2 ≡ ⋆.
(*
#RN #RP #L1 #i #H1 #f #L2 #H2
lapply (lexs_co_dropable_sn … H1 … H2) // -HL1 -H2
*)


axiom frees_inv_lifts_SO: ∀b,f,L,U. L ⊢ 𝐅*⦃U⦄ ≡ f →
                          ∀K. ⬇*[b, 𝐔❴1❵] L ≡ K → ∀T. ⬆*[1] T ≡ U →
                          K ⊢ 𝐅*⦃T⦄ ≡ ⫱f.

axiom frees_pair_flat: ∀L,T,f1,I1,V1. L.ⓑ{I1}V1 ⊢ 𝐅*⦃T⦄ ≡ f1 →
                       ∀f2,I2,V2. L.ⓑ{I2}V2 ⊢ 𝐅*⦃T⦄ ≡ f2 →
                       ∀f0. f1 ⋓ f2 ≡ f0 →
                       ∀I0,I. L.ⓑ{I0}ⓕ{I}V1.V2 ⊢ 𝐅*⦃T⦄ ≡ f0.

(* Basic_2A1: was: lpx_cpx_frees_trans *)
lemma cpx_frees_trans_lexs: ∀h,G,L1,T1,f1. L1 ⊢ 𝐅*⦃T1⦄ ≡ f1 →
                            ∀L2. L1 ⦻*[cpx h G, cfull, f1] L2 →
                            ∀T2. ⦃G, L1⦄ ⊢ T1 ⬈[h] T2 →
                            ∃∃f2. L2 ⊢ 𝐅*⦃T2⦄ ≡ f2 & f2 ⊆ f1.
#h #G #L1 #T1 @(fqup_wf_ind_eq … G L1 T1) -G -L1 -T1
#G0 #L0 #U0 #IH #G #L1 * *
[ -IH #s #HG #HL #HU #g1 #H1 #L2 #_ #U2 #H0 destruct
  lapply (frees_inv_sort … H1) -H1 #Hg1
  elim (cpx_inv_sort1 … H0) -H0 #H destruct
  /3 width=3 by frees_sort_gen, sle_refl, ex2_intro/
| #i #HG #HL #HU #g1 #H1 #L2 #H2 #U2 #H0 destruct
  elim (frees_inv_lref_drops … H1) -H1 *
  [ -IH #HL1 #Hg1
    elim (cpx_inv_lref1_drops … H0) -H0
    [ #H destruct lapply (pippo … HL1 … H2) -HL1 -H2
      /3 width=3 by frees_lref_atom, sle_refl, ex2_intro/
    | * -H2 -Hg1 #I #K1 #V1 #V2 #HLK1
      lapply (drops_TF … HLK1) -HLK1 #HLK1
      lapply (drops_mono … HLK1 … HL1) -L1 #H destruct
    ]
  | #f1 #I #K1 #V1 #Hf1 #HLK1 #H destruct
    elim (cpx_inv_lref1_drops … H0) -H0
    [ #H destruct
      elim (lexs_drops_conf_next … H2 … HLK1) -H2 [ |*: // ] #K2 #V2 #HLK2 #HK12 #HV12
      elim (IH … Hf1 … HK12 … HV12) /2 width=2 by fqup_lref/ -L1 -K1 -V1 #f2 #Hf2 #Hf21
      /4 width=7 by frees_lref_pushs, frees_lref_pair, drops_refl, sle_next, ex2_intro, sle_pushs/
    | * #J #Y #X #V2 #H #HV12 #HVU2
      lapply (drops_mono … H … HLK1) -H #H destruct
      elim (lexs_drops_conf_next … H2 … HLK1) -H2 [ |*: // ] #K2 #V0 #HLK2 #HK12 #_
      lapply (drops_isuni_fwd_drop2 … HLK2) // -V0 #HLK2
      elim (IH … Hf1 … HK12 … HV12) /2 width=2 by fqup_lref/ -I -L1 -K1 -V1 #f2 #Hf2 #Hf21
      lapply (frees_lifts … Hf2 … HLK2 … HVU2 ??) /4 width=7 by sle_weak, ex2_intro, sle_pushs/
    ]
  ]
| -IH #l #HG #HL #HU #g1 #H1 #L2 #_ #U2 #H0 destruct
  lapply (frees_inv_gref … H1) -H1 #Hg1
  lapply (cpx_inv_gref1 … H0) -H0 #H destruct
  /3 width=3 by frees_gref_gen, sle_refl, ex2_intro/
| #p #I #V1 #T1 #HG #HL #HU #g1 #H1 #L2 #H2 #U2 #H0 destruct
  elim (frees_inv_bind … H1) -H1 #gV1 #gT1 #HgV1 #HgT1 #Hg1
  elim (cpx_inv_bind1 … H0) -H0 *
  [ #V2 #T2 #HV12 #HT12 #H destruct
    lapply (sle_lexs_trans … H2 gV1 ?) /2 width=2 by sor_inv_sle_sn/ #HL12V
    lapply (sle_lexs_trans … H2 (⫱gT1) ?) /2 width=2 by sor_inv_sle_dx/ -H2 #HL12T
    lapply (lexs_inv_tl … I … HL12T … HV12 ?) // -HL12T #HL12T
    elim (IH … HgV1 … HL12V … HV12) // -HgV1 -HL12V -HV12 #gV2 #HgV2 #HgV21
    elim (IH … HgT1 … HL12T … HT12) // -IH -HgT1 -HL12T -HT12 #gT2 #HgT2 #HgT21
    elim (sor_isfin_ex gV2 (⫱gT2)) /3 width=3 by frees_fwd_isfin, isfin_tl/
    /4 width=10 by frees_bind, monotonic_sle_sor, sle_tl, ex2_intro/
  | #T2 #HT12 #HUT2 #H0 #H1 destruct -HgV1
    lapply (sle_lexs_trans … H2 (⫱gT1) ?) /2 width=2 by sor_inv_sle_dx/ -H2 #HL12T
    lapply (lexs_inv_tl … Abbr … V1 V1 HL12T ??) // -HL12T #HL12T
    elim (IH … HgT1 … HL12T … HT12) // -L1 -T1 #gT2 #HgT2 #HgT21
    lapply (frees_inv_lifts_SO (Ⓣ) … HgT2 … L2 … HUT2) [ /3 width=1 by drops_refl, drops_drop/ ] -V1 -T2
    /5 width=6 by sor_inv_sle_dx, sle_trans, sle_tl, ex2_intro/
  ]
| #I #V1 #T0 #HG #HL #HU #g1 #H1 #L2 #H2 #U2 #H0 destruct
  elim (frees_inv_flat … H1) -H1 #gV1 #gT0 #HgV1 #HgT0 #Hg1
  elim (cpx_inv_flat1 … H0) -H0 *
  [ #V2 #T2 #HV12 #HT12 #H destruct
    lapply (sle_lexs_trans … H2 gV1 ?) /2 width=2 by sor_inv_sle_sn/ #HL12V
    lapply (sle_lexs_trans … H2 gT0 ?) /2 width=2 by sor_inv_sle_dx/ -H2 #HL12T
    elim (IH … HgV1 … HL12V … HV12) // -HgV1 -HL12V -HV12 #gV2 #HgV2 #HgV21
    elim (IH … HgT0 … HL12T … HT12) // -IH -HgT0 -HL12T -HT12 #gT2 #HgT2 #HgT21
    elim (sor_isfin_ex gV2 gT2) /2 width=3 by frees_fwd_isfin/
    /3 width=10 by frees_flat, monotonic_sle_sor, ex2_intro/
  | #HU2 #H destruct -HgV1
    lapply (sle_lexs_trans … H2 gT0 ?) /2 width=2 by sor_inv_sle_dx/ -H2 #HL12T
    elim (IH … HgT0 … HL12T … HU2) // -L1 -T0 -V1
    /4 width=6 by sor_inv_sle_dx, sle_trans, ex2_intro/
  | #HU2 #H destruct -HgT0
    lapply (sle_lexs_trans … H2 gV1 ?) /2 width=2 by sor_inv_sle_sn/ -H2 #HL12V
    elim (IH … HgV1 … HL12V … HU2) // -L1 -T0 -V1
    /4 width=6 by sor_inv_sle_sn, sle_trans, ex2_intro/
  | #p #V2 #W1 #W2 #T1 #T2 #HV12 #HW12 #HT12 #H0 #H1 #H destruct
    elim (frees_inv_bind … HgT0) -HgT0 #gW1 #gT1 #HgW1 #HgT1 #HgT0
    lapply (sle_lexs_trans … H2 gV1 ?) /2 width=2 by sor_inv_sle_sn/ #HL12V
    lapply (sle_lexs_trans … H2 gT0 ?) /2 width=2 by sor_inv_sle_dx/ -H2 #H2
    lapply (sle_lexs_trans … H2 gW1 ?) /2 width=2 by sor_inv_sle_sn/ #HL12W
    lapply (sle_lexs_trans … H2 (⫱gT1) ?) /2 width=2 by sor_inv_sle_dx/ -H2 #HL12T
    lapply (lexs_inv_tl … Abst … HL12T … HW12 ?) // -HL12T #HL12T
    elim (IH … HgV1 … HL12V … HV12) // -HgV1 -HL12V -HV12 #gV2 #HgV2 #HgV21
    elim (IH … HgW1 … HL12W … HW12) // -HgW1 -HL12W -HW12 #gW2 #HgW2 #HgW21
    elim (IH … HgT1 … HL12T … HT12) // -IH -HgT1 -HL12T -HT12 #gT2 #HgT2 #HgT21
    elim (sor_isfin_ex gW2 gV2) /2 width=3 by frees_fwd_isfin/ #gV0 #HgV0 #H
    elim (sor_isfin_ex gV0 (⫱gT2)) /3 width=3 by frees_fwd_isfin, isfin_tl/ -H #g2 #Hg2 #_
    @(ex2_intro … g2)
    [ @(frees_bind … Hg2) /2 width=5 by frees_flat/ ]
  | #p #V2 #V #W1 #W2 #T1 #T2 #HV12 #HV2 #HW12 #HT12 #H0 #H1 #H destruct
    elim (frees_inv_bind … HgT0) -HgT0 #gW1 #gT1 #HgW1 #HgT1 #HgT0
    lapply (sle_lexs_trans … H2 gV1 ?) /2 width=2 by sor_inv_sle_sn/ #HL12V
    lapply (sle_lexs_trans … H2 gT0 ?) /2 width=2 by sor_inv_sle_dx/ -H2 #H2
    lapply (sle_lexs_trans … H2 gW1 ?) /2 width=2 by sor_inv_sle_sn/ #HL12W
    lapply (sle_lexs_trans … H2 (⫱gT1) ?) /2 width=2 by sor_inv_sle_dx/ -H2 #HL12T
    lapply (lexs_inv_tl … Abbr … HL12T … HW12 ?) // -HL12T #HL12T
    elim (sor_isfin_ex gV1 gW1) /2 width=3 by frees_fwd_isfin/ #g0 #Hg0 #_
    lapply (sor_trans2 … Hg1 … HgT0 … Hg0) -Hg1 -HgT0 #Hg1
    elim (IH … HgV1 … HL12V … HV12) // -HgV1 -HL12V -HV12 #gV2 #HgV2 #HgV21
    elim (IH … HgW1 … HL12W … HW12) // -HgW1 -HL12W -HW12 #gW2 #HgW2 #HgW21
    elim (IH … HgT1 … HL12T … HT12) // -IH -HgT1 -HL12T -HT12 #gT2 #HgT2 #HgT21
    elim (sor_isfin_ex (↑gV2) gT2) /3 width=3 by frees_fwd_isfin, isfin_push/ #gV0 #HgV0 #H
    elim (sor_isfin_ex gW2 (⫱gV0)) /3 width=3 by frees_fwd_isfin, isfin_tl/ -H #g2 #Hg2 #_
    elim (sor_isfin_ex gW2 gV2) /2 width=3 by frees_fwd_isfin/ #g #Hg #_
    lapply (sor_trans2 … Hg2 … (⫱gT2) … Hg) /2 width=1 by sor_tl/ #Hg2
    lapply (frees_lifts (Ⓣ) … HgV2 … (L2.ⓓW2) … HV2 ??) [4: |*: /3 width=3 by drops_refl, drops_drop/ ] -V2 #HgV
    lapply (sor_sym … Hg) -Hg #Hg
    /4 width=10 by frees_flat, frees_bind, monotonic_sle_sor, sle_tl, ex2_intro/
  ]
]

lemma cpx_frees_trans: ∀h,o,G. frees_trans (cpx h o G).
/2 width=8 by lpx_cpx_frees_trans/ qed-.

lemma lpx_frees_trans: ∀h,o,G,L1,L2. ⦃G, L1⦄ ⊢ ➡[h, o] L2 →
                       ∀U,i. L2 ⊢ i ϵ 𝐅*[0]⦃U⦄ → L1 ⊢ i ϵ 𝐅*[0]⦃U⦄.
/2 width=8 by lpx_cpx_frees_trans/ qed-.
