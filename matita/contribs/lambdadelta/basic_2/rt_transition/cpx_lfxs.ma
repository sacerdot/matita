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

include "basic_2/syntax/lveq_length.ma".
include "basic_2/relocation/lexs_length.ma".
include "basic_2/relocation/drops_lexs.ma".
include "basic_2/static/frees_drops.ma".
include "basic_2/static/lsubf_frees.ma".
include "basic_2/static/lfxs.ma".
include "basic_2/rt_transition/cpx_drops.ma".
include "basic_2/rt_transition/cpx_ext.ma".

(* UNCOUNTED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS *************)

(* Properties with context-sensitive free variables *************************)

(* Basic_2A1: uses: lpx_cpx_frees_trans *)
lemma cpx_frees_conf_lexs: ∀h,G,L1,T1,f1. L1 ⊢ 𝐅*⦃T1⦄ ≡ f1 →
                           ∀L2. L1 ⪤*[cpx_ext h G, cfull, f1] L2 →
                           ∀T2. ⦃G, L1⦄ ⊢ T1 ⬈[h] T2 →
                           ∃∃f2. L2 ⊢ 𝐅*⦃T2⦄ ≡ f2 & f2 ⊆ f1.
#h #G #L1 #T1 @(fqup_wf_ind_eq (Ⓣ) … G L1 T1) -G -L1 -T1
#G0 #L0 #U0 #IH #G #L1 * *
[ -IH #s #HG #HL #HU #g1 #H1 #L2 #_ #U2 #H0 destruct
  lapply (frees_inv_sort … H1) -H1 #Hg1
  elim (cpx_inv_sort1 … H0) -H0 #H destruct
  /3 width=3 by frees_sort, sle_refl, ex2_intro/
| #i #HG #HL #HU #g1 #H1 #L2 #H2 #U2 #H0 destruct
  elim (frees_inv_lref_drops … H1) -H1 *
  [ -IH #f1 #HL1 #Hf1 #H destruct
    elim (cpx_inv_lref1_drops … H0) -H0
    [ #H destruct
      /4 width=9 by frees_atom_drops, drops_atom2_lexs_conf, sle_refl, ex2_intro/
    | * -H2 -Hf1 #I #K1 #V1 #V2 #HLK1
      lapply (drops_TF … HLK1) -HLK1 #HLK1
      lapply (drops_mono … HLK1 … HL1) -L1 #H destruct
    ]
  | #f1 #I #K1 #V1 #Hf1 #HLK1 #H destruct
    elim (cpx_inv_lref1_drops … H0) -H0
    [ #H destruct
      elim (lexs_drops_conf_next … H2 … HLK1) -H2 [ |*: // ] #Z #K2 #HLK2 #HK12 #H
      elim (ext2_inv_pair_sn … H) -H #V2 #HV12 #H destruct
      elim (IH … Hf1 … HK12 … HV12) /2 width=2 by fqup_lref/ -L1 -K1 -V1 #f2 #Hf2 #Hf21
      /4 width=7 by frees_lref_pushs, frees_pair_drops, drops_refl, sle_pushs, sle_next, ex2_intro/
    | * #Z #Y #X #V2 #H #HV12 #HVU2
      lapply (drops_mono … H … HLK1) -H #H destruct
      elim (lexs_drops_conf_next … H2 … HLK1) -H2 [ |*: // ] #I2 #K2 #HLK2 #HK12 #H
      elim (ext2_inv_pair_sn … H) -H #V0 #_ #H destruct
      lapply (drops_isuni_fwd_drop2 … HLK2) // -V0 #HLK2
      elim (IH … Hf1 … HK12 … HV12) /2 width=2 by fqup_lref/ -I -L1 -K1 -V1 #f2 #Hf2 #Hf21
      lapply (frees_lifts … Hf2 … HLK2 … HVU2 ??) /4 width=7 by sle_weak, ex2_intro, sle_pushs/
    ]
  | #f1 #I #K1 #HLK1 #Hf1 #H destruct
    elim (cpx_inv_lref1_drops … H0) -H0
    [ -IH #H destruct
      elim (lexs_drops_conf_next … H2 … HLK1) -H2 -HLK1 [ |*: // ] #Z #K2 #HLK2 #_ #H
      lapply (ext2_inv_unit_sn … H) -H #H destruct
      /3 width=3 by frees_unit_drops, sle_refl, ex2_intro/
    | * -H2 -Hf1 #Z #Y1 #X1 #X2 #HLY1
      lapply (drops_mono … HLK1 … HLY1) -L1 #H destruct
    ]
  ]
| -IH #l #HG #HL #HU #g1 #H1 #L2 #_ #U2 #H0 destruct
  lapply (frees_inv_gref … H1) -H1 #Hg1
  lapply (cpx_inv_gref1 … H0) -H0 #H destruct
  /3 width=3 by frees_gref, sle_refl, ex2_intro/
| #p #I #V1 #T1 #HG #HL #HU #g1 #H1 #L2 #H2 #U2 #H0 destruct
  elim (frees_inv_bind … H1) -H1 #gV1 #gT1 #HgV1 #HgT1 #Hg1
  elim (cpx_inv_bind1 … H0) -H0 *
  [ #V2 #T2 #HV12 #HT12 #H destruct
    lapply (sle_lexs_trans … H2 gV1 ?) /2 width=2 by sor_inv_sle_sn/ #HL12V
    lapply (sle_lexs_trans … H2 (⫱gT1) ?) /2 width=2 by sor_inv_sle_dx/ -H2 #HL12T
    lapply (lexs_inv_tl … (BPair I V1) (BPair I V2) … HL12T ??) /2 width=1 by ext2_pair/ -HL12T #HL12T
    elim (IH … HgV1 … HL12V … HV12) // -HgV1 -HL12V -HV12 #gV2 #HgV2 #HgV21
    elim (IH … HgT1 … HL12T … HT12) // -IH -HgT1 -HL12T -HT12 #gT2 #HgT2 #HgT21
    elim (sor_isfin_ex gV2 (⫱gT2)) /3 width=3 by frees_fwd_isfin, isfin_tl/
    /4 width=10 by frees_bind, monotonic_sle_sor, sle_tl, ex2_intro/
  | #T2 #HT12 #HUT2 #H0 #H1 destruct -HgV1
    lapply (sle_lexs_trans … H2 (⫱gT1) ?) /2 width=2 by sor_inv_sle_dx/ -H2 #HL12T
    lapply (lexs_inv_tl … (BPair Abbr V1) (BPair Abbr V1) … HL12T ??) /2 width=1 by ext2_pair/ -HL12T #HL12T
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
    lapply (lexs_inv_tl … (BPair Abst W1) (BPair Abst W2) … HL12T ??) /2 width=1 by ext2_pair, I/ -HL12T #HL12T
    elim (sor_isfin_ex gV1 gW1) /2 width=3 by frees_fwd_isfin/ #g0 #Hg0 #_
    lapply (sor_assoc_sn … Hg1 … HgT0 … Hg0) -Hg1 -HgT0 #Hg1
    lapply (sor_comm … Hg0) -Hg0 #Hg0
    elim (IH … HgV1 … HL12V … HV12) // -HgV1 -HL12V -HV12 #gV2 #HgV2 #HgV21
    elim (IH … HgW1 … HL12W … HW12) // -HgW1 -HL12W -HW12 #gW2 #HgW2 #HgW21
    elim (IH … HgT1 … HL12T … HT12) // -IH -HgT1 -HL12T -HT12 #gT2 #HgT2 #HgT21
    elim (sor_isfin_ex (⫱gT2) gV2) /3 width=3 by frees_fwd_isfin, isfin_tl/ #gVT2 #HgVT2 #_
    elim (lsubf_beta_tl_dx … HgV2 … HgVT2 … W2) [ |*: /1 width=3 by lsubf_refl/ ] #gT0 #HL2 #HgT02
    lapply (lsubf_frees_trans … HgT2 … HL2) -HgT2 -HL2 #HgT0
    lapply (sor_comm … HgVT2) -HgVT2 #HgVT2 (**) (* this should be removed *)
    elim (sor_isfin_ex gW2 gV2) /2 width=3 by frees_fwd_isfin/ #gV0 #HgV0 #H
    elim (sor_isfin_ex gV0 (⫱gT0)) /3 width=3 by frees_fwd_isfin, isfin_tl/ -H #g2 #Hg2 #_
    @(ex2_intro … g2) /3 width=5 by frees_flat, frees_bind/ -h -p -G -L1 -L2 -V1 -V2 -W1 -W2 -T1 -T2
    @(sor_inv_sle … Hg2) -Hg2
    [ /3 width=11 by sor_inv_sle_sn_trans, monotonic_sle_sor/
    | @(sle_trans … HgT02) -HgT02
      /3 width=8 by monotonic_sle_sor, sor_inv_sle_dx_trans, sle_tl/
    ] (**) (* full auto too slow *)
  | #p #V2 #V #W1 #W2 #T1 #T2 #HV12 #HV2 #HW12 #HT12 #H0 #H1 #H destruct
    elim (frees_inv_bind … HgT0) -HgT0 #gW1 #gT1 #HgW1 #HgT1 #HgT0
    lapply (sle_lexs_trans … H2 gV1 ?) /2 width=2 by sor_inv_sle_sn/ #HL12V
    lapply (sle_lexs_trans … H2 gT0 ?) /2 width=2 by sor_inv_sle_dx/ -H2 #H2
    lapply (sle_lexs_trans … H2 gW1 ?) /2 width=2 by sor_inv_sle_sn/ #HL12W
    lapply (sle_lexs_trans … H2 (⫱gT1) ?) /2 width=2 by sor_inv_sle_dx/ -H2 #HL12T
    lapply (lexs_inv_tl … (BPair Abbr W1) (BPair Abbr W2) … HL12T ??) /2 width=1 by ext2_pair, I/ -HL12T #HL12T
    elim (sor_isfin_ex gV1 gW1) /2 width=3 by frees_fwd_isfin/ #g0 #Hg0 #_
    lapply (sor_assoc_sn … Hg1 … HgT0 … Hg0) -Hg1 -HgT0 #Hg1
    elim (IH … HgV1 … HL12V … HV12) // -HgV1 -HL12V -HV12 #gV2 #HgV2 #HgV21
    elim (IH … HgW1 … HL12W … HW12) // -HgW1 -HL12W -HW12 #gW2 #HgW2 #HgW21
    elim (IH … HgT1 … HL12T … HT12) // -IH -HgT1 -HL12T -HT12 #gT2 #HgT2 #HgT21
    elim (sor_isfin_ex (↑gV2) gT2) /3 width=3 by frees_fwd_isfin, isfin_push/ #gV0 #HgV0 #H
    elim (sor_isfin_ex gW2 (⫱gV0)) /3 width=3 by frees_fwd_isfin, isfin_tl/ -H #g2 #Hg2 #_
    elim (sor_isfin_ex gW2 gV2) /2 width=3 by frees_fwd_isfin/ #g #Hg #_
    lapply (sor_assoc_sn … Hg2 … (⫱gT2) … Hg) /2 width=1 by sor_tl/ #Hg2
    lapply (frees_lifts (Ⓣ) … HgV2 … (L2.ⓓW2) … HV2 ??)
    [4: lapply (sor_comm … Hg) |*: /3 width=3 by drops_refl, drops_drop/ ] -V2 (**) (* full auto too slow *)
    /4 width=10 by frees_flat, frees_bind, monotonic_sle_sor, sle_tl, ex2_intro/
  ]
]
qed-.

(* Basic_2A1: uses: cpx_frees_trans *)
lemma cpx_fle_comp: ∀h,G. R_fle_compatible (cpx h G).
#h #G #L #T1 #T2 #HT12
elim (frees_total L T1) #f1 #Hf1
elim (cpx_frees_conf_lexs … Hf1 L … HT12) -HT12
/3 width=8 by lexs_refl, ext2_refl, ex4_4_intro/
qed-.

(* Basic_2A1: uses: lpx_frees_trans *)
lemma lfpx_fle_comp: ∀h,G. lfxs_fle_compatible (cpx h G).
#h #G #L1 #L2 #T * #f1 #Hf1 #HL12
elim (cpx_frees_conf_lexs h … Hf1 … HL12 T) // #f2 #Hf2
lapply (lexs_fwd_length … HL12)
/3 width=8 by lveq_length_eq, ex4_4_intro/ (**) (* full auto fails *)
qed-.

(* Properties with generic extension on referred entries ********************)

(* Note: lemma 1000 *)
(* Basic_2A1: uses: cpx_llpx_sn_conf *)
lemma cpx_lfxs_conf: ∀R,h,G. s_r_confluent1 … (cpx h G) (lfxs R).
#R #h #G #L1 #T1 #T2 #H #L2 * #f1 #Hf1 elim (cpx_frees_conf_lexs … Hf1 L1 … H) -T1
/3 width=5 by lexs_refl, ext2_refl, sle_lexs_trans, ex2_intro/
qed-.
