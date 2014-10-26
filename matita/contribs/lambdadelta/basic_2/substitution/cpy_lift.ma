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

include "basic_2/substitution/drop_drop.ma".
include "basic_2/substitution/cpy.ma".

(* CONTEXT-SENSITIVE EXTENDED ORDINARY SUBSTITUTION FOR TERMS ***************)

(* Properties on relocation *************************************************)

(* Basic_1: was: subst1_lift_lt *)
lemma cpy_lift_le: ∀G,K,T1,T2,lt,mt. ⦃G, K⦄ ⊢ T1 ▶[lt, mt] T2 →
                   ∀L,U1,U2,s,l,m. ⬇[s, l, m] L ≡ K →
                   ⬆[l, m] T1 ≡ U1 → ⬆[l, m] T2 ≡ U2 →
                   lt + mt ≤ l → ⦃G, L⦄ ⊢ U1 ▶[lt, mt] U2.
#G #K #T1 #T2 #lt #mt #H elim H -G -K -T1 -T2 -lt -mt
[ #I #G #K #lt #mt #L #U1 #U2 #s #l #m #_ #H1 #H2 #_
  >(lift_mono … H1 … H2) -H1 -H2 //
| #I #G #K #KV #V #W #i #lt #mt #Hlti #Hilmt #HKV #HVW #L #U1 #U2 #s #l #m #HLK #H #HWU2 #Hlmtl
  lapply (ylt_yle_trans … Hlmtl … Hilmt) -Hlmtl #Hil
  lapply (ylt_inv_inj … Hil) -Hil #Hil
  lapply (lift_inv_lref1_lt … H … Hil) -H #H destruct
  elim (lift_trans_ge … HVW … HWU2) -W // <minus_plus #W #HVW #HWU2
  elim (drop_trans_le … HLK … HKV) -K /2 width=2 by lt_to_le/ #X #HLK #H
  elim (drop_inv_skip2 … H) -H /2 width=1 by lt_plus_to_minus_r/ -Hil #K #Y #_ #HVY
  >(lift_mono … HVY … HVW) -Y -HVW #H destruct /2 width=5 by cpy_subst/
| #a #I #G #K #V1 #V2 #T1 #T2 #lt #mt #_ #_ #IHV12 #IHT12 #L #U1 #U2 #s #l #m #HLK #H1 #H2 #Hlmtl
  elim (lift_inv_bind1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_bind1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct
  /4 width=7 by cpy_bind, drop_skip, yle_succ/
| #G #I #K #V1 #V2 #T1 #T2 #lt #mt #_ #_ #IHV12 #IHT12 #L #U1 #U2 #s #l #m #HLK #H1 #H2 #Hlmtl
  elim (lift_inv_flat1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_flat1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct
  /3 width=7 by cpy_flat/
]
qed-.

lemma cpy_lift_be: ∀G,K,T1,T2,lt,mt. ⦃G, K⦄ ⊢ T1 ▶[lt, mt] T2 →
                   ∀L,U1,U2,s,l,m. ⬇[s, l, m] L ≡ K →
                   ⬆[l, m] T1 ≡ U1 → ⬆[l, m] T2 ≡ U2 →
                   lt ≤ l → l ≤ lt + mt → ⦃G, L⦄ ⊢ U1 ▶[lt, mt + m] U2.
#G #K #T1 #T2 #lt #mt #H elim H -G -K -T1 -T2 -lt -mt
[ #I #G #K #lt #mt #L #U1 #U2 #s #l #m #_ #H1 #H2 #_ #_
  >(lift_mono … H1 … H2) -H1 -H2 //
| #I #G #K #KV #V #W #i #lt #mt #Hlti #Hilmt #HKV #HVW #L #U1 #U2 #s #l #m #HLK #H #HWU2 #Hltl #_
  elim (lift_inv_lref1 … H) -H * #Hil #H destruct
  [ -Hltl
    lapply (ylt_yle_trans … (lt+mt+m) … Hilmt) // -Hilmt #Hilmtm
    elim (lift_trans_ge … HVW … HWU2) -W // <minus_plus #W #HVW #HWU2
    elim (drop_trans_le … HLK … HKV) -K /2 width=2 by lt_to_le/ #X #HLK #H
    elim (drop_inv_skip2 … H) -H /2 width=1 by lt_plus_to_minus_r/ -Hil #K #Y #_ #HVY
    >(lift_mono … HVY … HVW) -V #H destruct /2 width=5 by cpy_subst/
  | -Hlti
    elim (yle_inv_inj2 … Hltl) -Hltl #ltt #Hltl #H destruct
    lapply (transitive_le … Hltl Hil) -Hltl #Hlti
    lapply (lift_trans_be … HVW … HWU2 ? ?) -W /2 width=1 by le_S/ >plus_plus_comm_23 #HVU2
    lapply (drop_trans_ge_comm … HLK … HKV ?) -K // -Hil
    /4 width=5 by cpy_subst, drop_inv_gen, monotonic_ylt_plus_dx, yle_plus_dx1_trans, yle_inj/
  ]
| #a #I #G #K #V1 #V2 #T1 #T2 #lt #mt #_ #_ #IHV12 #IHT12 #L #U1 #U2 #s #l #m #HLK #H1 #H2 #Hltl #Hllmt
  elim (lift_inv_bind1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_bind1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct
  /4 width=7 by cpy_bind, drop_skip, yle_succ/
| #I #G #K #V1 #V2 #T1 #T2 #lt #mt #_ #_ #IHV12 #IHT12 #L #U1 #U2 #s #l #m #HLK #H1 #H2 #Hlmtl
  elim (lift_inv_flat1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_flat1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct
  /3 width=7 by cpy_flat/
]
qed-.

(* Basic_1: was: subst1_lift_ge *)
lemma cpy_lift_ge: ∀G,K,T1,T2,lt,mt. ⦃G, K⦄ ⊢ T1 ▶[lt, mt] T2 →
                   ∀L,U1,U2,s,l,m. ⬇[s, l, m] L ≡ K →
                   ⬆[l, m] T1 ≡ U1 → ⬆[l, m] T2 ≡ U2 →
                   l ≤ lt → ⦃G, L⦄ ⊢ U1 ▶[lt+m, mt] U2.
#G #K #T1 #T2 #lt #mt #H elim H -G -K -T1 -T2 -lt -mt
[ #I #G #K #lt #mt #L #U1 #U2 #s #l #m #_ #H1 #H2 #_
  >(lift_mono … H1 … H2) -H1 -H2 //
| #I #G #K #KV #V #W #i #lt #mt #Hlti #Hilmt #HKV #HVW #L #U1 #U2 #s #l #m #HLK #H #HWU2 #Hllt
  lapply (yle_trans … Hllt … Hlti) -Hllt #Hil
  elim (yle_inv_inj2 … Hil) -Hil #ll #Hlli #H0 destruct
  lapply (lift_inv_lref1_ge … H … Hlli) -H #H destruct
  lapply (lift_trans_be … HVW … HWU2 ? ?) -W /2 width=1 by le_S/ >plus_plus_comm_23 #HVU2
  lapply (drop_trans_ge_comm … HLK … HKV ?) -K // -Hlli
  /3 width=5 by cpy_subst, drop_inv_gen, monotonic_ylt_plus_dx, monotonic_yle_plus_dx/
| #a #I #G #K #V1 #V2 #T1 #T2 #lt #mt #_ #_ #IHV12 #IHT12 #L #U1 #U2 #s #l #m #HLK #H1 #H2 #Hllt
  elim (lift_inv_bind1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_bind1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct
  /4 width=6 by cpy_bind, drop_skip, yle_succ/
| #I #G #K #V1 #V2 #T1 #T2 #lt #mt #_ #_ #IHV12 #IHT12 #L #U1 #U2 #s #l #m #HLK #H1 #H2 #Hllt
  elim (lift_inv_flat1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_flat1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct
  /3 width=6 by cpy_flat/
]
qed-.

(* Inversion lemmas on relocation *******************************************)

(* Basic_1: was: subst1_gen_lift_lt *)
lemma cpy_inv_lift1_le: ∀G,L,U1,U2,lt,mt. ⦃G, L⦄ ⊢ U1 ▶[lt, mt] U2 →
                        ∀K,s,l,m. ⬇[s, l, m] L ≡ K → ∀T1. ⬆[l, m] T1 ≡ U1 →
                        lt + mt ≤ l →
                        ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶[lt, mt] T2 & ⬆[l, m] T2 ≡ U2.
#G #L #U1 #U2 #lt #mt #H elim H -G -L -U1 -U2 -lt -mt
[ * #i #G #L #lt #mt #K #s #l #m #_ #T1 #H #_
  [ lapply (lift_inv_sort2 … H) -H #H destruct /2 width=3 by ex2_intro/
  | elim (lift_inv_lref2 … H) -H * #Hil #H destruct /3 width=3 by lift_lref_ge_minus, lift_lref_lt, ex2_intro/
  | lapply (lift_inv_gref2 … H) -H #H destruct /2 width=3 by ex2_intro/
  ]
| #I #G #L #KV #V #W #i #lt #mt #Hlti #Hilmt #HLKV #HVW #K #s #l #m #HLK #T1 #H #Hlmtl
  lapply (ylt_yle_trans … Hlmtl … Hilmt) -Hlmtl #Hil
  lapply (ylt_inv_inj … Hil) -Hil #Hil
  lapply (lift_inv_lref2_lt … H … Hil) -H #H destruct
  elim (drop_conf_lt … HLK … HLKV) -L // #L #U #HKL #_ #HUV
  elim (lift_trans_le … HUV … HVW) -V // >minus_plus <plus_minus_m_m // -Hil /3 width=5 by cpy_subst, ex2_intro/
| #a #I #G #L #W1 #W2 #U1 #U2 #lt #mt #_ #_ #IHW12 #IHU12 #K #s #l #m #HLK #X #H #Hlmtl
  elim (lift_inv_bind2 … H) -H #V1 #T1 #HVW1 #HTU1 #H destruct
  elim (IHW12 … HLK … HVW1) -IHW12 // #V2 #HV12 #HVW2
  elim (IHU12 … HTU1) -IHU12 -HTU1
  /3 width=6 by cpy_bind, yle_succ, drop_skip, lift_bind, ex2_intro/
| #I #G #L #W1 #W2 #U1 #U2 #lt #mt #_ #_ #IHW12 #IHU12 #K #s #l #m #HLK #X #H #Hlmtl
  elim (lift_inv_flat2 … H) -H #V1 #T1 #HVW1 #HTU1 #H destruct
  elim (IHW12 … HLK … HVW1) -W1 //
  elim (IHU12 … HLK … HTU1) -U1 -HLK
  /3 width=5 by cpy_flat, lift_flat, ex2_intro/
]
qed-.

lemma cpy_inv_lift1_be: ∀G,L,U1,U2,lt,mt. ⦃G, L⦄ ⊢ U1 ▶[lt, mt] U2 →
                        ∀K,s,l,m. ⬇[s, l, m] L ≡ K → ∀T1. ⬆[l, m] T1 ≡ U1 →
                        lt ≤ l → yinj l + m ≤ lt + mt →
                        ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶[lt, mt-m] T2 & ⬆[l, m] T2 ≡ U2.
#G #L #U1 #U2 #lt #mt #H elim H -G -L -U1 -U2 -lt -mt
[ * #i #G #L #lt #mt #K #s #l #m #_ #T1 #H #_ #_
  [ lapply (lift_inv_sort2 … H) -H #H destruct /2 width=3 by ex2_intro/
  | elim (lift_inv_lref2 … H) -H * #Hil #H destruct /3 width=3 by lift_lref_ge_minus, lift_lref_lt, ex2_intro/
  | lapply (lift_inv_gref2 … H) -H #H destruct /2 width=3 by ex2_intro/
  ]
| #I #G #L #KV #V #W #i #lt #mt #Hlti #Hilmt #HLKV #HVW #K #s #l #m #HLK #T1 #H #Hltl #Hlmlmt
  lapply (yle_fwd_plus_ge_inj … Hltl Hlmlmt) #Hmmt
  elim (lift_inv_lref2 … H) -H * #Hil #H destruct [ -Hltl -Hilmt | -Hlti -Hlmlmt ]
  [ lapply (ylt_yle_trans i l (lt+(mt-m)) ? ?) /2 width=1 by ylt_inj/
    [ >yplus_minus_assoc_inj /2 width=1 by yle_plus1_to_minus_inj2/ ] -Hlmlmt #Hilmtm
    elim (drop_conf_lt … HLK … HLKV) -L // #L #U #HKL #_ #HUV
    elim (lift_trans_le … HUV … HVW) -V // >minus_plus <plus_minus_m_m // -Hil
    /3 width=5 by cpy_subst, ex2_intro/
  | elim (le_inv_plus_l … Hil) #Hlim #Hmi
    lapply (yle_trans … Hltl (i-m) ?) /2 width=1 by yle_inj/ -Hltl #Hltim
    lapply (drop_conf_ge … HLK … HLKV ?) -L // #HKV
    elim (lift_split … HVW l (i-m+1)) -HVW [2,3,4: /2 width=1 by le_S_S, le_S/ ] -Hil -Hlim
    #V1 #HV1 >plus_minus // <minus_minus /2 width=1 by le_S/ <minus_n_n <plus_n_O #H
    @(ex2_intro … H) @(cpy_subst … HKV HV1) // (**) (* explicit constructor *)
    >yplus_minus_assoc_inj /3 width=1 by monotonic_ylt_minus_dx, yle_inj/
  ]
| #a #I #G #L #W1 #W2 #U1 #U2 #lt #mt #_ #_ #IHW12 #IHU12 #K #s #l #m #HLK #X #H #Hltl #Hlmlmt
  elim (lift_inv_bind2 … H) -H #V1 #T1 #HVW1 #HTU1 #H destruct
  elim (IHW12 … HLK … HVW1) -IHW12 // #V2 #HV12 #HVW2
  elim (IHU12 … HTU1) -U1
  /3 width=6 by cpy_bind, drop_skip, lift_bind, yle_succ, ex2_intro/
| #I #G #L #W1 #W2 #U1 #U2 #lt #mt #_ #_ #IHW12 #IHU12 #K #s #l #m #HLK #X #H #Hltl #Hlmlmt
  elim (lift_inv_flat2 … H) -H #V1 #T1 #HVW1 #HTU1 #H destruct
  elim (IHW12 … HLK … HVW1) -W1 //
  elim (IHU12 … HLK … HTU1) -U1 -HLK //
  /3 width=5 by cpy_flat, lift_flat, ex2_intro/
]
qed-.

(* Basic_1: was: subst1_gen_lift_ge *)
lemma cpy_inv_lift1_ge: ∀G,L,U1,U2,lt,mt. ⦃G, L⦄ ⊢ U1 ▶[lt, mt] U2 →
                        ∀K,s,l,m. ⬇[s, l, m] L ≡ K → ∀T1. ⬆[l, m] T1 ≡ U1 →
                        yinj l + m ≤ lt →
                        ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶[lt-m, mt] T2 & ⬆[l, m] T2 ≡ U2.
#G #L #U1 #U2 #lt #mt #H elim H -G -L -U1 -U2 -lt -mt
[ * #i #G #L #lt #mt #K #s #l #m #_ #T1 #H #_
  [ lapply (lift_inv_sort2 … H) -H #H destruct /2 width=3 by ex2_intro/
  | elim (lift_inv_lref2 … H) -H * #Hil #H destruct /3 width=3 by lift_lref_ge_minus, lift_lref_lt, ex2_intro/
  | lapply (lift_inv_gref2 … H) -H #H destruct /2 width=3 by ex2_intro/
  ]
| #I #G #L #KV #V #W #i #lt #mt #Hlti #Hilmt #HLKV #HVW #K #s #l #m #HLK #T1 #H #Hlmlt
  lapply (yle_trans … Hlmlt … Hlti) #Hlmi
  elim (yle_inv_plus_inj2 … Hlmlt) -Hlmlt #_ #Hmlt
  elim (yle_inv_plus_inj2 … Hlmi) #Hlim #Hmi
  lapply (lift_inv_lref2_ge  … H ?) -H /2 width=1 by yle_inv_inj/ #H destruct
  lapply (drop_conf_ge … HLK … HLKV ?) -L /2 width=1 by yle_inv_inj/ #HKV
  elim (lift_split … HVW l (i-m+1)) -HVW [2,3,4: /3 width=1 by yle_inv_inj, le_S_S, le_S/ ] -Hlmi -Hlim
  #V0 #HV10 >plus_minus /2 width=1 by yle_inv_inj/ <minus_minus /3 width=1 by yle_inv_inj, le_S/ <minus_n_n <plus_n_O #H
  @(ex2_intro … H) @(cpy_subst … HKV HV10) (**) (* explicit constructor *)
  [ /2 width=1 by monotonic_yle_minus_dx/
  | <yplus_minus_comm_inj /2 width=1 by monotonic_ylt_minus_dx/
  ]
| #a #I #G #L #W1 #W2 #U1 #U2 #lt #mt #_ #_ #IHW12 #IHU12 #K #s #l #m #HLK #X #H #Hlmtl
  elim (lift_inv_bind2 … H) -H #V1 #T1 #HVW1 #HTU1 #H destruct
  elim (yle_inv_plus_inj2 … Hlmtl) #_ #Hmlt
  elim (IHW12 … HLK … HVW1) -IHW12 // #V2 #HV12 #HVW2
  elim (IHU12 … HTU1) -U1 [4: @drop_skip // |2,5: skip |3: /2 width=1 by yle_succ/ ]
  >yminus_succ1_inj /3 width=5 by cpy_bind, lift_bind, ex2_intro/
| #I #G #L #W1 #W2 #U1 #U2 #lt #mt #_ #_ #IHW12 #IHU12 #K #s #l #m #HLK #X #H #Hlmtl
  elim (lift_inv_flat2 … H) -H #V1 #T1 #HVW1 #HTU1 #H destruct
  elim (IHW12 … HLK … HVW1) -W1 //
  elim (IHU12 … HLK … HTU1) -U1 -HLK /3 width=5 by cpy_flat, lift_flat, ex2_intro/
]
qed-.

(* Advanced inversion lemmas on relocation ***********************************)

lemma cpy_inv_lift1_ge_up: ∀G,L,U1,U2,lt,mt. ⦃G, L⦄ ⊢ U1 ▶[lt, mt] U2 →
                           ∀K,s,l,m. ⬇[s, l, m] L ≡ K → ∀T1. ⬆[l, m] T1 ≡ U1 →
                           l ≤ lt → lt ≤ yinj l + m → yinj l + m ≤ lt + mt →
                           ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶[l, lt + mt - (yinj l + m)] T2 & ⬆[l, m] T2 ≡ U2.
#G #L #U1 #U2 #lt #mt #HU12 #K #s #l #m #HLK #T1 #HTU1 #Hllt #Hltlm #Hlmlmt
elim (cpy_split_up … HU12 (l + m)) -HU12 // -Hlmlmt #U #HU1 #HU2
lapply (cpy_weak … HU1 l m ? ?) -HU1 // [ >ymax_pre_sn_comm // ] -Hllt -Hltlm #HU1
lapply (cpy_inv_lift1_eq … HTU1 … HU1) -HU1 #HU1 destruct
elim (cpy_inv_lift1_ge … HU2 … HLK … HTU1) -U -L /2 width=3 by ex2_intro/
qed-.

lemma cpy_inv_lift1_be_up: ∀G,L,U1,U2,lt,mt. ⦃G, L⦄ ⊢ U1 ▶[lt, mt] U2 →
                           ∀K,s,l,m. ⬇[s, l, m] L ≡ K → ∀T1. ⬆[l, m] T1 ≡ U1 →
                           lt ≤ l → lt + mt ≤ yinj l + m →
                           ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶[lt, l-lt] T2 & ⬆[l, m] T2 ≡ U2.
#G #L #U1 #U2 #lt #mt #HU12 #K #s #l #m #HLK #T1 #HTU1 #Hltl #Hlmtlm
lapply (cpy_weak … HU12 lt (l+m-lt) ? ?) -HU12 //
[ >ymax_pre_sn_comm /2 width=1 by yle_plus_dx1_trans/ ] -Hlmtlm #HU12
elim (cpy_inv_lift1_be … HU12 … HLK … HTU1) -U1 -L /2 width=3 by ex2_intro/
qed-.

lemma cpy_inv_lift1_le_up: ∀G,L,U1,U2,lt,mt. ⦃G, L⦄ ⊢ U1 ▶[lt, mt] U2 →
                           ∀K,s,l,m. ⬇[s, l, m] L ≡ K → ∀T1. ⬆[l, m] T1 ≡ U1 →
                           lt ≤ l → l ≤ lt + mt → lt + mt ≤ yinj l + m →
                           ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶[lt, l - lt] T2 & ⬆[l, m] T2 ≡ U2.
#G #L #U1 #U2 #lt #mt #HU12 #K #s #l #m #HLK #T1 #HTU1 #Hltl #Hllmt #Hlmtlm
elim (cpy_split_up … HU12 l) -HU12 // #U #HU1 #HU2
elim (cpy_inv_lift1_le … HU1 … HLK … HTU1) -U1
[2: >ymax_pre_sn_comm // ] -Hltl #T #HT1 #HTU
lapply (cpy_weak … HU2 l m ? ?) -HU2 //
[ >ymax_pre_sn_comm // ] -Hllmt -Hlmtlm #HU2
lapply (cpy_inv_lift1_eq … HTU … HU2) -L #H destruct /2 width=3 by ex2_intro/
qed-.
