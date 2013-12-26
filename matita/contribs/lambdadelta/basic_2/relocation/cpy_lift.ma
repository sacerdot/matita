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

include "basic_2/relocation/ldrop_ldrop.ma".
include "basic_2/relocation/cpy.ma".

(* CONTEXT-SENSITIVE EXTENDED ORDINARY SUBSTITUTION FOR TERMS ***************)

(* Relocation properties ****************************************************)

lemma cpy_lift_le: ∀G,K,T1,T2,dt,et. ⦃G, K⦄ ⊢ T1 ▶×[dt, et] T2 →
                   ∀L,U1,U2,d,e. ⇩[d, e] L ≡ K →
                   ⇧[d, e] T1 ≡ U1 → ⇧[d, e] T2 ≡ U2 →
                   dt + et ≤ d → ⦃G, L⦄ ⊢ U1 ▶×[dt, et] U2.
#G #K #T1 #T2 #dt #et #H elim H -G -K -T1 -T2 -dt -et
[ #I #G #K #dt #et #L #U1 #U2 #d #e #_ #H1 #H2 #_
  >(lift_mono … H1 … H2) -H1 -H2 //
| #I #G #K #KV #V #W #i #dt #et #Hdti #Hidet #HKV #HVW #L #U1 #U2 #d #e #HLK #H #HWU2 #Hdetd
  lapply (lt_to_le_to_lt … Hidet … Hdetd) -Hdetd #Hid
  lapply (lift_inv_lref1_lt … H … Hid) -H #H destruct
  elim (lift_trans_ge … HVW … HWU2) -W // <minus_plus #W #HVW #HWU2
  elim (ldrop_trans_le … HLK … HKV) -K /2 width=2 by lt_to_le/ #X #HLK #H
  elim (ldrop_inv_skip2 … H) -H /2 width=1 by lt_plus_to_minus_r/ -Hid #K #Y #_ #HVY
  >(lift_mono … HVY … HVW) -Y -HVW #H destruct /2 width=5 by cpy_subst/
| #a #I #G #K #V1 #V2 #T1 #T2 #dt #et #_ #_ #IHV12 #IHT12 #L #U1 #U2 #d #e #HLK #H1 #H2 #Hdetd
  elim (lift_inv_bind1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_bind1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct
  /4 width=6 by cpy_bind, ldrop_skip, le_S_S/
| #G #I #K #V1 #V2 #T1 #T2 #dt #et #_ #_ #IHV12 #IHT12 #L #U1 #U2 #d #e #HLK #H1 #H2 #Hdetd
  elim (lift_inv_flat1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_flat1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct
  /3 width=6 by cpy_flat/
]
qed-.

lemma cpy_lift_be: ∀G,K,T1,T2,dt,et. ⦃G, K⦄ ⊢ T1 ▶×[dt, et] T2 →
                   ∀L,U1,U2,d,e. ⇩[d, e] L ≡ K →
                   ⇧[d, e] T1 ≡ U1 → ⇧[d, e] T2 ≡ U2 →
                   dt ≤ d → d ≤ dt + et → ⦃G, L⦄ ⊢ U1 ▶×[dt, et + e] U2.
#G #K #T1 #T2 #dt #et #H elim H -G -K -T1 -T2 -dt -et
[ #I #G #K #dt #et #L #U1 #U2 #d #e #_ #H1 #H2 #_ #_
  >(lift_mono … H1 … H2) -H1 -H2 //
| #I #G #K #KV #V #W #i #dt #et #Hdti #Hidet #HKV #HVW #L #U1 #U2 #d #e #HLK #H #HWU2 #Hdtd #_
  elim (lift_inv_lref1 … H) -H * #Hid #H destruct
  [ -Hdtd
    lapply (lt_to_le_to_lt … (dt+et+e) Hidet ?) // -Hidet #Hidete
    elim (lift_trans_ge … HVW … HWU2) -W // <minus_plus #W #HVW #HWU2
    elim (ldrop_trans_le … HLK … HKV) -K /2 width=2 by lt_to_le/ #X #HLK #H
    elim (ldrop_inv_skip2 … H) -H /2 width=1 by lt_plus_to_minus_r/ -Hid #K #Y #_ #HVY
    >(lift_mono … HVY … HVW) -V #H destruct /2 width=5 by cpy_subst/
  | -Hdti
    lapply (transitive_le … Hdtd Hid) -Hdtd #Hdti
    lapply (lift_trans_be … HVW … HWU2 ? ?) -W /2 width=1 by le_S/ >plus_plus_comm_23 #HVU2
    lapply (ldrop_trans_ge_comm … HLK … HKV ?) -K // -Hid /3 width=5 by cpy_subst, lt_minus_to_plus_r, transitive_le/
  ]
| #a #I #G #K #V1 #V2 #T1 #T2 #dt #et #_ #_ #IHV12 #IHT12 #L #U1 #U2 #d #e #HLK #H1 #H2 #Hdtd #Hddet
  elim (lift_inv_bind1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_bind1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct
  /4 width=6 by cpy_bind, ldrop_skip, le_S_S/ (**) (* auto a bit slow *)
| #I #G #K #V1 #V2 #T1 #T2 #dt #et #_ #_ #IHV12 #IHT12 #L #U1 #U2 #d #e #HLK #H1 #H2 #Hdetd
  elim (lift_inv_flat1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_flat1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct
  /3 width=6 by cpy_flat/
]
qed-.

lemma cpy_lift_ge: ∀G,K,T1,T2,dt,et. ⦃G, K⦄ ⊢ T1 ▶×[dt, et] T2 →
                   ∀L,U1,U2,d,e. ⇩[d, e] L ≡ K →
                   ⇧[d, e] T1 ≡ U1 → ⇧[d, e] T2 ≡ U2 →
                   d ≤ dt → ⦃G, L⦄ ⊢ U1 ▶×[dt + e, et] U2.
#G #K #T1 #T2 #dt #et #H elim H -G -K -T1 -T2 -dt -et
[ #I #G #K #dt #et #L #U1 #U2 #d #e #_ #H1 #H2 #_
  >(lift_mono … H1 … H2) -H1 -H2 //
| #I #G #K #KV #V #W #i #dt #et #Hdti #Hidet #HKV #HVW #L #U1 #U2 #d #e #HLK #H #HWU2 #Hddt
  lapply (transitive_le … Hddt … Hdti) -Hddt #Hid
  lapply (lift_inv_lref1_ge … H … Hid) -H #H destruct
  lapply (lift_trans_be … HVW … HWU2 ? ?) -W /2 width=1 by le_S/ >plus_plus_comm_23 #HVU2
  lapply (ldrop_trans_ge_comm … HLK … HKV ?) -K // -Hid /3 width=5 by cpy_subst, lt_minus_to_plus_r, monotonic_le_plus_l/
| #a #I #G #K #V1 #V2 #T1 #T2 #dt #et #_ #_ #IHV12 #IHT12 #L #U1 #U2 #d #e #HLK #H1 #H2 #Hddt
  elim (lift_inv_bind1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_bind1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct
  /4 width=5 by cpy_bind, ldrop_skip, le_minus_to_plus/
| #I #G #K #V1 #V2 #T1 #T2 #dt #et #_ #_ #IHV12 #IHT12 #L #U1 #U2 #d #e #HLK #H1 #H2 #Hddt
  elim (lift_inv_flat1 … H1) -H1 #VV1 #TT1 #HVV1 #HTT1 #H1
  elim (lift_inv_flat1 … H2) -H2 #VV2 #TT2 #HVV2 #HTT2 #H2 destruct
  /3 width=5 by cpy_flat/
]
qed-.

lemma cpy_inv_lift1_le: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶×[dt, et] U2 →
                        ∀K,d,e. ⇩[d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                        dt + et ≤ d →
                        ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶×[dt, et] T2 & ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et #H elim H -G -L -U1 -U2 -dt -et
[ * #G #L #i #dt #et #K #d #e #_ #T1 #H #_
  [ lapply (lift_inv_sort2 … H) -H #H destruct /2 width=3 by cpy_atom, lift_sort, ex2_intro/
  | elim (lift_inv_lref2 … H) -H * #Hid #H destruct /3 width=3 by cpy_atom, lift_lref_ge_minus, lift_lref_lt, ex2_intro/
  | lapply (lift_inv_gref2 … H) -H #H destruct /2 width=3 by cpy_atom, lift_gref, ex2_intro/
  ]
| #I #G #L #KV #V #W #i #dt #et #Hdti #Hidet #HLKV #HVW #K #d #e #HLK #T1 #H #Hdetd
  lapply (lt_to_le_to_lt … Hidet … Hdetd) -Hdetd #Hid
  lapply (lift_inv_lref2_lt … H … Hid) -H #H destruct
  elim (ldrop_conf_lt … HLK … HLKV ?) -L // #L #U #HKL #_ #HUV
  elim (lift_trans_le … HUV … HVW ?) -V // >minus_plus <plus_minus_m_m // -Hid /3 width=5 by cpy_subst, ex2_intro/
| #a #I #G #L #V1 #V2 #U1 #U2 #dt #et #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H #Hdetd
  elim (lift_inv_bind2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHV12 … HLK … HWV1) -V1 // #W2 #HW12 #HWV2
  elim (IHU12 … HTU1) -IHU12 -HTU1
  /3 width=5 by cpy_bind, ldrop_skip, lift_bind, le_S_S, ex2_intro/
| #I #G #L #V1 #V2 #U1 #U2 #dt #et #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H #Hdetd
  elim (lift_inv_flat2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHV12 … HLK … HWV1) -V1 //
  elim (IHU12 … HLK … HTU1) -U1 -HLK
  /3 width=5 by cpy_flat, lift_flat, ex2_intro/
]
qed-.

lemma cpy_inv_lift1_be: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶×[dt, et] U2 →
                        ∀K,d,e. ⇩[d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                        dt ≤ d → d + e ≤ dt + et →
                        ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶×[dt, et - e] T2 & ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et #H elim H -G -L -U1 -U2 -dt -et
[ * #G #L #i #dt #et #K #d #e #_ #T1 #H #_
  [ lapply (lift_inv_sort2 … H) -H #H destruct /2 width=3 by cpy_atom, lift_sort, ex2_intro/
  | elim (lift_inv_lref2 … H) -H * #Hid #H destruct /3 width=3 by cpy_atom, lift_lref_ge_minus, lift_lref_lt, ex2_intro/
  | lapply (lift_inv_gref2 … H) -H #H destruct /2 width=3 by cpy_atom, lift_gref, ex2_intro/
  ]
| #I #G #L #KV #V #W #i #dt #et #Hdti #Hidet #HLKV #HVW #K #d #e #HLK #T1 #H #Hdtd #Hdedet
  lapply (le_fwd_plus_plus_ge … Hdtd … Hdedet) #Heet
  elim (lift_inv_lref2 … H) -H * #Hid #H destruct
  [ -Hdtd -Hidet
    lapply (lt_to_le_to_lt … (dt + (et - e)) Hid ?) [ <le_plus_minus /2 width=1 by le_plus_to_minus_r/ ] -Hdedet #Hidete
    elim (ldrop_conf_lt … HLK … HLKV) -L // #L #U #HKL #_ #HUV
    elim (lift_trans_le … HUV … HVW) -V // >minus_plus <plus_minus_m_m // -Hid /3 width=5 by cpy_subst, ex2_intro/
  | -Hdti -Hdedet
    lapply (transitive_le … (i - e) Hdtd ?) /2 width=1 by le_plus_to_minus_r/ -Hdtd #Hdtie
    elim (le_inv_plus_l … Hid) #Hdie #Hei
    lapply (ldrop_conf_ge … HLK … HLKV ?) -L // #HKV
    elim (lift_split … HVW d (i-e+1)) -HVW [2,3,4: /2 width=1 by le_S_S, le_S/ ] -Hid -Hdie
    #V1 #HV1 >plus_minus // <minus_minus /2 width=1 by le_S/ <minus_n_n <plus_n_O #H
    @(ex2_intro … H) @(cpy_subst … Hdtie … HKV HV1) (**) (* explicit constructor *)
    >commutative_plus >plus_minus /2 width=1 by monotonic_lt_minus_l/
  ]
| #a #I #G #L #V1 #V2 #U1 #U2 #dt #et #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H #Hdtd #Hdedet
  elim (lift_inv_bind2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHV12 … HLK … HWV1) -V1 // #W2 #HW12 #HWV2
  elim (IHU12 … HTU1) -U1
  [5: /2 width=2 by ldrop_skip/ |2: skip 
  |3: >plus_plus_comm_23 >(plus_plus_comm_23 dt) /2 width=1 by le_S_S/
  |4: /2 width=1 by le_S_S/
  ]
  /3 width=5 by cpy_bind, lift_bind, ex2_intro/
| #I #G #L #V1 #V2 #U1 #U2 #dt #et #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H #Hdtd #Hdedet
  elim (lift_inv_flat2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHV12 … HLK … HWV1) -V1 //
  elim (IHU12 … HLK … HTU1) -U1 -HLK //
  /3 width=5 by cpy_flat, lift_flat, ex2_intro/
]
qed-.

lemma cpy_inv_lift1_ge: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶×[dt, et] U2 →
                        ∀K,d,e. ⇩[d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                        d + e ≤ dt →
                        ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶×[dt - e, et] T2 & ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et #H elim H -G -L -U1 -U2 -dt -et
[ * #G #L #i #dt #et #K #d #e #_ #T1 #H #_
  [ lapply (lift_inv_sort2 … H) -H #H destruct /2 width=3 by cpy_atom, lift_sort, ex2_intro/
  | elim (lift_inv_lref2 … H) -H * #Hid #H destruct /3 width=3 by cpy_atom, lift_lref_ge_minus, lift_lref_lt, ex2_intro/
  | lapply (lift_inv_gref2 … H) -H #H destruct /2 width=3 by cpy_atom, lift_gref, ex2_intro/
  ]
| #I #G #L #KV #V #W #i #dt #et #Hdti #Hidet #HLKV #HVW #K #d #e #HLK #T1 #H #Hdedt
  lapply (transitive_le … Hdedt … Hdti) #Hdei
  elim (le_inv_plus_l … Hdedt) -Hdedt #_ #Hedt
  elim (le_inv_plus_l … Hdei) #Hdie #Hei
  lapply (lift_inv_lref2_ge … H … Hdei) -H #H destruct
  lapply (ldrop_conf_ge … HLK … HLKV ?) -L // #HKV
  elim (lift_split … HVW d (i-e+1)) -HVW [2,3,4: /2 width=1 by le_S_S, le_S/ ] -Hdei -Hdie
  #V0 #HV10 >plus_minus // <minus_minus /2 width=1 by le_S/ <minus_n_n <plus_n_O #H
  @(ex2_intro … H) @(cpy_subst … HKV HV10) /2 width=1 by monotonic_le_minus_l2/ (**) (* explicit constructor *)
  >plus_minus /2 width=1 by monotonic_lt_minus_l/
| #a #I #G #L #V1 #V2 #U1 #U2 #dt #et #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H #Hdetd
  elim (lift_inv_bind2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (le_inv_plus_l … Hdetd) #_ #Hedt
  elim (IHV12 … HLK … HWV1) -V1 // #W2 #HW12 #HWV2
  elim (IHU12 … HTU1) -U1 [4: @ldrop_skip // |2: skip |3: /2 width=1 by le_S_S/ ]
  <plus_minus /3 width=5 by cpy_bind, lift_bind, ex2_intro/
| #I #G #L #V1 #V2 #U1 #U2 #dt #et #_ #_ #IHV12 #IHU12 #K #d #e #HLK #X #H #Hdetd
  elim (lift_inv_flat2 … H) -H #W1 #T1 #HWV1 #HTU1 #H destruct
  elim (IHV12 … HLK … HWV1) -V1 //
  elim (IHU12 … HLK … HTU1) -U1 -HLK /3 width=5 by cpy_flat, lift_flat, ex2_intro/
]
qed-.

lemma cpy_inv_lift1_eq: ∀G,L,U1,U2,d,e.
                        ⦃G, L⦄ ⊢ U1 ▶×[d, e] U2 → ∀T1. ⇧[d, e] T1 ≡ U1 → U1 = U2.
#G #L #U1 #U2 #d #e #H elim H -G -L -U1 -U2 -d -e
[ //
| #I #G #L #K #V #W #i #d #e #Hdi #Hide #_ #_ #T1 #H
  elim (lift_inv_lref2 … H) -H * #H
  [ lapply (le_to_lt_to_lt … Hdi … H) -Hdi -H #H
    elim (lt_refl_false … H)
  | lapply (lt_to_le_to_lt … Hide … H) -Hide -H #H
    elim (lt_refl_false … H)
  ]
| #a #I #G #L #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_bind2 … HX) -HX #V #T #HV1 #HT1 #H destruct
  >IHV12 // >IHT12 //
| #I #G #L #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #X #HX
  elim (lift_inv_flat2 … HX) -HX #V #T #HV1 #HT1 #H destruct
  >IHV12 // >IHT12 //
]
qed-.

lemma cpy_inv_lift1_ge_up: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶×[dt, et] U2 →
                           ∀K,d,e. ⇩[d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                           d ≤ dt → dt ≤ d + e → d + e ≤ dt + et →
                           ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶×[d, dt + et - (d + e)] T2 & ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et #HU12 #K #d #e #HLK #T1 #HTU1 #Hddt #Hdtde #Hdedet
elim (cpy_split_up … HU12 (d + e)) -HU12 // -Hdedet #U #HU1 #HU2
lapply (cpy_weak … HU1 d e ? ?) -HU1 // [ >commutative_plus /2 width=1 by le_minus_to_plus_r/ ] -Hddt -Hdtde #HU1
lapply (cpy_inv_lift1_eq … HU1 … HTU1) -HU1 #HU1 destruct
elim (cpy_inv_lift1_ge … HU2 … HLK … HTU1) -U -L // <minus_plus_m_m /2 width=3 by ex2_intro/
qed-.

lemma cpy_inv_lift1_be_up: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶×[dt, et] U2 →
                           ∀K,d,e. ⇩[d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                           dt ≤ d → dt + et ≤ d + e →
                           ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶×[dt, d - dt] T2 & ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et #HU12 #K #d #e #HLK #T1 #HTU1 #Hdtd #Hdetde
lapply (cpy_weak … HU12 dt (d + e - dt) ? ?) -HU12 /2 width=3 by transitive_le, le_n/ -Hdetde #HU12
elim (cpy_inv_lift1_be … HU12 … HLK … HTU1) -U1 -L /2 width=3 by ex2_intro/
qed-.

lemma cpy_inv_lift1_le_up: ∀G,L,U1,U2,dt,et. ⦃G, L⦄ ⊢ U1 ▶×[dt, et] U2 →
                           ∀K,d,e. ⇩[d, e] L ≡ K → ∀T1. ⇧[d, e] T1 ≡ U1 →
                           dt ≤ d → d ≤ dt + et → dt + et ≤ d + e →
                           ∃∃T2. ⦃G, K⦄ ⊢ T1 ▶×[dt, d - dt] T2 & ⇧[d, e] T2 ≡ U2.
#G #L #U1 #U2 #dt #et #HU12 #K #d #e #HLK #T1 #HTU1 #Hdtd #Hddet #Hdetde
elim (cpy_split_up … HU12 d) -HU12 // #U #HU1 #HU2
elim (cpy_inv_lift1_le … HU1 … HLK … HTU1) -U1 [2: >commutative_plus /2 width=1 by le_minus_to_plus_r/ ] -Hdtd #T #HT1 #HTU
lapply (cpy_weak … HU2 d e ? ?) -HU2 // [ >commutative_plus <plus_minus_m_m // ] -Hddet -Hdetde #HU2
lapply (cpy_inv_lift1_eq … HU2 … HTU) -L #H destruct /2 width=3 by ex2_intro/
qed-.
