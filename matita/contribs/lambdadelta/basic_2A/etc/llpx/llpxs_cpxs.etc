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

include "basic_2/relocation/llpx_sn_tc.ma".
include "basic_2/computation/cpxs_llpx.ma".
include "basic_2/computation/llpxs.ma".

(* LAZY SN EXTENDED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS **************)

(* Advanced properties ******************************************************)

lemma llpxs_pair_dx: ∀h,g,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡*[h, g] V2 →
                     ∀I,T. ⦃G, L.ⓑ{I}V1⦄ ⊢ ➡*[h, g, T, 0] L.ⓑ{I}V2.
/2 width=1 by llpx_sn_TC_pair_dx/ qed.

(* Properties on context-sensitive extended parallel computation for terms **)

lemma llpxs_cpx_trans: ∀h,g,G. s_r_transitive … (cpx h g G) (llpxs h g G 0).
/3 width=5 by s_r_trans_LTC2, llpx_cpxs_trans/ qed-.

lemma llpxs_cpxs_trans: ∀h,g,G. s_rs_transitive … (cpx h g G) (llpxs h g G 0).
#h #g #G @s_r_to_s_rs_trans @s_r_trans_LTC2
/3 width=5 by llpx_cpxs_trans, s_rs_trans_TC1/ (**) (* full auto too slow *)
qed-.

(* Note: this is an instance of a general theorem *)
lemma llpxs_cpxs_conf_dx: ∀h,g,G2,L2,T2,U2. ⦃G2, L2⦄ ⊢ T2 ➡*[h, g] U2 →
                          ∀L0. ⦃G2, L0⦄ ⊢ ➡*[h, g, T2, O] L2 → ⦃G2, L0⦄ ⊢ ➡*[h, g, U2, O] L2.
#h #g #G2 #L2 #T2 #U2 #HTU2 #L0 #H @(llpxs_ind_dx … H) -L0 //
#L0 #L #HL0 #HL2 #IHL2 @(llpxs_strap2 … IHL2) -IHL2
lapply (llpxs_cpxs_trans … HTU2 … HL2) -L2 #HTU2
/3 width=3 by llpx_cpxs_trans, cpxs_llpx_conf/
qed-.

(* Note: this is an instance of a general theorem *)
lemma llpxs_cpx_conf_dx: ∀h,g,G2,L2,T2,U2. ⦃G2, L2⦄ ⊢ T2 ➡[h, g] U2 →
                         ∀L0. ⦃G2, L0⦄ ⊢ ➡*[h, g, T2, O] L2 → ⦃G2, L0⦄ ⊢ ➡*[h, g, U2, O] L2.
#h #g #G2 #L2 #T2 #U2 #HTU2 #L0 #H @(llpxs_ind_dx … H) -L0 //
#L0 #L #HL0 #HL2 #IHL2 @(llpxs_strap2 … IHL2) -IHL2
lapply (llpxs_cpx_trans … HTU2 … HL2) -L2 #HTU2
/3 width=3 by llpx_cpxs_trans, cpxs_llpx_conf/
qed-.

lemma cpxs_bind2: ∀h,g,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡*[h, g] V2 →
                  ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ➡*[h, g] T2 →
                  ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡*[h, g] ⓑ{a,I}V2.T2.
/4 width=5 by llpxs_cpxs_trans, llpxs_pair_dx, cpxs_bind/ qed.

(* Advanced forward lemmas **************************************************)

(* Note: this might be moved *)
lemma llpxs_fwd_lref_ge_sn: ∀h,g,G,L1,L2,d,i. ⦃G, L1⦄ ⊢ ➡*[h, g, #i, d] L2 → d ≤ i →
                            ∀I,K1,V1. ⇩[i] L1 ≡ K1.ⓑ{I}V1 →
                            ∃∃K2,V2. ⇩[i] L2 ≡ K2.ⓑ{I}V2 &
                                     ⦃G, K1⦄ ⊢ ➡*[h, g, V2, 0] K2 & ⦃G, K1⦄ ⊢ V1 ➡*[h, g] V2.
#h #g #G #L1 #L2 #d #i #H #Hdi #I #K1 #V1 #HLK1 @(llpxs_ind … H) -L2 /2 width=5 by ex3_2_intro/ -HLK1
#L #L2 #_ #HL2 * #K #V #HLK #HK1 #HV1 elim (llpx_inv_lref_ge_sn … HL2 … HLK) // -HL2 -HLK -Hdi
#K2 #V2 #HLK2 #HK2 #HV2
@(ex3_2_intro … HLK2) -HLK2
[ /3 width=5 by llpxs_cpx_conf_dx, llpxs_strap1, llpx_cpx_conf/
| /3 width=5 by llpxs_cpx_trans, cpxs_trans/
]
qed-.

(* Inversion lemmas on context-sensitive ext parallel computation for terms *)

lemma cpxs_inv_abst1: ∀h,g,a,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓛ{a}V1.T1 ➡*[h, g] U2 →
                      ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡*[h, g] V2 & ⦃G, L.ⓛV1⦄ ⊢ T1 ➡*[h, g] T2 &
                               U2 = ⓛ{a}V2.T2.
#h #g #a #G #L #V1 #T1 #U2 #H @(cpxs_ind … H) -U2 /2 width=5 by ex3_2_intro/
#U0 #U2 #_ #HU02 * #V0 #T0 #HV10 #HT10 #H destruct
elim (cpx_inv_abst1 … HU02) -HU02 #V2 #T2 #HV02 #HT02 #H destruct
lapply (llpxs_cpx_trans … HT02 (L.ⓛV1) ?)
/3 width=5 by llpxs_pair_dx, cpxs_trans, cpxs_strap1, ex3_2_intro/
qed-.

lemma cpxs_inv_abbr1: ∀h,g,a,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓓ{a}V1.T1 ➡*[h, g] U2 → (
                      ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡*[h, g] V2 & ⦃G, L.ⓓV1⦄ ⊢ T1 ➡*[h, g] T2 &
                               U2 = ⓓ{a}V2.T2
                      ) ∨
                      ∃∃T2. ⦃G, L.ⓓV1⦄ ⊢ T1 ➡*[h, g] T2 & ⇧[0, 1] U2 ≡ T2 & a = true.
#h #g #a #G #L #V1 #T1 #U2 #H @(cpxs_ind … H) -U2 /3 width=5 by ex3_2_intro, or_introl/
#U0 #U2 #_ #HU02 * *
[ #V0 #T0 #HV10 #HT10 #H destruct
  elim (cpx_inv_abbr1 … HU02) -HU02 *
  [ #V2 #T2 #HV02 #HT02 #H destruct
    lapply (llpxs_cpx_trans … HT02 (L.ⓓV1) ?)
    /4 width=5 by llpxs_pair_dx, cpxs_trans, cpxs_strap1, ex3_2_intro, or_introl/
  | #T2 #HT02 #HUT2
    lapply (llpxs_cpx_trans … HT02 (L.ⓓV1) ?) -HT02
    /4 width=3 by llpxs_pair_dx, cpxs_trans, ex3_intro, or_intror/
  ]
| #U1 #HTU1 #HU01
  elim (lift_total U2 0 1) #U #HU2
  /6 width=12 by cpxs_strap1, cpx_lift, ldrop_drop, ex3_intro, or_intror/
]
qed-.

(* Properties on supclosure *************************************************)

lemma llpx_fqup_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃+ ⦃G2, L2, T2⦄ →
                       ∀K1. ⦃G1, K1⦄ ⊢ ➡[h, g, T1, 0] L1 →
                       ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡*[h, g] T & ⦃G1, K1, T⦄ ⊃+ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡[h, g, T2, 0] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
[ #G2 #L2 #T2 #H12 #K1 #HKL1 elim (llpx_fqu_trans … H12 … HKL1) -L1
  /3 width=5 by cpx_cpxs, fqu_fqup, ex3_2_intro/
| #G #G2 #L #L2 #T #T2 #_ #H2 #IH1 #K1 #HLK1 elim (IH1 … HLK1) -L1
  #L0 #T0 #HT10 #HT0 #HL0 elim (llpx_fqu_trans … H2 … HL0) -L
  #L #T3 #HT3 #HT32 #HL2 elim (fqup_cpx_trans … HT0 … HT3) -T
  /3 width=7 by cpxs_strap1, fqup_strap1, ex3_2_intro/
]
qed-.

lemma llpx_fqus_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄ →
                       ∀K1. ⦃G1, K1⦄ ⊢ ➡[h, g, T1, 0] L1 →
                       ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡*[h, g] T & ⦃G1, K1, T⦄ ⊃* ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡[h, g, T2, 0] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqus_ind … H) -G2 -L2 -T2 /2 width=5 by ex3_2_intro/
#G #G2 #L #L2 #T #T2 #_ #H2 #IH1 #K1 #HLK1 elim (IH1 … HLK1) -L1
#L0 #T0 #HT10 #HT0 #HL0 elim (llpx_fquq_trans … H2 … HL0) -L
#L #T3 #HT3 #HT32 #HL2 elim (fqus_cpx_trans … HT0 … HT3) -T
/3 width=7 by cpxs_strap1, fqus_strap1, ex3_2_intro/
qed-.

lemma llpxs_fquq_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ →
                        ∀K1. ⦃G1, K1⦄ ⊢ ➡*[h, g, T1, 0] L1 →
                        ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡*[h, g] T & ⦃G1, K1, T⦄ ⊃⸮ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡*[h, g, T2, 0] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #HT12 #K1 #H @(llpxs_ind_dx … H) -K1
[ /2 width=5 by ex3_2_intro/
| #K1 #K #HK1 #_ * #L #T #HT1 #HT2 #HL2 -HT12
  lapply (llpx_cpxs_trans … HT1 … HK1) -HT1 #HT1
  lapply (cpxs_llpx_conf … HT1 … HK1) -HK1 #HK1
  elim (llpx_fquq_trans … HT2 … HK1) -K
  /3 width=7 by llpxs_strap2, cpxs_strap1, ex3_2_intro/
]
qed-.

lemma llpxs_fqup_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃+ ⦃G2, L2, T2⦄ →
                        ∀K1. ⦃G1, K1⦄ ⊢ ➡*[h, g, T1, 0] L1 →
                        ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡*[h, g] T & ⦃G1, K1, T⦄ ⊃+ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡*[h, g, T2, 0] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #HT12 #K1 #H @(llpxs_ind_dx … H) -K1
[ /2 width=5 by ex3_2_intro/
| #K1 #K #HK1 #_ * #L #T #HT1 #HT2 #HL2 -HT12
  lapply (llpx_cpxs_trans … HT1 … HK1) -HT1 #HT1
  lapply (cpxs_llpx_conf … HT1 … HK1) -HK1 #HK1
  elim (llpx_fqup_trans … HT2 … HK1) -K
  /3 width=7 by llpxs_strap2, cpxs_trans, ex3_2_intro/
]
qed-.

lemma llpxs_fqus_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄ →
                        ∀K1. ⦃G1, K1⦄ ⊢ ➡*[h, g, T1, 0] L1 →
                        ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡*[h, g] T & ⦃G1, K1, T⦄ ⊃* ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡*[h, g, T2, 0] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #HT12 #K1 #H @(llpxs_ind_dx … H) -K1
[ /2 width=5 by ex3_2_intro/
| #K1 #K #HK1 #_ * #L #T #HT1 #HT2 #HL2 -HT12
  lapply (llpx_cpxs_trans … HT1 … HK1) -HT1 #HT1
  lapply (cpxs_llpx_conf … HT1 … HK1) -HK1 #HK1
  elim (llpx_fqus_trans … HT2 … HK1) -K
  /3 width=7 by llpxs_strap2, cpxs_trans, ex3_2_intro/
]
qed-.
