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

include "basic_2/computation/cpxs_cpxs.ma".
include "basic_2/computation/lpxs.ma".

(* SN EXTENDED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS *******************)

(* Advanced properties ******************************************************)

lemma lpxs_pair: ∀h,g,I,G,L1,L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 →
                 ∀V1,V2. ⦃G, L1⦄ ⊢ V1 ➡*[h, g] V2 →
                 ⦃G, L1.ⓑ{I}V1⦄ ⊢ ➡*[h, g] L2.ⓑ{I}V2.
/2 width=1 by TC_lpx_sn_pair/ qed.

(* Advanced inversion lemmas ************************************************)

lemma lpxs_inv_pair1: ∀h,g,I,G,K1,L2,V1. ⦃G, K1.ⓑ{I}V1⦄ ⊢ ➡*[h, g] L2 →
                      ∃∃K2,V2. ⦃G, K1⦄ ⊢ ➡*[h, g] K2 & ⦃G, K1⦄ ⊢ V1 ➡*[h, g] V2 & L2 = K2.ⓑ{I}V2.
/3 width=3 by TC_lpx_sn_inv_pair1, lpx_cpxs_trans/ qed-.

lemma lpxs_inv_pair2: ∀h,g,I,G,L1,K2,V2. ⦃G, L1⦄ ⊢ ➡*[h, g] K2.ⓑ{I}V2 →
                      ∃∃K1,V1. ⦃G, K1⦄ ⊢ ➡*[h, g] K2 & ⦃G, K1⦄ ⊢ V1 ➡*[h, g] V2 & L1 = K1.ⓑ{I}V1.
/3 width=3 by TC_lpx_sn_inv_pair2, lpx_cpxs_trans/ qed-.

(* Properties on context-sensitive extended parallel computation for terms **)

lemma lpxs_cpx_trans: ∀h,g,G. s_r_trans … (cpx h g G) (lpxs h g G).
/3 width=5 by s_r_trans_TC2, lpx_cpxs_trans/ qed-.

lemma lpxs_cpxs_trans: ∀h,g,G. s_rs_trans … (cpx h g G) (lpxs h g G).
/3 width=5 by s_r_trans_TC1, lpxs_cpx_trans/ qed-.

lemma cpxs_bind2: ∀h,g,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡*[h, g] V2 →
                  ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ➡*[h, g] T2 →
                  ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡*[h, g] ⓑ{a,I}V2.T2.
/4 width=5 by lpxs_cpxs_trans, lpxs_pair, cpxs_bind/ qed.

(* Inversion lemmas on context-sensitive ext parallel computation for terms *)

lemma cpxs_inv_abst1: ∀h,g,a,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓛ{a}V1.T1 ➡*[h, g] U2 →
                      ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡*[h, g] V2 & ⦃G, L.ⓛV1⦄ ⊢ T1 ➡*[h, g] T2 &
                               U2 = ⓛ{a}V2.T2.
#h #g #a #G #L #V1 #T1 #U2 #H @(cpxs_ind … H) -U2 /2 width=5 by ex3_2_intro/
#U0 #U2 #_ #HU02 * #V0 #T0 #HV10 #HT10 #H destruct
elim (cpx_inv_abst1 … HU02) -HU02 #V2 #T2 #HV02 #HT02 #H destruct
lapply (lpxs_cpx_trans … HT02 (L.ⓛV1) ?)
/3 width=5 by lpxs_pair, cpxs_trans, cpxs_strap1, ex3_2_intro/
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
    lapply (lpxs_cpx_trans … HT02 (L.ⓓV1) ?)
    /4 width=5 by lpxs_pair, cpxs_trans, cpxs_strap1, ex3_2_intro, or_introl/
  | #T2 #HT02 #HUT2
    lapply (lpxs_cpx_trans … HT02 (L.ⓓV1) ?) -HT02
    /4 width=3 by lpxs_pair, cpxs_trans, ex3_intro, or_intror/
  ]
| #U1 #HTU1 #HU01
  elim (lift_total U2 0 1) #U #HU2
  /6 width=11 by cpxs_strap1, cpx_lift, ldrop_ldrop, ex3_intro, or_intror/
]
qed-.

(* More advanced properties *************************************************)

lemma lpxs_pair2: ∀h,g,I,G,L1,L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 →
                  ∀V1,V2. ⦃G, L2⦄ ⊢ V1 ➡*[h, g] V2 → ⦃G, L1.ⓑ{I}V1⦄ ⊢ ➡*[h, g] L2.ⓑ{I}V2.
/3 width=3 by lpxs_pair, lpxs_cpxs_trans/ qed.

(* Properties on supclosure *************************************************)

lemma lpxs_fquq_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃⸮ ⦃G2, L2, T2⦄ →
                       ∀K1. ⦃G1, K1⦄ ⊢ ➡*[h, g] L1 →
                       ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡*[h, g] T & ⦃G1, K1, T⦄ ⊃⸮ ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡*[h, g] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #HT12 #K1 #H @(lpxs_ind_dx … H) -K1
[ /2 width=5 by ex3_2_intro/
| #K1 #K #HK1 #_ * #L #T #HT1 #HT2 #HL2 -HT12
  lapply (lpx_cpxs_trans … HT1 … HK1) -HT1
  elim (lpx_fquq_trans … HT2 … HK1) -K
  /3 width=7 by lpxs_strap2, cpxs_strap1, ex3_2_intro/
]
qed-.

lemma lpxs_fqus_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄ →
                       ∀K1. ⦃G1, K1⦄ ⊢ ➡*[h, g] L1 →
                       ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡*[h, g] T & ⦃G1, K1, T⦄ ⊃* ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡*[h, g] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqus_ind … H) -G2 -L2 -T2 /2 width=5 by ex3_2_intro/
#G #G2 #L #L2 #T #T2 #_ #H2 #IH1 #K1 #HLK1 elim (IH1 … HLK1) -L1
#L0 #T0 #HT10 #HT0 #HL0 elim (lpxs_fquq_trans … H2 … HL0) -L
#L #T3 #HT3 #HT32 #HL2 elim (fqus_cpxs_trans … HT0 … HT3) -T
/3 width=7 by cpxs_trans, fqus_strap1, ex3_2_intro/
qed-.

lemma lpx_fqus_trans: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄ →
                      ∀K1. ⦃G1, K1⦄ ⊢ ➡[h, g] L1 →
                      ∃∃K2,T. ⦃G1, K1⦄ ⊢ T1 ➡*[h, g] T & ⦃G1, K1, T⦄ ⊃* ⦃G2, K2, T2⦄ & ⦃G2, K2⦄ ⊢ ➡[h, g] L2.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqus_ind … H) -G2 -L2 -T2 /2 width=5 by ex3_2_intro/
#G #G2 #L #L2 #T #T2 #_ #H2 #IH1 #K1 #HLK1 elim (IH1 … HLK1) -L1
#L0 #T0 #HT10 #HT0 #HL0 elim (lpx_fquq_trans … H2 … HL0) -L
#L #T3 #HT3 #HT32 #HL2 elim (fqus_cpx_trans … HT0 … HT3) -T
/3 width=7 by cpxs_strap1, fqus_strap1, ex3_2_intro/
qed-.