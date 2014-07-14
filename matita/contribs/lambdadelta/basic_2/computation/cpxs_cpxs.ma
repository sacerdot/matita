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

include "basic_2/reduction/lpx_drop.ma".
include "basic_2/computation/cpxs_lift.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL COMPUTATION ON TERMS *****************)

(* Main properties **********************************************************)

theorem cpxs_trans: ∀h,g,G,L. Transitive … (cpxs h g G L).
normalize /2 width=3 by trans_TC/ qed-.

theorem cpxs_bind: ∀h,g,a,I,G,L,V1,V2,T1,T2. ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ➡*[h, g] T2 →
                   ⦃G, L⦄ ⊢ V1 ➡*[h, g] V2 →
                   ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡*[h, g] ⓑ{a,I}V2.T2.
#h #g #a #I #G #L #V1 #V2 #T1 #T2 #HT12 #H @(cpxs_ind … H) -V2
/3 width=5 by cpxs_trans, cpxs_bind_dx/
qed.

theorem cpxs_flat: ∀h,g,I,G,L,V1,V2,T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 →
                   ⦃G, L⦄ ⊢ V1 ➡*[h, g] V2 →
                   ⦃G, L⦄ ⊢ ⓕ{I}V1.T1 ➡*[h, g] ⓕ{I}V2.T2.
#h #g #I #G #L #V1 #V2 #T1 #T2 #HT12 #H @(cpxs_ind … H) -V2
/3 width=5 by cpxs_trans, cpxs_flat_dx/
qed.

theorem cpxs_beta_rc: ∀h,g,a,G,L,V1,V2,W1,W2,T1,T2.
                      ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 → ⦃G, L.ⓛW1⦄ ⊢ T1 ➡*[h, g] T2 → ⦃G, L⦄ ⊢ W1 ➡*[h, g] W2 →
                      ⦃G, L⦄ ⊢ ⓐV1.ⓛ{a}W1.T1 ➡*[h, g] ⓓ{a}ⓝW2.V2.T2.
#h #g #a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HT12 #H @(cpxs_ind … H) -W2
/4 width=5 by cpxs_trans, cpxs_beta_dx, cpxs_bind_dx, cpx_pair_sn/
qed.

theorem cpxs_beta: ∀h,g,a,G,L,V1,V2,W1,W2,T1,T2.
                   ⦃G, L.ⓛW1⦄ ⊢ T1 ➡*[h, g] T2 → ⦃G, L⦄ ⊢ W1 ➡*[h, g] W2 → ⦃G, L⦄ ⊢ V1 ➡*[h, g] V2 →
                   ⦃G, L⦄ ⊢ ⓐV1.ⓛ{a}W1.T1 ➡*[h, g] ⓓ{a}ⓝW2.V2.T2.
#h #g #a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HT12 #HW12 #H @(cpxs_ind … H) -V2
/4 width=5 by cpxs_trans, cpxs_beta_rc, cpxs_bind_dx, cpx_flat/
qed.

theorem cpxs_theta_rc: ∀h,g,a,G,L,V1,V,V2,W1,W2,T1,T2.
                       ⦃G, L⦄ ⊢ V1 ➡[h, g] V → ⇧[0, 1] V ≡ V2 →
                       ⦃G, L.ⓓW1⦄ ⊢ T1 ➡*[h, g] T2 → ⦃G, L⦄ ⊢ W1 ➡*[h, g] W2 →
                       ⦃G, L⦄ ⊢ ⓐV1.ⓓ{a}W1.T1 ➡*[h, g] ⓓ{a}W2.ⓐV2.T2.
#h #g #a #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 #HT12 #H @(cpxs_ind … H) -W2
/3 width=5 by cpxs_trans, cpxs_theta_dx, cpxs_bind_dx/
qed.

theorem cpxs_theta: ∀h,g,a,G,L,V1,V,V2,W1,W2,T1,T2.
                    ⇧[0, 1] V ≡ V2 → ⦃G, L⦄ ⊢ W1 ➡*[h, g] W2 →
                    ⦃G, L.ⓓW1⦄ ⊢ T1 ➡*[h, g] T2 → ⦃G, L⦄ ⊢ V1 ➡*[h, g] V →
                    ⦃G, L⦄ ⊢ ⓐV1.ⓓ{a}W1.T1 ➡*[h, g] ⓓ{a}W2.ⓐV2.T2.
#h #g #a #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV2 #HW12 #HT12 #H @(TC_ind_dx … V1 H) -V1
/3 width=5 by cpxs_trans, cpxs_theta_rc, cpxs_flat_dx/
qed.

(* Advanced inversion lemmas ************************************************)

lemma cpxs_inv_appl1: ∀h,g,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓐV1.T1 ➡*[h, g] U2 →
                      ∨∨ ∃∃V2,T2.       ⦃G, L⦄ ⊢ V1 ➡*[h, g] V2 & ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 &
                                        U2 = ⓐV2. T2
                       | ∃∃a,W,T.       ⦃G, L⦄ ⊢ T1 ➡*[h, g] ⓛ{a}W.T & ⦃G, L⦄ ⊢ ⓓ{a}ⓝW.V1.T ➡*[h, g] U2
                       | ∃∃a,V0,V2,V,T. ⦃G, L⦄ ⊢ V1 ➡*[h, g] V0 & ⇧[0,1] V0 ≡ V2 &
                                        ⦃G, L⦄ ⊢ T1 ➡*[h, g] ⓓ{a}V.T & ⦃G, L⦄ ⊢ ⓓ{a}V.ⓐV2.T ➡*[h, g] U2.
#h #g #G #L #V1 #T1 #U2 #H @(cpxs_ind … H) -U2 [ /3 width=5 by or3_intro0, ex3_2_intro/ ]
#U #U2 #_ #HU2 * *
[ #V0 #T0 #HV10 #HT10 #H destruct
  elim (cpx_inv_appl1 … HU2) -HU2 *
  [ #V2 #T2 #HV02 #HT02 #H destruct /4 width=5 by cpxs_strap1, or3_intro0, ex3_2_intro/
  | #a #V2 #W #W2 #T #T2 #HV02 #HW2 #HT2 #H1 #H2 destruct
    lapply (cpxs_strap1 … HV10 … HV02) -V0 #HV12
    lapply (lsubr_cpx_trans … HT2 (L.ⓓⓝW.V1) ?) -HT2
    /5 width=5 by cpxs_bind, cpxs_flat_dx, cpx_cpxs, lsubr_beta, ex2_3_intro, or3_intro1/
  | #a #V #V2 #W0 #W2 #T #T2 #HV0 #HV2 #HW02 #HT2 #H1 #H2 destruct
    /5 width=10 by cpxs_flat_sn, cpxs_bind_dx, cpxs_strap1, ex4_5_intro, or3_intro2/
  ]
| /4 width=9 by cpxs_strap1, or3_intro1, ex2_3_intro/
| /4 width=11 by cpxs_strap1, or3_intro2, ex4_5_intro/
]
qed-.

(* Properties on sn extended parallel reduction for local environments ******)

lemma lpx_cpx_trans: ∀h,g,G. s_r_transitive … (cpx h g G) (λ_.lpx h g G).
#h #g #G #L2 #T1 #T2 #HT12 elim HT12 -G -L2 -T1 -T2
[ /2 width=3 by/
| /3 width=2 by cpx_cpxs, cpx_st/
| #I #G #L2 #K2 #V0 #V2 #W2 #i #HLK2 #_ #HVW2 #IHV02 #L1 #HL12
  elim (lpx_drop_trans_O1 … HL12 … HLK2) -L2 #X #HLK1 #H
  elim (lpx_inv_pair2 … H) -H #K1 #V1 #HK12 #HV10 #H destruct
  /4 width=7 by cpxs_delta, cpxs_strap2/
|4,9: /4 width=1 by cpxs_beta, cpxs_bind, lpx_pair/
|5,7,8: /3 width=1 by cpxs_flat, cpxs_ct, cpxs_eps/
| /4 width=3 by cpxs_zeta, lpx_pair/
| /4 width=3 by cpxs_theta, cpxs_strap1, lpx_pair/
]
qed-.

lemma cpx_bind2: ∀h,g,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 →
                 ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ➡[h, g] T2 →
                 ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡*[h, g] ⓑ{a,I}V2.T2.
/4 width=5 by lpx_cpx_trans, cpxs_bind_dx, lpx_pair/ qed.

(* Advanced properties ******************************************************)

lemma lpx_cpxs_trans: ∀h,g,G. s_rs_transitive … (cpx h g G) (λ_.lpx h g G).
#h #g #G @s_r_trans_LTC1 /2 width=3 by lpx_cpx_trans/ (**) (* full auto fails *)
qed-.

lemma cpxs_bind2_dx: ∀h,g,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 →
                     ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ➡*[h, g] T2 →
                     ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡*[h, g] ⓑ{a,I}V2.T2.
/4 width=5 by lpx_cpxs_trans, cpxs_bind_dx, lpx_pair/ qed.

(* Properties on supclosure *************************************************)

lemma fqu_cpxs_trans_neq: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                          ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡*[h, g] U2 → (T2 = U2 → ⊥) →
                          ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐ ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #V1 #V2 #HV12 #_ elim (lift_total V2 0 1)
  #U2 #HVU2 @(ex3_intro … U2)
  [1,3: /3 width=7 by fqu_drop, cpxs_delta, drop_pair, drop_drop/
  | #H destruct /2 width=7 by lift_inv_lref2_be/
  ]
| #I #G #L #V1 #T #V2 #HV12 #H @(ex3_intro … (②{I}V2.T))
  [1,3: /2 width=4 by fqu_pair_sn, cpxs_pair_sn/
  | #H0 destruct /2 width=1 by/
  ]
| #a #I #G #L #V #T1 #T2 #HT12 #H @(ex3_intro … (ⓑ{a,I}V.T2))
  [1,3: /2 width=4 by fqu_bind_dx, cpxs_bind/
  | #H0 destruct /2 width=1 by/
  ]
| #I #G #L #V #T1 #T2 #HT12 #H @(ex3_intro … (ⓕ{I}V.T2))
  [1,3: /2 width=4 by fqu_flat_dx, cpxs_flat/
  | #H0 destruct /2 width=1 by/
  ]
| #G #L #K #T1 #U1 #e #HLK #HTU1 #T2 #HT12 #H elim (lift_total T2 0 (e+1))
  #U2 #HTU2 @(ex3_intro … U2)
  [1,3: /2 width=10 by cpxs_lift, fqu_drop/
  | #H0 destruct /3 width=5 by lift_inj/
]
qed-.

lemma fquq_cpxs_trans_neq: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                           ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡*[h, g] U2 → (T2 = U2 → ⊥) →
                           ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐⸮ ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H12 #U2 #HTU2 #H elim (fquq_inv_gen … H12) -H12
[ #H12 elim (fqu_cpxs_trans_neq … H12 … HTU2 H) -T2
  /3 width=4 by fqu_fquq, ex3_intro/
| * #HG #HL #HT destruct /3 width=4 by ex3_intro/
]
qed-.

lemma fqup_cpxs_trans_neq: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                           ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡*[h, g] U2 → (T2 = U2 → ⊥) →
                           ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐+ ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind_dx … H) -G1 -L1 -T1
[ #G1 #L1 #T1 #H12 #U2 #HTU2 #H elim (fqu_cpxs_trans_neq … H12 … HTU2 H) -T2
  /3 width=4 by fqu_fqup, ex3_intro/
| #G #G1 #L #L1 #T #T1 #H1 #_ #IH12 #U2 #HTU2 #H elim (IH12 … HTU2 H) -T2
  #U1 #HTU1 #H #H12 elim (fqu_cpxs_trans_neq … H1 … HTU1 H) -T1
  /3 width=8 by fqup_strap2, ex3_intro/
]
qed-.

lemma fqus_cpxs_trans_neq: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                           ∀U2. ⦃G2, L2⦄ ⊢ T2 ➡*[h, g] U2 → (T2 = U2 → ⊥) →
                           ∃∃U1. ⦃G1, L1⦄ ⊢ T1 ➡*[h, g] U1 & T1 = U1 → ⊥ & ⦃G1, L1, U1⦄ ⊐* ⦃G2, L2, U2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H12 #U2 #HTU2 #H elim (fqus_inv_gen … H12) -H12
[ #H12 elim (fqup_cpxs_trans_neq … H12 … HTU2 H) -T2
  /3 width=4 by fqup_fqus, ex3_intro/
| * #HG #HL #HT destruct /3 width=4 by ex3_intro/
]
qed-.
