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

include "basic_2/rt_transition/cpx_fqus.ma".
include "basic_2/rt_transition/lpx_fquq.ma".
include "basic_2/rt_computation/cpxs_drops.ma".
include "basic_2/rt_computation/cpxs_cpxs.ma".

(* UNBOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Properties with unbound rt-transition for full local environments ********)

lemma lpx_cpx_trans: ∀h,G. s_r_transitive … (cpx h G) (λ_.lpx h G).
#h #G #L2 #T1 #T2 #H @(cpx_ind … H) -G -L2 -T1 -T2
[ /2 width=3 by/
| /3 width=2 by cpx_cpxs, cpx_ess/
| #I #G #K2 #V2 #V4 #W4 #_ #IH #HVW4 #L1 #H
  elim (lpx_inv_pair_dx … H) -H #K1 #V1 #HK12 #HV12 #H destruct
  /4 width=3 by cpxs_delta, cpxs_strap2/
| #I2 #G #K2 #T #U #i #_ #IH #HTU #L1 #H
  elim (lpx_inv_bind_dx … H) -H #I1 #K1 #HK12 #HI12 #H destruct
  /4 width=3 by cpxs_lref, cpxs_strap2/
|5,10: /4 width=1 by cpxs_beta, cpxs_bind, lpx_bind_refl_dx/
|6,8,9: /3 width=1 by cpxs_flat, cpxs_ee, cpxs_eps/
| /4 width=3 by cpxs_zeta, lpx_bind_refl_dx/
| /4 width=3 by cpxs_theta, cpxs_strap1, lpx_bind_refl_dx/
]
qed-.

lemma lpx_cpxs_trans: ∀h,G. s_rs_transitive … (cpx h G) (λ_.lpx h G).
#h #G @s_r_trans_CTC1 /2 width=3 by lpx_cpx_trans/ (**) (* full auto fails *)
qed-.

(* Advanced properties ******************************************************)

lemma cpx_bind2: ∀h,G,L,V1,V2. ❪G,L❫ ⊢ V1 ⬈[h] V2 →
                 ∀I,T1,T2. ❪G,L.ⓑ[I]V2❫ ⊢ T1 ⬈[h] T2 →
                 ∀p. ❪G,L❫ ⊢ ⓑ[p,I]V1.T1 ⬈*[h] ⓑ[p,I]V2.T2.
/4 width=5 by lpx_cpx_trans, cpxs_bind_dx, lpx_pair/ qed.

lemma cpxs_bind2_dx: ∀h,G,L,V1,V2. ❪G,L❫ ⊢ V1 ⬈[h] V2 →
                     ∀I,T1,T2. ❪G,L.ⓑ[I]V2❫ ⊢ T1 ⬈*[h] T2 →
                     ∀p. ❪G,L❫ ⊢ ⓑ[p,I]V1.T1 ⬈*[h] ⓑ[p,I]V2.T2.
/4 width=5 by lpx_cpxs_trans, cpxs_bind_dx, lpx_pair/ qed.

(* Properties with plus-iterated structural successor for closures **********)

(* Basic_2A1: uses: lpx_fqup_trans *)
lemma lpx_fqup_trans: ∀h,b,G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ⬂+[b] ❪G2,L2,T2❫ →
                      ∀K1. ❪G1,K1❫ ⊢ ⬈[h] L1 →
                      ∃∃K2,T. ❪G1,K1❫ ⊢ T1 ⬈*[h] T & ❪G1,K1,T❫ ⬂+[b] ❪G2,K2,T2❫ & ❪G2,K2❫ ⊢ ⬈[h] L2.
#h #b #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
[ #G2 #L2 #T2 #H12 #K1 #HKL1 elim (lpx_fqu_trans … H12 … HKL1) -L1
  /3 width=5 by cpx_cpxs, fqu_fqup, ex3_2_intro/
| #G #G2 #L #L2 #T #T2 #_ #H2 #IH1 #K1 #HLK1 elim (IH1 … HLK1) -L1
  #L0 #T0 #HT10 #HT0 #HL0 elim (lpx_fqu_trans … H2 … HL0) -L
  #L #T3 #HT3 #HT32 #HL2 elim (fqup_cpx_trans … HT0 … HT3) -T
  /3 width=7 by cpxs_strap1, fqup_strap1, ex3_2_intro/
]
qed-.

(* Properties with star-iterated structural successor for closures **********)

(* Basic_2A1: uses: lpx_fqus_trans *)
lemma lpx_fqus_trans: ∀h,b,G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ⬂*[b] ❪G2,L2,T2❫ →
                      ∀K1. ❪G1,K1❫ ⊢ ⬈[h] L1 →
                      ∃∃K2,T. ❪G1,K1❫ ⊢ T1 ⬈*[h] T & ❪G1,K1,T❫ ⬂*[b] ❪G2,K2,T2❫ & ❪G2,K2❫ ⊢ ⬈[h] L2.
#h #b #G1 #G2 #L1 #L2 #T1 #T2 #H #K1 #HKL1 elim (fqus_inv_fqup … H) -H
[ #H12 elim (lpx_fqup_trans … H12 … HKL1) -L1 /3 width=5 by fqup_fqus, ex3_2_intro/
| * #H1 #H2 #H3 destruct /2 width=5 by ex3_2_intro/
]
qed-.
