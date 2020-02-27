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

include "ground/xoa/ex_4_5.ma".
include "basic_2/rt_transition/cpx_lsubr.ma".
include "basic_2/rt_computation/cpxs.ma".

(* UNBOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Main properties **********************************************************)

theorem cpxs_trans: ∀h,G,L. Transitive … (cpxs h G L).
normalize /2 width=3 by trans_TC/ qed-.

theorem cpxs_bind: ∀h,p,I,G,L,V1,V2,T1,T2. ❪G,L.ⓑ[I]V1❫ ⊢ T1 ⬈*[h] T2 →
                   ❪G,L❫ ⊢ V1 ⬈*[h] V2 →
                   ❪G,L❫ ⊢ ⓑ[p,I]V1.T1 ⬈*[h] ⓑ[p,I]V2.T2.
#h #p #I #G #L #V1 #V2 #T1 #T2 #HT12 #H @(cpxs_ind … H) -V2
/3 width=5 by cpxs_trans, cpxs_bind_dx/
qed.

theorem cpxs_flat: ∀h,I,G,L,V1,V2,T1,T2. ❪G,L❫ ⊢ T1 ⬈*[h] T2 →
                   ❪G,L❫ ⊢ V1 ⬈*[h] V2 →
                   ❪G,L❫ ⊢ ⓕ[I]V1.T1 ⬈*[h] ⓕ[I]V2.T2.
#h #I #G #L #V1 #V2 #T1 #T2 #HT12 #H @(cpxs_ind … H) -V2
/3 width=5 by cpxs_trans, cpxs_flat_dx/
qed.

theorem cpxs_beta_rc: ∀h,p,G,L,V1,V2,W1,W2,T1,T2.
                      ❪G,L❫ ⊢ V1 ⬈[h] V2 → ❪G,L.ⓛW1❫ ⊢ T1 ⬈*[h] T2 → ❪G,L❫ ⊢ W1 ⬈*[h] W2 →
                      ❪G,L❫ ⊢ ⓐV1.ⓛ[p]W1.T1 ⬈*[h] ⓓ[p]ⓝW2.V2.T2.
#h #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HT12 #H @(cpxs_ind … H) -W2
/4 width=5 by cpxs_trans, cpxs_beta_dx, cpxs_bind_dx, cpx_pair_sn/
qed.

theorem cpxs_beta: ∀h,p,G,L,V1,V2,W1,W2,T1,T2.
                   ❪G,L.ⓛW1❫ ⊢ T1 ⬈*[h] T2 → ❪G,L❫ ⊢ W1 ⬈*[h] W2 → ❪G,L❫ ⊢ V1 ⬈*[h] V2 →
                   ❪G,L❫ ⊢ ⓐV1.ⓛ[p]W1.T1 ⬈*[h] ⓓ[p]ⓝW2.V2.T2.
#h #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HT12 #HW12 #H @(cpxs_ind … H) -V2
/4 width=5 by cpxs_trans, cpxs_beta_rc, cpxs_bind_dx, cpx_flat/
qed.

theorem cpxs_theta_rc: ∀h,p,G,L,V1,V,V2,W1,W2,T1,T2.
                       ❪G,L❫ ⊢ V1 ⬈[h] V → ⇧[1] V ≘ V2 →
                       ❪G,L.ⓓW1❫ ⊢ T1 ⬈*[h] T2 → ❪G,L❫ ⊢ W1 ⬈*[h] W2 →
                       ❪G,L❫ ⊢ ⓐV1.ⓓ[p]W1.T1 ⬈*[h] ⓓ[p]W2.ⓐV2.T2.
#h #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 #HT12 #H @(cpxs_ind … H) -W2
/3 width=5 by cpxs_trans, cpxs_theta_dx, cpxs_bind_dx/
qed.

theorem cpxs_theta: ∀h,p,G,L,V1,V,V2,W1,W2,T1,T2.
                    ⇧[1] V ≘ V2 → ❪G,L❫ ⊢ W1 ⬈*[h] W2 →
                    ❪G,L.ⓓW1❫ ⊢ T1 ⬈*[h] T2 → ❪G,L❫ ⊢ V1 ⬈*[h] V →
                    ❪G,L❫ ⊢ ⓐV1.ⓓ[p]W1.T1 ⬈*[h] ⓓ[p]W2.ⓐV2.T2.
#h #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV2 #HW12 #HT12 #H @(TC_ind_dx … V1 H) -V1
/3 width=5 by cpxs_trans, cpxs_theta_rc, cpxs_flat_dx/
qed.

(* Advanced inversion lemmas ************************************************)

lemma cpxs_inv_appl1: ∀h,G,L,V1,T1,U2. ❪G,L❫ ⊢ ⓐV1.T1 ⬈*[h] U2 →
                      ∨∨ ∃∃V2,T2.       ❪G,L❫ ⊢ V1 ⬈*[h] V2 & ❪G,L❫ ⊢ T1 ⬈*[h] T2 &
                                        U2 = ⓐV2.T2
                       | ∃∃p,W,T.       ❪G,L❫ ⊢ T1 ⬈*[h] ⓛ[p]W.T & ❪G,L❫ ⊢ ⓓ[p]ⓝW.V1.T ⬈*[h] U2
                       | ∃∃p,V0,V2,V,T. ❪G,L❫ ⊢ V1 ⬈*[h] V0 & ⇧[1] V0 ≘ V2 &
                                        ❪G,L❫ ⊢ T1 ⬈*[h] ⓓ[p]V.T & ❪G,L❫ ⊢ ⓓ[p]V.ⓐV2.T ⬈*[h] U2.
#h #G #L #V1 #T1 #U2 #H @(cpxs_ind … H) -U2 [ /3 width=5 by or3_intro0, ex3_2_intro/ ]
#U #U2 #_ #HU2 * *
[ #V0 #T0 #HV10 #HT10 #H destruct
  elim (cpx_inv_appl1 … HU2) -HU2 *
  [ #V2 #T2 #HV02 #HT02 #H destruct /4 width=5 by cpxs_strap1, or3_intro0, ex3_2_intro/
  | #p #V2 #W #W2 #T #T2 #HV02 #HW2 #HT2 #H1 #H2 destruct
    lapply (cpxs_strap1 … HV10 … HV02) -V0 #HV12
    lapply (lsubr_cpx_trans … HT2 (L.ⓓⓝW.V1) ?) -HT2
    /5 width=5 by cpxs_bind, cpxs_flat_dx, cpx_cpxs, lsubr_beta, ex2_3_intro, or3_intro1/
  | #p #V #V2 #W0 #W2 #T #T2 #HV0 #HV2 #HW02 #HT2 #H1 #H2 destruct
    /5 width=10 by cpxs_flat_sn, cpxs_bind_dx, cpxs_strap1, ex4_5_intro, or3_intro2/
  ]
| /4 width=9 by cpxs_strap1, or3_intro1, ex2_3_intro/
| /4 width=11 by cpxs_strap1, or3_intro2, ex4_5_intro/
]
qed-.
