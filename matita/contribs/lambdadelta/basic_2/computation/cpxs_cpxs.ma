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

include "basic_2/reduction/lpx_ldrop.ma".
include "basic_2/computation/cpxs_lift.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL COMPUTATION ON TERMS *****************)

(* Main properties **********************************************************)

theorem cpxs_trans: ∀h,g,L. Transitive … (cpxs h g L).
#h #g #L #T1 #T #HT1 #T2 @trans_TC @HT1 qed-. (**) (* auto /3 width=3/ does not work because a δ-expansion gets in the way *)

theorem cpxs_bind: ∀h,g,a,I,L,V1,V2,T1,T2. ⦃h, L.ⓑ{I}V1⦄ ⊢ T1 ➡*[g] T2 →
                   ⦃h, L⦄ ⊢ V1 ➡*[g] V2 →
                   ⦃h, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡*[g] ⓑ{a,I}V2.T2.
#h #g #a #I #L #V1 #V2 #T1 #T2 #HT12 #H @(cpxs_ind … H) -V2 /2 width=1/
#V #V2 #_ #HV2 #IHV1
@(cpxs_trans … IHV1) -V1 /2 width=1/
qed.

theorem cpxs_flat: ∀h,g,I,L,V1,V2,T1,T2. ⦃h, L⦄ ⊢ T1 ➡*[g] T2 →
                   ⦃h, L⦄ ⊢ V1 ➡*[g] V2 →
                   ⦃h, L⦄ ⊢ ⓕ{I} V1.T1 ➡*[g] ⓕ{I} V2.T2.
#h #g #I #L #V1 #V2 #T1 #T2 #HT12 #H @(cpxs_ind … H) -V2 /2 width=1/
#V #V2 #_ #HV2 #IHV1
@(cpxs_trans … IHV1) -IHV1 /2 width=1/
qed.

theorem cpxs_beta_rc: ∀h,g,a,L,V1,V2,W1,W2,T1,T2.
                      ⦃h, L⦄ ⊢ V1 ➡[g] V2 → ⦃h, L.ⓛW1⦄ ⊢ T1 ➡*[g] T2 → ⦃h, L⦄ ⊢ W1 ➡*[g] W2 →
                      ⦃h, L⦄ ⊢ ⓐV1.ⓛ{a}W1.T1 ➡*[g] ⓓ{a}ⓝW2.V2.T2.
#h #g #a #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HT12 #H @(cpxs_ind … H) -W2 /2 width=1/
#W #W2 #_ #HW2 #IHW1
@(cpxs_trans … IHW1) -IHW1 /3 width=1/
qed.

theorem cpxs_beta: ∀h,g,a,L,V1,V2,W1,W2,T1,T2.
                   ⦃h, L.ⓛW1⦄ ⊢ T1 ➡*[g] T2 → ⦃h, L⦄ ⊢ W1 ➡*[g] W2 → ⦃h, L⦄ ⊢ V1 ➡*[g] V2 →
                   ⦃h, L⦄ ⊢ ⓐV1.ⓛ{a}W1.T1 ➡*[g] ⓓ{a}ⓝW2.V2.T2.
#h #g #a #L #V1 #V2 #W1 #W2 #T1 #T2 #HT12 #HW12 #H @(cpxs_ind … H) -V2 /2 width=1/
#V #V2 #_ #HV2 #IHV1
@(cpxs_trans … IHV1) -IHV1 /3 width=1/
qed.

theorem cpxs_theta_rc: ∀h,g,a,L,V1,V,V2,W1,W2,T1,T2.
                       ⦃h, L⦄ ⊢ V1 ➡[g] V → ⇧[0, 1] V ≡ V2 →
                       ⦃h, L.ⓓW1⦄ ⊢ T1 ➡*[g] T2 → ⦃h, L⦄ ⊢ W1 ➡*[g] W2 →
                       ⦃h, L⦄ ⊢ ⓐV1.ⓓ{a}W1.T1 ➡*[g] ⓓ{a}W2.ⓐV2.T2.
#h #g #a #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 #HT12 #H elim H -W2 /2 width=3/
#W #W2 #_ #HW2 #IHW1
@(cpxs_trans … IHW1) -IHW1 /2 width=1/
qed.

theorem cpxs_theta: ∀h,g,a,L,V1,V,V2,W1,W2,T1,T2.
                    ⇧[0, 1] V ≡ V2 → ⦃h, L⦄ ⊢ W1 ➡*[g] W2 →
                    ⦃h, L.ⓓW1⦄ ⊢ T1 ➡*[g] T2 → ⦃h, L⦄ ⊢ V1 ➡*[g] V →
                    ⦃h, L⦄ ⊢ ⓐV1.ⓓ{a}W1.T1 ➡*[g] ⓓ{a}W2.ⓐV2.T2.
#h #g #a #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV2 #HW12 #HT12 #H @(TC_ind_dx … V1 H) -V1 /2 width=3/
#V1 #V0 #HV10 #_ #IHV0
@(cpxs_trans … IHV0) -IHV0 /2 width=1/
qed.

(* Advanced inversion lemmas ************************************************)

lemma cpxs_inv_appl1: ∀h,g,L,V1,T1,U2. ⦃h, L⦄ ⊢ ⓐV1.T1 ➡*[g] U2 →
                      ∨∨ ∃∃V2,T2.       ⦃h, L⦄ ⊢ V1 ➡*[g] V2 & ⦃h, L⦄ ⊢ T1 ➡*[g] T2 &
                                        U2 = ⓐV2. T2
                       | ∃∃a,W,T.       ⦃h, L⦄ ⊢ T1 ➡*[g] ⓛ{a}W.T & ⦃h, L⦄ ⊢ ⓓ{a}ⓝW.V1.T ➡*[g] U2
                       | ∃∃a,V0,V2,V,T. ⦃h, L⦄ ⊢ V1 ➡*[g] V0 & ⇧[0,1] V0 ≡ V2 &
                                        ⦃h, L⦄ ⊢ T1 ➡*[g] ⓓ{a}V.T & ⦃h, L⦄ ⊢ ⓓ{a}V.ⓐV2.T ➡*[g] U2.
#h #g #L #V1 #T1 #U2 #H @(cpxs_ind … H) -U2 [ /3 width=5/ ]
#U #U2 #_ #HU2 * *
[ #V0 #T0 #HV10 #HT10 #H destruct
  elim (cpx_inv_appl1 … HU2) -HU2 *
  [ #V2 #T2 #HV02 #HT02 #H destruct /4 width=5/
  | #a #V2 #W #W2 #T #T2 #HV02 #HW2 #HT2 #H1 #H2 destruct
    lapply (cpxs_strap1 … HV10 … HV02) -V0 #HV12
    lapply (lsubx_cpx_trans … HT2 (L.ⓓⓝW.V1) ?) -HT2 /2 width=1/ #HT2
    @or3_intro1 @(ex2_3_intro … HT10) -HT10 /3 width=1/ (**) (* explicit constructor. /5 width=8/ is too slow because TC_transitive gets in the way *)
  | #a #V #V2 #W0 #W2 #T #T2 #HV0 #HV2 #HW02 #HT2 #H1 #H2 destruct
    @or3_intro2 @(ex4_5_intro … HV2 HT10) /2 width=3/ /3 width=1/ (**) (* explicit constructor. /5 width=8/ is too slow because TC_transitive gets in the way *)
  ]
| /4 width=9/
| /4 width=11/
]
qed-.

(* Properties on sn extended parallel reduction for local environments ******)

lemma lpx_cpx_trans: ∀h,g. s_r_trans … (cpx h g) (lpx h g).
#h #g #L2 #T1 #T2 #HT12 elim HT12 -L2 -T1 -T2
[ /2 width=3/
| /3 width=2/
| #I #L2 #K2 #V0 #V2 #W2 #i #HLK2 #_ #HVW2 #IHV02 #L1 #HL12
  elim (lpx_ldrop_trans_O1 … HL12 … HLK2) -L2 #X #HLK1 #H
  elim (lpx_inv_pair2 … H) -H #K1 #V1 #HK12 #HV10 #H destruct
  lapply (IHV02 … HK12) -K2 #HV02
  lapply (cpxs_strap2 … HV10 … HV02) -V0 /2 width=7/
| #a #I #L2 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #HL12
  lapply (IHT12 (L1.ⓑ{I}V1) ?) -IHT12 /2 width=1/ /3 width=1/
|5,7,8: /3 width=1/
| #L2 #V2 #T1 #T #T2 #_ #HT2 #IHT1 #L1 #HL12
  lapply (IHT1 (L1.ⓓV2) ?) -IHT1 /2 width=1/ /2 width=3/
| #a #L2 #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #L1 #HL12
  lapply (IHT12 (L1.ⓛW1) ?) -IHT12 /2 width=1/ /3 width=1/
| #a #L2 #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV1 #IHW12 #IHT12 #L1 #HL12
  lapply (IHT12 (L1.ⓓW1) ?) -IHT12 /2 width=1/ /3 width=3/
]
qed-.

lemma cpx_bind2: ∀h,g,L,V1,V2. ⦃h, L⦄ ⊢ V1 ➡[g] V2 →
                 ∀I,T1,T2. ⦃h, L.ⓑ{I}V2⦄ ⊢ T1 ➡[g] T2 →
                 ∀a. ⦃h, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡*[g] ⓑ{a,I}V2.T2.
#h #g #L #V1 #V2 #HV12 #I #T1 #T2 #HT12
lapply (lpx_cpx_trans … HT12 (L.ⓑ{I}V1) ?) /2 width=1/
qed.

(* Advanced properties ******************************************************)

lemma lpx_cpxs_trans: ∀h,g. s_rs_trans … (cpx h g) (lpx h g).
/3 width=5 by s_r_trans_TC1, lpx_cpx_trans/ qed-.

lemma cpxs_bind2_dx: ∀h,g,L,V1,V2. ⦃h, L⦄ ⊢ V1 ➡[g] V2 →
                     ∀I,T1,T2. ⦃h, L.ⓑ{I}V2⦄ ⊢ T1 ➡*[g] T2 →
                     ∀a. ⦃h, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡*[g] ⓑ{a,I}V2.T2.
#h #g #L #V1 #V2 #HV12 #I #T1 #T2 #HT12
lapply (lpx_cpxs_trans … HT12 (L.ⓑ{I}V1) ?) /2 width=1/
qed.
