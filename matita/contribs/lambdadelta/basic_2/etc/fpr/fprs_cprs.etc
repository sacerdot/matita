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

include "basic_2/reducibility/fpr_cpr.ma".
include "basic_2/computation/cprs_lfprs.ma".
include "basic_2/computation/lfprs_ltprs.ma".
include "basic_2/computation/lfprs_fprs.ma".

(* CONTEXT-FREE PARALLEL COMPUTATION ON CLOSURES ****************************)

(* Advanced properties ******************************************************)

lemma fprs_flat_dx_tpr: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ➡* ⦃L2, T2⦄ → ∀V1,V2. V1 ➡ V2 →
                        ∀I. ⦃L1, ⓕ{I}V1.T1⦄ ➡* ⦃L2, ⓕ{I}V2.T2⦄.
#L1 #L2 #T1 #T2 #HT12 @(fprs_ind … HT12) -L2 -T2 /3 width=1/
#L #L2 #T #T2 #_ #HT2 #IHT2 #V1 #V2 #HV12 #I
lapply (IHT2 … HV12 I) -IHT2 -HV12 /3 width=6/
qed.

lemma fprs_bind2_minus: ∀I,L1,L2,V1,T1,U2. ⦃L1, -ⓑ{I}V1.T1⦄ ➡* ⦃L2, U2⦄ →
                        ∃∃V2,T2. ⦃L1.ⓑ{I}V1, T1⦄ ➡* ⦃L2.ⓑ{I}V2, T2⦄ &
                                 U2 = -ⓑ{I}V2.T2.
#I #L1 #L2 #V1 #T1 #U2 #H @(fprs_ind … H) -L2 -U2 /2 width=4/
#L #L2 #U #U2 #_ #HU2 * #V #T #HT1 #H destruct
elim (fpr_bind2_minus … HU2) -HU2 /3 width=4/
qed-.

lemma fprs_lift: ∀K1,K2,T1,T2. ⦃K1, T1⦄ ➡* ⦃K2, T2⦄ →
                 ∀d,e,L1. ⇩[d, e] L1 ≡ K1 →
                 ∀U1,U2. ⇧[d, e] T1 ≡ U1 → ⇧[d, e] T2 ≡ U2 →
                 ∃∃L2. ⦃L1, U1⦄ ➡* ⦃L2, U2⦄ & ⇩[d, e] L2 ≡ K2.
#K1 #K2 #T1 #T2 #HT12 @(fprs_ind … HT12) -K2 -T2
[ #d #e #L1 #HLK1 #U1 #U2 #HTU1 #HTU2
  >(lift_mono … HTU2 … HTU1) -U2 /2 width=3/
| #K #K2 #T #T2 #_ #HT2 #IHT1 #d #e #L1 #HLK1 #U1 #U2 #HTU1 #HTU2
  elim (lift_total T d e) #U #HTU
  elim (IHT1 … HLK1 … HTU1 HTU) -K1 -T1 #L #HU1 #HKL
  elim (fpr_lift … HT2 … HKL … HTU HTU2) -K -T -T2 /3 width=4/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma fprs_inv_pair1: ∀I,K1,L2,V1,T1,T2. ⦃K1.ⓑ{I}V1, T1⦄ ➡* ⦃L2, T2⦄ →
                      ∃∃K2,V2. ⦃K1, V1⦄  ➡* ⦃K2, V2⦄ &
                               ⦃K1, -ⓑ{I}V1.T1⦄ ➡* ⦃K2, -ⓑ{I}V2.T2⦄  &
                               L2 = K2.ⓑ{I}V2.
#I #K1 #L2 #V1 #T1 #T2 #H @(fprs_ind … H) -L2 -T2 /2 width=5/
#L #L2 #T #T2 #_ #HT2 * #K #V #HV1 #HT1 #H destruct
elim (fpr_inv_pair1 … HT2) -HT2 #K2 #V2 #HV2 #HT2 #H destruct /3 width=5/
qed-.

lemma fprs_inv_pair3: ∀I,L1,K2,V2,T1,T2. ⦃L1, T1⦄ ➡* ⦃K2.ⓑ{I}V2, T2⦄ →
                      ∃∃K1,V1. ⦃K1, V1⦄  ➡* ⦃K2, V2⦄ &
                               ⦃K1, -ⓑ{I}V1.T1⦄ ➡* ⦃K2, -ⓑ{I}V2.T2⦄  &
                               L1 = K1.ⓑ{I}V1.
#I2 #L1 #K2 #V2 #T1 #T2 #H @(fprs_ind_dx … H) -L1 -T1 /2 width=5/
#L1 #L #T1 #T #HT1 #_ * #K #V #HV2 #HT2 #H destruct
elim (fpr_inv_pair3 … HT1) -HT1 #K1 #V1 #HV1 #HT1 #H destruct /3 width=5/
qed-.

(* Advanced forward lemmas **************************************************)

lemma fprs_fwd_bind2_minus: ∀I,L1,L,V1,T1,T. ⦃L1, -ⓑ{I}V1.T1⦄ ➡* ⦃L, T⦄ → ∀b.
                            ∃∃V2,T2. ⦃L1, ⓑ{b,I}V1.T1⦄ ➡* ⦃L, ⓑ{b,I}V2.T2⦄ &
                                     T = -ⓑ{I}V2.T2.
#I #L1 #L #V1 #T1 #T #H1 #b @(fprs_ind … H1) -L -T /2 width=4/
#L0 #L #T0 #T #_ #H0 * #W1 #U1 #HTU1 #H destruct
elim (fpr_fwd_bind2_minus … H0 b) -H0 /3 width=4/
qed-.

lemma fprs_fwd_pair1_full: ∀I,K1,L2,V1,T1,T2. ⦃K1.ⓑ{I}V1, T1⦄ ➡* ⦃L2, T2⦄ →
                           ∀b. ∃∃K2,V2. ⦃K1, V1⦄  ➡* ⦃K2, V2⦄ &
                                        ⦃K1, ⓑ{b,I}V1.T1⦄ ➡* ⦃K2, ⓑ{b,I}V2.T2⦄ &
                                        L2 = K2.ⓑ{I}V2.
#I #K1 #L2 #V1 #T1 #T2 #H #b
elim (fprs_inv_pair1 … H) -H #K2 #V2 #HV12 #HT12 #H destruct
elim (fprs_fwd_bind2_minus … HT12 b) -HT12 #W1 #U1 #HTU1 #H destruct /2 width=5/
qed-.

lemma fprs_fwd_abst2: ∀a,L1,L2,V1,T1,U2. ⦃L1, ⓛ{a}V1.T1⦄ ➡* ⦃L2, U2⦄ → ∀b,I,W.
                      ∃∃V2,T2. ⦃L1, ⓑ{b,I}W.T1⦄ ➡* ⦃L2, ⓑ{b,I}W.T2⦄ &
                               U2 = ⓛ{a}V2.T2.
#a #L1 #L2 #V1 #T1 #U2 #H #b #I #W @(fprs_ind … H) -L2 -U2 /2 width=4/
#L #L2 #U #U2 #_ #H2 * #V #T #HT1 #H destruct
elim (fpr_fwd_abst2 … H2 b I W) -H2 /3 width=4/
qed-.

(* Properties on context-sensitive parallel computation for terms ***********)

lemma cprs_fprs: ∀L,T1,T2. L ⊢ T1 ➡* T2 → ⦃L, T1⦄ ➡* ⦃L, T2⦄.
#L #T1 #T2 #H @(cprs_ind … H) -T2 // /3 width=4/
qed.

(* Forward lemmas on context-sensitive parallel computation for terms *******)

lemma fprs_fwd_cprs: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ➡* ⦃L2, T2⦄ → L1 ⊢ T1 ➡* T2.
#L1 #L2 #T1 #T2 #H @(fprs_ind … H) -L2 -T2 //
#L #L2 #T #T2 #H1 #H2 #IH1
elim (fpr_inv_all … H2) -H2 #L0 #HL0 #HT2 #_ -L2
lapply (lfprs_cpr_trans L1 … HT2) -HT2 /3 width=3/
qed-.
(*
(* Advanced properties ******************************************************)

lamma fpr_bind_sn: ∀L1,L2,V1,V2. ⦃L1, V1⦄ ➡ ⦃L2, V2⦄ → ∀T1,T2. T1 ➡ T2 →
                   ∀a,I. ⦃L1, ⓑ{a,I}V1.T1⦄ ➡ ⦃L2, ⓑ{a,I}V2.T2⦄.
#L1 #L2 #V1 #V2 #H #T1 #T2 #HT12 #a #I
elim (fpr_inv_all … H) /3 width=4/
qed.

(* Advanced forward lemmas **************************************************)

lamma fpr_fwd_shift_bind_minus: ∀I1,I2,L1,L2,V1,V2,T1,T2.
                                ⦃L1, -ⓑ{I1}V1.T1⦄ ➡ ⦃L2, -ⓑ{I2}V2.T2⦄ →
                                ⦃L1, V1⦄ ➡ ⦃L2, V2⦄ ∧ I1 = I2.
* #I2 #L1 #L2 #V1 #V2 #T1 #T2 #H
elim (fpr_inv_all … H) -H #L #HL1 #H #HL2
[ elim (cpr_inv_abbr1 … H) -H *
  [ #V #V0 #T #HV1 #HV0 #_ #H destruct /4 width=4/
  | #T #_ #_ #H destruct
  ]
| elim (cpr_inv_abst1 … H Abst V2) -H
  #V #T #HV1 #_ #H destruct /3 width=4/
]
qed-.
*)
