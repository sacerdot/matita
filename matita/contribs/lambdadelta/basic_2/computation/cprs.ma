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

include "basic_2/reduction/cnf.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Basic_1: includes: pr1_pr0 *)
definition cprs: lenv → relation term ≝ LTC … cpr.

interpretation "context-sensitive parallel computation (term)"
   'PRedStar L T1 T2 = (cprs L T1 T2).

(* Basic eliminators ********************************************************)

lemma cprs_ind: ∀L,T1. ∀R:predicate term. R T1 →
                (∀T,T2. L ⊢ T1 ➡* T → L ⊢ T ➡ T2 → R T → R T2) →
                ∀T2. L ⊢ T1 ➡* T2 → R T2.
#L #T1 #R #HT1 #IHT1 #T2 #HT12
@(TC_star_ind … HT1 IHT1 … HT12) //
qed-.

lemma cprs_ind_dx: ∀L,T2. ∀R:predicate term. R T2 →
                   (∀T1,T. L ⊢ T1 ➡ T → L ⊢ T ➡* T2 → R T → R T1) →
                   ∀T1. L ⊢ T1 ➡* T2 → R T1.
#L #T2 #R #HT2 #IHT2 #T1 #HT12
@(TC_star_ind_dx … HT2 IHT2 … HT12) //
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: pr3_pr2 *)
lemma cpr_cprs: ∀L,T1,T2. L ⊢ T1 ➡ T2 → L ⊢ T1 ➡* T2.
/2 width=1/ qed.

lemma cpss_cprs: ∀L,T1,T2. L ⊢ T1 ▶* T2 → L ⊢ T1 ➡* T2.
/3 width=1/ qed.

(* Basic_1: was: pr3_refl *)
lemma cprs_refl: ∀L,T. L ⊢ T ➡* T.
/2 width=1/ qed.

lemma cprs_strap1: ∀L,T1,T,T2.
                   L ⊢ T1 ➡* T → L ⊢ T ➡ T2 → L ⊢ T1 ➡* T2.
normalize /2 width=3/ qed.

(* Basic_1: was: pr3_step *)
lemma cprs_strap2: ∀L,T1,T,T2.
                   L ⊢ T1 ➡ T → L ⊢ T ➡* T2 → L ⊢ T1 ➡* T2.
normalize /2 width=3/ qed.

lemma cprs_cpss_trans: ∀L,T1,T. L ⊢ T1 ➡* T → ∀T2. L ⊢ T ▶* T2 → L ⊢ T1 ➡* T2.
/3 width=3/ qed-.

lemma cpss_cprs_trans: ∀L,T1,T. L ⊢ T1 ▶* T → ∀T2. L ⊢ T ➡* T2 → L ⊢ T1 ➡* T2.
/3 width=3/ qed-.

lemma cprs_lsubr_trans: lsubr_trans … cprs.
/3 width=3 by cpr_lsubr_trans, TC_lsubr_trans/
qed-.

(* Basic_1: was: pr3_pr1 *)
lemma tprs_cprs: ∀L,T1,T2. ⋆ ⊢ T1 ➡* T2 → L ⊢ T1 ➡* T2.
#L #T1 #T2 #H @(cprs_lsubr_trans … H) -H //
qed.

lemma cprs_ext_bind_dx: ∀L,V1,V2. L ⊢ V1 ➡ V2 → ∀V,T1,T2. L.ⓛV ⊢ T1 ➡* T2 →
                        ∀a,I. L ⊢ ⓑ{a,I}V1.T1 ➡* ⓑ{a,I}V2.T2.
#L #V1 #V2 #HV12 #V #T1 #T2 #HT12 #a @(cprs_ind … HT12) -T2
/3 width=1/ /3 width=6/
qed.

lemma cprs_bind_dx: ∀L,V1,V2. L ⊢ V1 ➡ V2 → ∀I,T1,T2. L. ⓑ{I}V1 ⊢ T1 ➡* T2 →
                    ∀a. L ⊢ ⓑ{a,I}V1. T1 ➡* ⓑ{a,I}V2. T2.
#L #V1 #V2 #HV12 #I #T1 #T2 #HT12 #a @(cprs_ind_dx … HT12) -T1
/3 width=1/ /3 width=3/
qed.

(* Basic_1: was only: pr3_thin_dx *)
lemma cprs_flat_dx: ∀I,L,V1,V2. L ⊢ V1 ➡ V2 → ∀T1,T2. L ⊢ T1 ➡* T2 →
                    L ⊢ ⓕ{I} V1. T1 ➡* ⓕ{I} V2. T2.
#I #L #V1 #V2 #HV12 #T1 #T2 #HT12 @(cprs_ind … HT12) -T2 /3 width=1/
#T #T2 #_ #HT2 #IHT1
@(cprs_strap1 … IHT1) -V1 -T1 /2 width=1/
qed.

lemma cprs_flat_sn: ∀I,L,T1,T2. L ⊢ T1 ➡ T2 → ∀V1,V2. L ⊢ V1 ➡* V2 →
                    L ⊢ ⓕ{I} V1. T1 ➡* ⓕ{I} V2. T2.
#I #L #T1 #T2 #HT12 #V1 #V2 #H @(cprs_ind … H) -V2 /3 width=1/
#V #V2 #_ #HV2 #IHV1
@(cprs_strap1 … IHV1) -V1 -T1 /2 width=1/
qed.

lemma cprs_zeta: ∀L,V,T1,T,T2. ⇧[0, 1] T2 ≡ T →
                 L.ⓓV ⊢ T1 ➡* T → L ⊢ +ⓓV.T1 ➡* T2.
#L #V #T1 #T #T2 #HT2 #H @(TC_ind_dx … T1 H) -T1 /3 width=3/
qed.

lemma cprs_tau: ∀L,T1,T2. L ⊢ T1 ➡* T2 → ∀V. L ⊢ ⓝV.T1 ➡* T2.
#L #T1 #T2 #H elim H -T2 /2 width=3/ /3 width=1/
qed.

lemma cprs_beta_dx: ∀a,L,V1,V2,W,T1,T2.
                    L ⊢ V1 ➡ V2 → L.ⓛW ⊢ T1 ➡* T2 →
                    L ⊢ ⓐV1.ⓛ{a}W.T1 ➡* ⓓ{a}V2.T2.
#a #L #V1 #V2 #W #T1 #T2 #HV12 * -T2 /3 width=1/
/4 width=6 by cprs_strap1, cprs_bind_dx, cprs_flat_dx, cpr_beta/ (**) (* auto too slow without trace *)
qed.

lemma cprs_theta_dx: ∀a,L,V1,V,V2,W1,W2,T1,T2.
                     L ⊢ V1 ➡ V → ⇧[0, 1] V ≡ V2 → L.ⓓW1 ⊢ T1 ➡* T2 →
                     L ⊢ W1 ➡ W2 → L ⊢ ⓐV1.ⓓ{a}W1.T1 ➡* ⓓ{a}W2.ⓐV2.T2.
#a #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 * -T2 [ /3 width=3/ ]
/4 width=9 by cprs_strap1, cprs_bind_dx, cprs_flat_dx, cpr_theta/ (**) (* auto too slow without trace *)
qed.

(* Basic inversion lemmas ***************************************************)

(* Basic_1: was: pr3_gen_sort *)
lemma cprs_inv_sort1: ∀L,U2,k. L ⊢ ⋆k ➡* U2 → U2 = ⋆k.
#L #U2 #k #H @(cprs_ind … H) -U2 //
#U2 #U #_ #HU2 #IHU2 destruct
>(cpr_inv_sort1 … HU2) -HU2 //
qed-.

(* Basic_1: was pr3_gen_appl *)
lemma cprs_inv_appl1: ∀L,V1,T1,U2. L ⊢ ⓐV1. T1 ➡* U2 →
                      ∨∨ ∃∃V2,T2.       L ⊢ V1 ➡* V2 & L ⊢ T1 ➡* T2 &
                                        U2 = ⓐV2. T2
                       | ∃∃a,V2,W,T.    L ⊢ V1 ➡* V2 &
                                        L ⊢ T1 ➡* ⓛ{a}W. T & L ⊢ ⓓ{a}V2. T ➡* U2
                       | ∃∃a,V0,V2,V,T. L ⊢ V1 ➡* V0 & ⇧[0,1] V0 ≡ V2 &
                                        L ⊢ T1 ➡* ⓓ{a}V. T & L ⊢ ⓓ{a}V. ⓐV2. T ➡* U2.
#L #V1 #T1 #U2 #H @(cprs_ind … H) -U2 /3 width=5/
#U #U2 #_ #HU2 * *
[ #V0 #T0 #HV10 #HT10 #H destruct
  elim (cpr_inv_appl1 … HU2) -HU2 *
  [ #V2 #T2 #HV02 #HT02 #H destruct /4 width=5/
  | #a #V2 #W2 #T #T2 #HV02 #HT2 #H1 #H2 destruct
    lapply (cprs_strap1 … HV10 … HV02) -V0 /5 width=7/
  | #a #V #V2 #W0 #W2 #T #T2 #HV0 #HV2 #HW02 #HT2 #H1 #H2 destruct
    @or3_intro2 @(ex4_5_intro … HV2 HT10) /2 width=3/ /3 width=1/ (**) (* explicit constructor. /5 width=8/ is too slow because TC_transitive gets in the way *)
  ]
| /4 width=9/
| /4 width=11/
]
qed-.

(* Basic_1: was: pr3_gen_cast *)
lemma cprs_inv_cast1: ∀L,W1,T1,U2. L ⊢ ⓝW1.T1 ➡* U2 → L ⊢ T1 ➡* U2 ∨
                      ∃∃W2,T2. L ⊢ W1 ➡* W2 & L ⊢ T1 ➡* T2 & U2 = ⓝW2.T2.
#L #W1 #T1 #U2 #H @(cprs_ind … H) -U2 /3 width=5/
#U2 #U #_ #HU2 * /3 width=3/ *
#W #T #HW1 #HT1 #H destruct
elim (cpr_inv_cast1 … HU2) -HU2 /3 width=3/ *
#W2 #T2 #HW2 #HT2 #H destruct /4 width=5/
qed-.

(* Basic_1: was: nf2_pr3_unfold *)
lemma cprs_inv_cnf1: ∀L,T,U. L ⊢ T ➡* U → L ⊢ 𝐍⦃T⦄ → T = U.
#L #T #U #H @(cprs_ind_dx … H) -T //
#T0 #T #H1T0 #_ #IHT #H2T0
lapply (H2T0 … H1T0) -H1T0 #H destruct /2 width=1/
qed-.

(* Basic forward lemmas *****************************************************)

(* Basic_1: was: pr3_gen_abst *)
lemma cprs_fwd_abst1: ∀a,L,V1,T1,U2. L ⊢ ⓛ{a}V1. T1 ➡* U2 → ∀I,W.
                      ∃∃V2,T2. L ⊢ V1 ➡* V2 & L. ⓑ{I} W ⊢ T1 ➡* T2 &
                               U2 = ⓛ{a}V2. T2.
#a #L #V1 #T1 #U2 #H @(cprs_ind … H) -U2 /2 width=5/
#U #U2 #_ #HU2 #IHU1 #I #W
elim (IHU1 I W) -IHU1 #V #T #HV1 #HT1 #H destruct
elim (cpr_fwd_abst1 … HU2 I W) -HU2 #V2 #T2 #HV2 #HT2 #H destruct /3 width=5/
qed-.

lemma cprs_fwd_abst: ∀a,L,V1,V2,T1,T2. L ⊢ ⓛ{a}V1. T1 ➡* ⓛ{a}V2. T2 → ∀I,W.
                     L ⊢ V1 ➡* V2 ∧ L. ⓑ{I} W ⊢ T1 ➡* T2.
#a #L #V1 #V2 #T1 #T2 #H #I #W
elim (cprs_fwd_abst1 … H I W) -H #V #T #HV1 #HT1 #H destruct /2 width=1/
qed-.

(* Basic_1: removed theorems 13:
   pr1_head_1 pr1_head_2 pr1_comp
   clear_pr3_trans pr3_cflat pr3_gen_bind
   pr3_head_1 pr3_head_2 pr3_head_21 pr3_head_12
   pr3_iso_appl_bind pr3_iso_appls_appl_bind pr3_iso_appls_bind
*)
