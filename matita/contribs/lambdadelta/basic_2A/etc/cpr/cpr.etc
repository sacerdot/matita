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

include "basic_2/unfold/tpss.ma".
include "basic_2/reducibility/tpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS ****************************)

(* Basic_1: includes: pr2_delta1 *)
definition cpr: lenv → relation term ≝
   λL,T1,T2. ∃∃T. T1 ➡ T & L ⊢ T ▶* [0, |L|] T2.

interpretation
   "context-sensitive parallel reduction (term)"
   'PRed L T1 T2 = (cpr L T1 T2).

(* Basic properties *********************************************************)

lemma cpr_intro: ∀L,T1,T,T2,d,e. T1 ➡ T → L ⊢ T ▶* [d, e] T2 → L ⊢ T1 ➡ T2.
/3 width=5/ qed-.

(* Basic_1: was by definition: pr2_free *)
lemma cpr_tpr: ∀T1,T2. T1 ➡ T2 → ∀L. L ⊢ T1 ➡ T2.
/2 width=3/ qed.

lemma cpr_tpss: ∀L,T1,T2,d,e. L ⊢ T1 ▶* [d, e] T2 → L ⊢ T1 ➡ T2.
/3 width=5/ qed.

lemma cpr_refl: ∀L,T. L ⊢ T ➡ T.
/2 width=1/ qed.

(* Note: new property *)
(* Basic_1: was only: pr2_thin_dx *)
lemma cpr_flat: ∀I,L,V1,V2,T1,T2.
                L ⊢ V1 ➡ V2 → L ⊢ T1 ➡ T2 → L ⊢ ⓕ{I} V1. T1 ➡ ⓕ{I} V2. T2.
#I #L #V1 #V2 #T1 #T2 * #V #HV1 #HV2 * /3 width=5/
qed.

lemma cpr_cast: ∀L,V,T1,T2.
                L ⊢ T1 ➡ T2 → L ⊢ ⓝV. T1 ➡ T2.
#L #V #T1 #T2 * /3 width=3/
qed.

(* Note: it does not hold replacing |L1| with |L2| *)
(* Basic_1: was only: pr2_change *)
lemma cpr_lsubr_trans: ∀L1,T1,T2. L1 ⊢ T1 ➡ T2 →
                       ∀L2. L2 ⊑ [0, |L1|] L1 → L2 ⊢ T1 ➡ T2.
#L1 #T1 #T2 * #T #HT1 #HT2 #L2 #HL12
lapply (tpss_lsubr_trans … HT2 … HL12) -HT2 -HL12 /3 width=4/
qed.

(* Basic inversion lemmas ***************************************************)

(* Basic_1: was: pr2_gen_csort *)
lemma cpr_inv_atom: ∀T1,T2. ⋆ ⊢ T1 ➡ T2 → T1 ➡ T2.
#T1 #T2 * #T #HT normalize #HT2
<(tpss_inv_refl_O2 … HT2) -HT2 //
qed-.

(* Basic_1: was: pr2_gen_sort *)
lemma cpr_inv_sort1: ∀L,T2,k. L ⊢ ⋆k ➡ T2 → T2 = ⋆k.
#L #T2 #k * #X #H
>(tpr_inv_atom1 … H) -H #H
>(tpss_inv_sort1 … H) -H //
qed-.

(* Basic_1: was: pr2_gen_cast *)
lemma cpr_inv_cast1: ∀L,V1,T1,U2. L ⊢ ⓝV1. T1 ➡ U2 → (
                        ∃∃V2,T2. L ⊢ V1 ➡ V2 & L ⊢ T1 ➡ T2 &
                                 U2 = ⓝV2. T2
                     ) ∨ L ⊢ T1 ➡ U2.
#L #V1 #T1 #U2 * #X #H #HU2
elim (tpr_inv_cast1 … H) -H /3 width=3/
* #V #T #HV1 #HT1 #H destruct
elim (tpss_inv_flat1 … HU2) -HU2 #V2 #T2 #HV2 #HT2 #H destruct /4 width=5/
qed-.

(* Basic forward lemmas *****************************************************)

lemma cpr_fwd_bind1_minus: ∀I,L,V1,T1,T. L ⊢ -ⓑ{I}V1.T1 ➡ T → ∀b.
                           ∃∃V2,T2. L ⊢ ⓑ{b,I}V1.T1 ➡ ⓑ{b,I}V2.T2 &
                                    T = -ⓑ{I}V2.T2.
#I #L #V1 #T1 #T * #X #H1 #H2 #b
elim (tpr_fwd_bind1_minus … H1 b) -H1 #V0 #T0 #HT10 #H destruct
elim (tpss_inv_bind1 … H2) -H2 #V2 #T2 #HV02 #HT02 #H destruct /4 width=5/
qed-.

lemma cpr_fwd_shift1: ∀L,L1,T1,T. L ⊢ L1 @@ T1 ➡ T →
                      ∃∃L2,T2. |L1| = |L2| & T = L2 @@ T2.
#L #L1 #T1 #T * #X #H1 #H2
elim (tpr_fwd_shift1 … H1) -H1 #L0 #T0 #HL10 #H destruct
elim (tpss_fwd_shift1 … H2) -H2 #L2 #T2 #HL02 #H destruct /2 width=4/
qed-.

(* Basic_1: removed theorems 6:
            pr2_head_2 pr2_cflat pr2_gen_cflat clear_pr2_trans
            pr2_gen_ctail pr2_ctail
   Basic_1: removed local theorems 3:
            pr2_free_free pr2_free_delta pr2_delta_delta
*)
