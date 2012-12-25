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

include "basic_2/reducibility/cpr.ma".

(* CONTEXT-SENSITIVE NORMAL TERMS *******************************************)

definition cnf: lenv → predicate term ≝ λL. NF … (cpr L) (eq …).

interpretation
   "context-sensitive normality (term)"
   'Normal L T = (cnf L T).

(* Basic inversion lemmas ***************************************************)

lemma cnf_inv_appl: ∀L,V,T. L ⊢ 𝐍⦃ⓐV.T⦄ → ∧∧ L ⊢ 𝐍⦃V⦄ & L ⊢ 𝐍⦃T⦄ & 𝐒⦃T⦄.
#L #V1 #T1 #HVT1 @and3_intro
[ #V2 #HV2 lapply (HVT1 (ⓐV2.T1) ?) -HVT1 /2 width=1/ -HV2 #H destruct //
| #T2 #HT2 lapply (HVT1 (ⓐV1.T2) ?) -HVT1 /2 width=1/ -HT2 #H destruct //
| generalize in match HVT1; -HVT1 elim T1 -T1 * // #a * #W1 #U1 #_ #_ #H
  [ elim (lift_total V1 0 1) #V2 #HV12
    lapply (H (ⓓ{a}W1.ⓐV2.U1) ?) -H /3 width=3/ -HV12 #H destruct
  | lapply (H (ⓓ{a}V1.U1) ?) -H /3 width=1/ #H destruct
]
qed-.

lemma cnf_inv_zeta: ∀L,V,T. L ⊢ 𝐍⦃+ⓓV.T⦄ → ⊥.
#L #V #T #H elim (is_lift_dec T 0 1)
[ * #U #HTU
  lapply (H U ?) -H /3 width=3 by cpr_tpr, tpr_zeta/ #H destruct (**) (* auto too slow without trace *)
  elim (lift_inv_pair_xy_y … HTU)
| #HT
  elim (tps_full (⋆) V T (⋆. ⓓV) 0 ?) // #T2 #T1 #HT2 #HT12
  lapply (H (+ⓓV.T2) ?) -H /3 width=3 by cpr_tpr, tpr_delta/ -HT2 #H destruct /3 width=2/ (**) (* auto too slow without trace *)
]
qed.

lemma cnf_inv_tau: ∀L,V,T. L ⊢ 𝐍⦃ⓝV.T⦄ → ⊥.
#L #V #T #H lapply (H T ?) -H /2 width=1/ #H
@discr_tpair_xy_y //
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: nf2_sort *)
lemma cnf_sort: ∀L,k. L ⊢ 𝐍⦃⋆k⦄.
#L #k #X #H
>(cpr_inv_sort1 … H) //
qed.

(* Basic_1: was: nf2_dec *)
axiom cnf_dec: ∀L,T1. L ⊢ 𝐍⦃T1⦄ ∨
               ∃∃T2. L ⊢ T1 ➡ T2 & (T1 = T2 → ⊥).

(* Basic_1: removed theorems 1: nf2_abst_shift *)
