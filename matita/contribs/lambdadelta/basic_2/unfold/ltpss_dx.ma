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

notation "hvbox( T1 break ▶ * [ term 46 d , break term 46 e ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PSubstStar $T1 $d $e $T2 }.

include "basic_2/unfold/tpss.ma".

(* DX PARALLEL UNFOLD ON LOCAL ENVIRONMENTS *********************************)

(* Basic_1: includes: csubst1_bind *)
inductive ltpss_dx: nat → nat → relation lenv ≝
| ltpss_dx_atom : ∀d,e. ltpss_dx d e (⋆) (⋆)
| ltpss_dx_pair : ∀L,I,V. ltpss_dx 0 0 (L. ⓑ{I} V) (L. ⓑ{I} V)
| ltpss_dx_tpss2: ∀L1,L2,I,V1,V2,e.
                  ltpss_dx 0 e L1 L2 → L2 ⊢ V1 ▶* [0, e] V2 →
                  ltpss_dx 0 (e + 1) (L1. ⓑ{I} V1) (L2. ⓑ{I} V2)
| ltpss_dx_tpss1: ∀L1,L2,I,V1,V2,d,e.
                  ltpss_dx d e L1 L2 → L2 ⊢ V1 ▶* [d, e] V2 →
                  ltpss_dx (d + 1) e (L1. ⓑ{I} V1) (L2. ⓑ{I} V2)
.

interpretation "parallel unfold (local environment, dx variant)"
   'PSubstStar L1 d e L2 = (ltpss_dx d e L1 L2).

(* Basic inversion lemmas ***************************************************)

fact ltpss_dx_inv_refl_O2_aux: ∀d,e,L1,L2. L1 ▶* [d, e] L2 → e = 0 → L1 = L2.
#d #e #L1 #L2 #H elim H -d -e -L1 -L2 //
[ #L1 #L2 #I #V1 #V2 #e #_ #_ #_ >commutative_plus normalize #H destruct
| #L1 #L2 #I #V1 #V2 #d #e #_ #HV12 #IHL12 #He destruct
  >(IHL12 ?) -IHL12 // >(tpss_inv_refl_O2 … HV12) //
]
qed.

lemma ltpss_dx_inv_refl_O2: ∀d,L1,L2. L1 ▶* [d, 0] L2 → L1 = L2.
/2 width=4/ qed-.

fact ltpss_dx_inv_atom1_aux: ∀d,e,L1,L2.
                             L1 ▶* [d, e] L2 → L1 = ⋆ → L2 = ⋆.
#d #e #L1 #L2 * -d -e -L1 -L2
[ //
| #L #I #V #H destruct
| #L1 #L2 #I #V1 #V2 #e #_ #_ #H destruct
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ #H destruct
]
qed.

lemma ltpss_dx_inv_atom1: ∀d,e,L2. ⋆ ▶* [d, e] L2 → L2 = ⋆.
/2 width=5/ qed-.

fact ltpss_dx_inv_tpss21_aux: ∀d,e,L1,L2. L1 ▶* [d, e] L2 → d = 0 → 0 < e →
                              ∀K1,I,V1. L1 = K1. ⓑ{I} V1 →
                              ∃∃K2,V2. K1 ▶* [0, e - 1] K2 &
                                       K2 ⊢ V1 ▶* [0, e - 1] V2 &
                                       L2 = K2. ⓑ{I} V2.
#d #e #L1 #L2 * -d -e -L1 -L2
[ #d #e #_ #_ #K1 #I #V1 #H destruct
| #L1 #I #V #_ #H elim (lt_refl_false … H)
| #L1 #L2 #I #V1 #V2 #e #HL12 #HV12 #_ #_ #K1 #J #W1 #H destruct /2 width=5/
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ >commutative_plus normalize #H destruct
]
qed.

lemma ltpss_dx_inv_tpss21: ∀e,K1,I,V1,L2. K1. ⓑ{I} V1 ▶* [0, e] L2 → 0 < e →
                           ∃∃K2,V2. K1 ▶* [0, e - 1] K2 &
                                    K2 ⊢ V1 ▶* [0, e - 1] V2 &
                                    L2 = K2. ⓑ{I} V2.
/2 width=5/ qed-.

fact ltpss_dx_inv_tpss11_aux: ∀d,e,L1,L2. L1 ▶* [d, e] L2 → 0 < d →
                              ∀I,K1,V1. L1 = K1. ⓑ{I} V1 →
                              ∃∃K2,V2. K1 ▶* [d - 1, e] K2 &
                                       K2 ⊢ V1 ▶* [d - 1, e] V2 &
                                       L2 = K2. ⓑ{I} V2.
#d #e #L1 #L2 * -d -e -L1 -L2
[ #d #e #_ #I #K1 #V1 #H destruct
| #L #I #V #H elim (lt_refl_false … H)
| #L1 #L2 #I #V1 #V2 #e #_ #_ #H elim (lt_refl_false … H)
| #L1 #L2 #I #V1 #V2 #d #e #HL12 #HV12 #_ #J #K1 #W1 #H destruct /2 width=5/
]
qed.

lemma ltpss_dx_inv_tpss11: ∀d,e,I,K1,V1,L2. K1. ⓑ{I} V1 ▶* [d, e] L2 → 0 < d →
                           ∃∃K2,V2. K1 ▶* [d - 1, e] K2 &
                                    K2 ⊢ V1 ▶* [d - 1, e] V2 &
                                    L2 = K2. ⓑ{I} V2.
/2 width=3/ qed-.

fact ltpss_dx_inv_atom2_aux: ∀d,e,L1,L2.
                             L1 ▶* [d, e] L2 → L2 = ⋆ → L1 = ⋆.
#d #e #L1 #L2 * -d -e -L1 -L2
[ //
| #L #I #V #H destruct
| #L1 #L2 #I #V1 #V2 #e #_ #_ #H destruct
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ #H destruct
]
qed.

lemma ltpss_dx_inv_atom2: ∀d,e,L1. L1 ▶* [d, e] ⋆ → L1 = ⋆.
/2 width=5/ qed-.

fact ltpss_dx_inv_tpss22_aux: ∀d,e,L1,L2. L1 ▶* [d, e] L2 → d = 0 → 0 < e →
                              ∀K2,I,V2. L2 = K2. ⓑ{I} V2 →
                              ∃∃K1,V1. K1 ▶* [0, e - 1] K2 &
                                       K2 ⊢ V1 ▶* [0, e - 1] V2 &
                                       L1 = K1. ⓑ{I} V1.
#d #e #L1 #L2 * -d -e -L1 -L2
[ #d #e #_ #_ #K1 #I #V1 #H destruct
| #L1 #I #V #_ #H elim (lt_refl_false … H)
| #L1 #L2 #I #V1 #V2 #e #HL12 #HV12 #_ #_ #K2 #J #W2 #H destruct /2 width=5/
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ >commutative_plus normalize #H destruct
]
qed.

lemma ltpss_dx_inv_tpss22: ∀e,L1,K2,I,V2. L1 ▶* [0, e] K2. ⓑ{I} V2 → 0 < e →
                           ∃∃K1,V1. K1 ▶* [0, e - 1] K2 &
                                    K2 ⊢ V1 ▶* [0, e - 1] V2 &
                                    L1 = K1. ⓑ{I} V1.
/2 width=5/ qed-.

fact ltpss_dx_inv_tpss12_aux: ∀d,e,L1,L2. L1 ▶* [d, e] L2 → 0 < d →
                              ∀I,K2,V2. L2 = K2. ⓑ{I} V2 →
                              ∃∃K1,V1. K1 ▶* [d - 1, e] K2 &
                                       K2 ⊢ V1 ▶* [d - 1, e] V2 &
                                       L1 = K1. ⓑ{I} V1.
#d #e #L1 #L2 * -d -e -L1 -L2
[ #d #e #_ #I #K2 #V2 #H destruct
| #L #I #V #H elim (lt_refl_false … H)
| #L1 #L2 #I #V1 #V2 #e #_ #_ #H elim (lt_refl_false … H)
| #L1 #L2 #I #V1 #V2 #d #e #HL12 #HV12 #_ #J #K2 #W2 #H destruct /2 width=5/
]
qed.

lemma ltpss_dx_inv_tpss12: ∀L1,K2,I,V2,d,e. L1 ▶* [d, e] K2. ⓑ{I} V2 → 0 < d →
                           ∃∃K1,V1. K1 ▶* [d - 1, e] K2 &
                                    K2 ⊢ V1 ▶* [d - 1, e] V2 &
                                    L1 = K1. ⓑ{I} V1.
/2 width=3/ qed-.

(* Basic properties *********************************************************)

lemma ltpss_dx_tps2: ∀L1,L2,I,V1,V2,e.
                     L1 ▶* [0, e] L2 → L2 ⊢ V1 ▶ [0, e] V2 →
                     L1. ⓑ{I} V1 ▶* [0, e + 1] L2. ⓑ{I} V2.
/3 width=1/ qed.

lemma ltpss_dx_tps1: ∀L1,L2,I,V1,V2,d,e.
                     L1 ▶* [d, e] L2 → L2 ⊢ V1 ▶ [d, e] V2 →
                     L1. ⓑ{I} V1 ▶* [d + 1, e] L2. ⓑ{I} V2.
/3 width=1/ qed.

lemma ltpss_dx_tpss2_lt: ∀L1,L2,I,V1,V2,e.
                         L1 ▶* [0, e - 1] L2 → L2 ⊢ V1 ▶* [0, e - 1] V2 →
                         0 < e → L1. ⓑ{I} V1 ▶* [0, e] L2. ⓑ{I} V2.
#L1 #L2 #I #V1 #V2 #e #HL12 #HV12 #He
>(plus_minus_m_m e 1) /2 width=1/
qed.

lemma ltpss_dx_tpss1_lt: ∀L1,L2,I,V1,V2,d,e.
                         L1 ▶* [d - 1, e] L2 → L2 ⊢ V1 ▶* [d - 1, e] V2 →
                         0 < d → L1. ⓑ{I} V1 ▶* [d, e] L2. ⓑ{I} V2.
#L1 #L2 #I #V1 #V2 #d #e #HL12 #HV12 #Hd
>(plus_minus_m_m d 1) /2 width=1/
qed.

lemma ltpss_dx_tps2_lt: ∀L1,L2,I,V1,V2,e.
                        L1 ▶* [0, e - 1] L2 → L2 ⊢ V1 ▶ [0, e - 1] V2 →
                        0 < e → L1. ⓑ{I} V1 ▶* [0, e] L2. ⓑ{I} V2.
/3 width=1/ qed.

lemma ltpss_dx_tps1_lt: ∀L1,L2,I,V1,V2,d,e.
                        L1 ▶* [d - 1, e] L2 → L2 ⊢ V1 ▶ [d - 1, e] V2 →
                        0 < d → L1. ⓑ{I} V1 ▶* [d, e] L2. ⓑ{I} V2.
/3 width=1/ qed.

(* Basic_1: was by definition: csubst1_refl *)
lemma ltpss_dx_refl: ∀L,d,e. L ▶* [d, e] L.
#L elim L -L //
#L #I #V #IHL * /2 width=1/ * /2 width=1/
qed.

lemma ltpss_dx_weak: ∀L1,L2,d1,e1. L1 ▶* [d1, e1] L2 →
                     ∀d2,e2. d2 ≤ d1 → d1 + e1 ≤ d2 + e2 → L1 ▶* [d2, e2] L2.
#L1 #L2 #d1 #e1 #H elim H -L1 -L2 -d1 -e1 //
[ #L1 #L2 #I #V1 #V2 #e1 #_ #HV12 #IHL12 #d2 #e2 #Hd2 #Hde2
  lapply (le_n_O_to_eq … Hd2) #H destruct normalize in Hde2;
  lapply (lt_to_le_to_lt 0 … Hde2) // #He2
  lapply (le_plus_to_minus_r … Hde2) -Hde2 /3 width=5/
| #L1 #L2 #I #V1 #V2 #d1 #e1 #_ #HV12 #IHL12 #d2 #e2 #Hd21 #Hde12
  >plus_plus_comm_23 in Hde12; #Hde12
  elim (le_to_or_lt_eq 0 d2 ?) // #H destruct
  [ lapply (le_plus_to_minus_r … Hde12) -Hde12 <plus_minus // #Hde12
    lapply (le_plus_to_minus … Hd21) -Hd21 #Hd21 /3 width=5/
  | -Hd21 normalize in Hde12;
    lapply (lt_to_le_to_lt 0 … Hde12) // #He2
    lapply (le_plus_to_minus_r … Hde12) -Hde12
    /3 width=5 by ltpss_dx_tpss2_lt, tpss_weak/ (**) (* /3 width=5/ used to work *)
  ]
]
qed.

lemma ltpss_dx_weak_full: ∀L1,L2,d,e. L1 ▶* [d, e] L2 → L1 ▶* [0, |L2|] L2.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e
// /3 width=2/ /3 width=3/
qed.

fact ltpss_dx_append_le_aux: ∀K1,K2,d,x. K1 ▶* [d, x] K2 → x = |K1| - d →
                             ∀L1,L2,e. L1 ▶* [0, e] L2 → d ≤ |K1| →
                             L1 @@ K1 ▶* [d, x + e] L2 @@ K2.
#K1 #K2 #d #x #H elim H -K1 -K2 -d -x
[ #d #x #H1 #L1 #L2 #e #HL12 #H2 destruct
  lapply (le_n_O_to_eq … H2) -H2 #H destruct //
| #K #I #V <minus_n_O normalize <plus_n_Sm #H destruct
| #K1 #K2 #I #V1 #V2 #x #_ #HV12 <minus_n_O #IHK12 <minus_n_O #H #L1 #L2 #e #HL12 #_
  lapply (injective_plus_l … H) -H #H destruct >plus_plus_comm_23
  /4 width=5 by ltpss_dx_tpss2, tpss_append, tpss_weak, monotonic_le_plus_r/ (**) (* too slow without trace *)
| #K1 #K2 #I #V1 #V2 #d #x #_ #HV12 #IHK12 normalize <minus_le_minus_minus_comm // <minus_plus_m_m #H1 #L1 #L2 #e #HL12 #H2 destruct
  lapply (le_plus_to_le_r … H2) -H2 #Hd
  /4 width=5 by ltpss_dx_tpss1, tpss_append, tpss_weak, monotonic_le_plus_r/ (**) (* too slow without trace *)
]
qed-.

lemma ltpss_dx_append_le: ∀K1,K2,d. K1 ▶* [d, |K1| - d] K2 →
                          ∀L1,L2,e. L1 ▶* [0, e] L2 → d ≤ |K1| →
                          L1 @@ K1 ▶* [d, |K1| - d + e] L2 @@ K2.
/2 width=1 by ltpss_dx_append_le_aux/ qed.

lemma ltpss_dx_append_zero: ∀K1,K2. K1 ▶* [0, |K1|] K2 →
                            ∀L1,L2,e. L1 ▶* [0, e] L2 →
                            L1 @@ K1 ▶* [0, |K1| + e] L2 @@ K2.
/2 width=1/ qed.

lemma ltpss_dx_append_ge: ∀K1,K2,d,e. K1 ▶* [d, e] K2 →
                          ∀L1,L2. L1 ▶* [d - |K1|, e] L2 → |K1| ≤ d →
                          L1 @@ K1 ▶* [d, e] L2 @@ K2.
#K1 #K2 #d #e #H elim H -K1 -K2 -d -e
[ #d #e #L1 #L2 <minus_n_O //
| #K #I #V #L1 #L2 #_ #H
  lapply (le_n_O_to_eq … H) -H normalize <plus_n_Sm #H destruct
| #K1 #K2 #I #V1 #V2 #e #_ #_ #_ #L1 #L2 #_ #H
  lapply (le_n_O_to_eq … H) -H normalize <plus_n_Sm #H destruct
| #K1 #K2 #I #V1 #V2 #d #e #_ #HV12 #IHK12 #L1 #L2
  normalize <minus_le_minus_minus_comm // <minus_plus_m_m #HL12 #H
  lapply (le_plus_to_le_r … H) -H /3 width=1/
]
qed.

(* Basic forward lemmas *****************************************************)

lemma ltpss_dx_fwd_length: ∀L1,L2,d,e. L1 ▶* [d, e] L2 → |L1| = |L2|.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e
normalize //
qed-.

(* Basic_1: removed theorems 28:
            csubst0_clear_O csubst0_drop_lt csubst0_drop_gt csubst0_drop_eq
            csubst0_clear_O_back csubst0_clear_S csubst0_clear_trans
            csubst0_drop_gt_back csubst0_drop_eq_back csubst0_drop_lt_back
            csubst0_gen_sort csubst0_gen_head csubst0_getl_ge csubst0_getl_lt
            csubst0_gen_S_bind_2 csubst0_getl_ge_back csubst0_getl_lt_back
            csubst0_snd_bind csubst0_fst_bind csubst0_both_bind
            csubst1_head csubst1_flat csubst1_gen_head
            csubst1_getl_ge csubst1_getl_lt csubst1_getl_ge_back getl_csubst1
            fsubst0_gen_base
*)
