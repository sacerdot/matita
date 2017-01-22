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

notation "hvbox( T1 break ⊢ ▶ * [ term 46 d , break term 46 e ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PSubstStarSn $T1 $d $e $T2 }.

include "basic_2/unfold/tpss.ma".

(* SN PARALLEL UNFOLD ON LOCAL ENVIRONMENTS *********************************)

inductive ltpss_sn: nat → nat → relation lenv ≝
| ltpss_sn_atom : ∀d,e. ltpss_sn d e (⋆) (⋆)
| ltpss_sn_pair : ∀L,I,V. ltpss_sn 0 0 (L. ⓑ{I} V) (L. ⓑ{I} V)
| ltpss_sn_tpss2: ∀L1,L2,I,V1,V2,e.
                  ltpss_sn 0 e L1 L2 → L1 ⊢ V1 ▶* [0, e] V2 →
                  ltpss_sn 0 (e + 1) (L1. ⓑ{I} V1) (L2. ⓑ{I} V2)
| ltpss_sn_tpss1: ∀L1,L2,I,V1,V2,d,e.
                  ltpss_sn d e L1 L2 → L1 ⊢ V1 ▶* [d, e] V2 →
                  ltpss_sn (d + 1) e (L1. ⓑ{I} V1) (L2. ⓑ{I} V2)
.

interpretation "parallel unfold (local environment, sn variant)"
   'PSubstStarSn L1 d e L2 = (ltpss_sn d e L1 L2).

(* Basic inversion lemmas ***************************************************)

fact ltpss_sn_inv_refl_O2_aux: ∀d,e,L1,L2. L1 ⊢ ▶* [d, e] L2 → e = 0 → L1 = L2.
#d #e #L1 #L2 #H elim H -d -e -L1 -L2 //
[ #L1 #L2 #I #V1 #V2 #e #_ #_ #_ >commutative_plus normalize #H destruct
| #L1 #L2 #I #V1 #V2 #d #e #_ #HV12 #IHL12 #He destruct
  >(IHL12 ?) -IHL12 // >(tpss_inv_refl_O2 … HV12) //
]
qed.

lemma ltpss_sn_inv_refl_O2: ∀d,L1,L2. L1 ⊢ ▶* [d, 0] L2 → L1 = L2.
/2 width=4/ qed-.

fact ltpss_sn_inv_atom1_aux: ∀d,e,L1,L2.
                             L1 ⊢ ▶* [d, e] L2 → L1 = ⋆ → L2 = ⋆.
#d #e #L1 #L2 * -d -e -L1 -L2
[ //
| #L #I #V #H destruct
| #L1 #L2 #I #V1 #V2 #e #_ #_ #H destruct
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ #H destruct
]
qed.

lemma ltpss_sn_inv_atom1: ∀d,e,L2. ⋆ ⊢ ▶* [d, e] L2 → L2 = ⋆.
/2 width=5/ qed-.

fact ltpss_sn_inv_tpss21_aux: ∀d,e,L1,L2. L1 ⊢ ▶* [d, e] L2 → d = 0 → 0 < e →
                              ∀K1,I,V1. L1 = K1. ⓑ{I} V1 →
                              ∃∃K2,V2. K1 ⊢ ▶* [0, e - 1] K2 &
                                       K1 ⊢ V1 ▶* [0, e - 1] V2 &
                                       L2 = K2. ⓑ{I} V2.
#d #e #L1 #L2 * -d -e -L1 -L2
[ #d #e #_ #_ #K1 #I #V1 #H destruct
| #L1 #I #V #_ #H elim (lt_refl_false … H)
| #L1 #L2 #I #V1 #V2 #e #HL12 #HV12 #_ #_ #K1 #J #W1 #H destruct /2 width=5/
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ >commutative_plus normalize #H destruct
]
qed.

lemma ltpss_sn_inv_tpss21: ∀e,K1,I,V1,L2. K1. ⓑ{I} V1 ⊢ ▶* [0, e] L2 → 0 < e →
                           ∃∃K2,V2. K1 ⊢ ▶* [0, e - 1] K2 &
                                    K1 ⊢ V1 ▶* [0, e - 1] V2 &
                                    L2 = K2. ⓑ{I} V2.
/2 width=5/ qed-.

fact ltpss_sn_inv_tpss11_aux: ∀d,e,L1,L2. L1 ⊢ ▶* [d, e] L2 → 0 < d →
                              ∀I,K1,V1. L1 = K1. ⓑ{I} V1 →
                              ∃∃K2,V2. K1 ⊢ ▶* [d - 1, e] K2 &
                                       K1 ⊢ V1 ▶* [d - 1, e] V2 &
                                       L2 = K2. ⓑ{I} V2.
#d #e #L1 #L2 * -d -e -L1 -L2
[ #d #e #_ #I #K1 #V1 #H destruct
| #L #I #V #H elim (lt_refl_false … H)
| #L1 #L2 #I #V1 #V2 #e #_ #_ #H elim (lt_refl_false … H)
| #L1 #L2 #I #V1 #V2 #d #e #HL12 #HV12 #_ #J #K1 #W1 #H destruct /2 width=5/
]
qed.

lemma ltpss_sn_inv_tpss11: ∀d,e,I,K1,V1,L2. K1. ⓑ{I} V1 ⊢ ▶* [d, e] L2 → 0 < d →
                           ∃∃K2,V2. K1 ⊢ ▶* [d - 1, e] K2 &
                                    K1 ⊢ V1 ▶* [d - 1, e] V2 &
                                    L2 = K2. ⓑ{I} V2.
/2 width=3/ qed-.

fact ltpss_sn_inv_atom2_aux: ∀d,e,L1,L2.
                             L1 ⊢ ▶* [d, e] L2 → L2 = ⋆ → L1 = ⋆.
#d #e #L1 #L2 * -d -e -L1 -L2
[ //
| #L #I #V #H destruct
| #L1 #L2 #I #V1 #V2 #e #_ #_ #H destruct
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ #H destruct
]
qed.

lemma ltpss_sn_inv_atom2: ∀d,e,L1. L1 ⊢ ▶* [d, e] ⋆ → L1 = ⋆.
/2 width=5/ qed-.

fact ltpss_sn_inv_tpss22_aux: ∀d,e,L1,L2. L1 ⊢ ▶* [d, e] L2 → d = 0 → 0 < e →
                              ∀K2,I,V2. L2 = K2. ⓑ{I} V2 →
                              ∃∃K1,V1. K1 ⊢ ▶* [0, e - 1] K2 &
                                       K1 ⊢ V1 ▶* [0, e - 1] V2 &
                                       L1 = K1. ⓑ{I} V1.
#d #e #L1 #L2 * -d -e -L1 -L2
[ #d #e #_ #_ #K1 #I #V1 #H destruct
| #L1 #I #V #_ #H elim (lt_refl_false … H)
| #L1 #L2 #I #V1 #V2 #e #HL12 #HV12 #_ #_ #K2 #J #W2 #H destruct /2 width=5/
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ >commutative_plus normalize #H destruct
]
qed.

lemma ltpss_sn_inv_tpss22: ∀e,L1,K2,I,V2. L1 ⊢ ▶* [0, e] K2. ⓑ{I} V2 → 0 < e →
                           ∃∃K1,V1. K1 ⊢ ▶* [0, e - 1] K2 &
                                    K1 ⊢ V1 ▶* [0, e - 1] V2 &
                                    L1 = K1. ⓑ{I} V1.
/2 width=5/ qed-.

fact ltpss_sn_inv_tpss12_aux: ∀d,e,L1,L2. L1 ⊢ ▶* [d, e] L2 → 0 < d →
                              ∀I,K2,V2. L2 = K2. ⓑ{I} V2 →
                              ∃∃K1,V1. K1 ⊢ ▶* [d - 1, e] K2 &
                                       K1 ⊢ V1 ▶* [d - 1, e] V2 &
                                       L1 = K1. ⓑ{I} V1.
#d #e #L1 #L2 * -d -e -L1 -L2
[ #d #e #_ #I #K2 #V2 #H destruct
| #L #I #V #H elim (lt_refl_false … H)
| #L1 #L2 #I #V1 #V2 #e #_ #_ #H elim (lt_refl_false … H)
| #L1 #L2 #I #V1 #V2 #d #e #HL12 #HV12 #_ #J #K2 #W2 #H destruct /2 width=5/
]
qed.

lemma ltpss_sn_inv_tpss12: ∀L1,K2,I,V2,d,e. L1 ⊢ ▶* [d, e] K2. ⓑ{I} V2 → 0 < d →
                           ∃∃K1,V1. K1 ⊢ ▶* [d - 1, e] K2 &
                                    K1 ⊢ V1 ▶* [d - 1, e] V2 &
                                    L1 = K1. ⓑ{I} V1.
/2 width=3/ qed-.

(* Basic properties *********************************************************)

lemma ltpss_sn_tps2: ∀L1,L2,I,V1,V2,e.
                     L1 ⊢ ▶* [0, e] L2 → L1 ⊢ V1 ▶ [0, e] V2 →
                     L1. ⓑ{I} V1 ⊢ ▶* [0, e + 1] L2. ⓑ{I} V2.
/3 width=1/ qed.

lemma ltpss_sn_tps1: ∀L1,L2,I,V1,V2,d,e.
                     L1 ⊢ ▶* [d, e] L2 → L1 ⊢ V1 ▶ [d, e] V2 →
                     L1. ⓑ{I} V1 ⊢ ▶* [d + 1, e] L2. ⓑ{I} V2.
/3 width=1/ qed.

lemma ltpss_sn_tpss2_lt: ∀L1,L2,I,V1,V2,e.
                         L1 ⊢ ▶* [0, e - 1] L2 → L1 ⊢ V1 ▶* [0, e - 1] V2 →
                         0 < e → L1. ⓑ{I} V1 ⊢ ▶* [0, e] L2. ⓑ{I} V2.
#L1 #L2 #I #V1 #V2 #e #HL12 #HV12 #He
>(plus_minus_m_m e 1) /2 width=1/
qed.

lemma ltpss_sn_tpss1_lt: ∀L1,L2,I,V1,V2,d,e.
                         L1 ⊢ ▶* [d - 1, e] L2 → L1 ⊢ V1 ▶* [d - 1, e] V2 →
                         0 < d → L1. ⓑ{I} V1 ⊢ ▶* [d, e] L2. ⓑ{I} V2.
#L1 #L2 #I #V1 #V2 #d #e #HL12 #HV12 #Hd
>(plus_minus_m_m d 1) /2 width=1/
qed.

lemma ltpss_sn_tps2_lt: ∀L1,L2,I,V1,V2,e.
                        L1 ⊢ ▶* [0, e - 1] L2 → L1 ⊢ V1 ▶ [0, e - 1] V2 →
                        0 < e → L1. ⓑ{I} V1 ⊢ ▶* [0, e] L2. ⓑ{I} V2.
/3 width=1/ qed.

lemma ltpss_sn_tps1_lt: ∀L1,L2,I,V1,V2,d,e.
                        L1 ⊢ ▶* [d - 1, e] L2 → L1 ⊢ V1 ▶ [d - 1, e] V2 →
                        0 < d → L1. ⓑ{I} V1 ⊢ ▶* [d, e] L2. ⓑ{I} V2.
/3 width=1/ qed.

lemma ltpss_sn_refl: ∀L,d,e. L ⊢ ▶* [d, e] L.
#L elim L -L //
#L #I #V #IHL * /2 width=1/ * /2 width=1/
qed.

lemma ltpss_sn_weak: ∀L1,L2,d1,e1. L1 ⊢ ▶* [d1, e1] L2 →
                     ∀d2,e2. d2 ≤ d1 → d1 + e1 ≤ d2 + e2 → L1 ⊢ ▶* [d2, e2] L2.
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
    /3 width=5 by ltpss_sn_tpss2_lt, tpss_weak/ (**) (* /3 width=5/ used to work *)
  ]
]
qed.

lemma ltpss_sn_weak_full: ∀L1,L2,d,e. L1 ⊢ ▶* [d, e] L2 → L1 ⊢ ▶* [0, |L1|] L2.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e
// /3 width=2/ /3 width=3/
qed.

fact ltpss_sn_append_le_aux: ∀K1,K2,d,x. K1 ⊢ ▶* [d, x] K2 → x = |K1| - d →
                             ∀L1,L2,e. L1 ⊢ ▶* [0, e] L2 → d ≤ |K1| →
                             L1 @@ K1 ⊢ ▶* [d, x + e] L2 @@ K2.
#K1 #K2 #d #x #H elim H -K1 -K2 -d -x
[ #d #x #H1 #L1 #L2 #e #HL12 #H2 destruct
  lapply (le_n_O_to_eq … H2) -H2 #H destruct //
| #K #I #V <minus_n_O normalize <plus_n_Sm #H destruct
| #K1 #K2 #I #V1 #V2 #x #_ #HV12 <minus_n_O #IHK12 <minus_n_O #H #L1 #L2 #e #HL12 #_
  lapply (injective_plus_l … H) -H #H destruct >plus_plus_comm_23
  /4 width=5 by ltpss_sn_tpss2, tpss_append, tpss_weak, monotonic_le_plus_r/ (**) (* too slow without trace *)
| #K1 #K2 #I #V1 #V2 #d #x #_ #HV12 #IHK12 normalize <minus_le_minus_minus_comm // <minus_plus_m_m #H1 #L1 #L2 #e #HL12 #H2 destruct
  lapply (le_plus_to_le_r … H2) -H2 #Hd
  /4 width=5 by ltpss_sn_tpss1, tpss_append, tpss_weak, monotonic_le_plus_r/ (**) (* too slow without trace *)
]
qed-.

lemma ltpss_sn_append_le: ∀K1,K2,d. K1 ⊢ ▶* [d, |K1| - d] K2 →
                          ∀L1,L2,e. L1 ⊢ ▶* [0, e] L2 → d ≤ |K1| →
                          L1 @@ K1 ⊢ ▶* [d, |K1| - d + e] L2 @@ K2.
/2 width=1 by ltpss_sn_append_le_aux/ qed.

lemma ltpss_sn_append_ge: ∀K1,K2,d,e. K1 ⊢ ▶* [d, e] K2 →
                          ∀L1,L2. L1 ⊢ ▶* [d - |K1|, e] L2 → |K1| ≤ d →
                          L1 @@ K1 ⊢ ▶* [d, e] L2 @@ K2.
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

lemma ltpss_sn_fwd_length: ∀L1,L2,d,e. L1 ⊢ ▶* [d, e] L2 → |L1| = |L2|.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e
normalize //
qed-.
