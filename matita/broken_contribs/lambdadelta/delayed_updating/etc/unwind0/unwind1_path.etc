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

include "delayed_updating/substitution/lift_length.ma".
include "delayed_updating/notation/functions/black_downtriangle_1.ma".
include "ground/relocation/tr_uni.ma".

(* BASIC UNWIND FOR PATH ****************************************************)

rec definition unwind1_path_pnat (n) (p) on n ≝
match n with
[ punit   ⇒ p
| psucc m ⇒
  match p with
  [ list_empty     ⇒ 𝐞
  | list_lcons l q ⇒
    match l with
    [ label_d n ⇒
      match q with
      [ list_empty     ⇒ l◗(unwind1_path_pnat m q)
      | list_lcons _ _ ⇒ unwind1_path_pnat m (↑[𝐮❨n❩]q)
      ]
    | label_m   ⇒ unwind1_path_pnat m q
    | label_L   ⇒ 𝗟◗(unwind1_path_pnat m q)
    | label_A   ⇒ 𝗔◗(unwind1_path_pnat m q)
    | label_S   ⇒ 𝗦◗(unwind1_path_pnat m q)
    ]
  ]
].

definition unwind1_path (p) ≝
           unwind1_path_pnat (↑❘p❘) p.

interpretation
  "basic unwind (path)"
  'BlackDownTriangle p = (unwind1_path p).

(* Basic constructions ******************************************************)

lemma unwind1_path_unfold (p):
      unwind1_path_pnat (↑❘p❘) p = ▼p.
// qed-.

lemma unwind1_path_empty:
      (𝐞) = ▼𝐞.
// qed.

lemma unwind1_path_d_empty (n):
      (𝗱n◗𝐞) = ▼(𝗱n◗𝐞).
// qed.

lemma unwind1_path_d_lcons (p) (l) (n:pnat):
      ▼(↑[𝐮❨n❩](l◗p)) = ▼(𝗱n◗l◗p).
#p #l #n
<unwind1_path_unfold <lift_path_length //
qed.

lemma unwind1_path_m_sn (p):
      ▼p = ▼(𝗺◗p).
// qed.

lemma unwind1_path_L_sn (p):
      (𝗟◗▼p) = ▼(𝗟◗p).
// qed.

lemma unwind1_path_A_sn (p):
      (𝗔◗▼p) = ▼(𝗔◗p).
// qed.

lemma unwind1_path_S_sn (p):
      (𝗦◗▼p) = ▼(𝗦◗p).
// qed.

(* Main constructions *******************************************************)

fact unwind1_path_fix_aux (k) (p):
     k = ❘p❘ → ▼p = ▼▼p.
#k @(nat_ind_succ … k) -k
[ #p #H0 >(list_length_inv_zero_sn … H0) -p //
| #k #IH *
  [ #H0 elim (eq_inv_nsucc_zero … H0)
  | * [ #n ] #p #H0
    lapply (eq_inv_nsucc_bi … H0) -H0
    [ cases p -p [ -IH | #l #p ] #H0 destruct //
      <unwind1_path_d_lcons <IH -IH //
    | #H0 destruct <unwind1_path_m_sn <IH -IH //
    | #H0 destruct <unwind1_path_L_sn <unwind1_path_L_sn <IH -IH //
    | #H0 destruct <unwind1_path_A_sn <unwind1_path_A_sn <IH -IH //
    | #H0 destruct <unwind1_path_S_sn <unwind1_path_S_sn <IH -IH //
    ]
  ]
]
qed-.

theorem unwind1_path_fix (p):
        ▼p = ▼▼p.
/2 width=2 by unwind1_path_fix_aux/ qed.
