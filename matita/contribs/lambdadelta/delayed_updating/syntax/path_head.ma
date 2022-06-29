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

include "delayed_updating/syntax/path_labels.ma".
include "delayed_updating/notation/functions/downarrowright_2.ma".
include "ground/arith/nat_plus.ma".
include "ground/arith/nat_pred_succ.ma".

(* HEAD FOR PATH ************************************************************)

rec definition path_head (m) (p) on p: path ≝
match m with
[ nzero  ⇒ 𝐞
| ninj o ⇒ 
  match p with
  [ list_empty     ⇒ 𝗟∗∗m
  | list_lcons l q ⇒
    match l with
    [ label_d n ⇒ l◗(path_head (m+n) q)
    | label_m   ⇒ l◗(path_head m q)
    | label_L   ⇒ l◗(path_head (↓o) q)
    | label_A   ⇒ l◗(path_head m q)
    | label_S   ⇒ l◗(path_head m q)
    ]
  ]
].

interpretation
  "head (reversed path)"
  'DownArrowRight n p = (path_head n p).

(* basic constructions ****************************************************)

lemma path_head_zero (p):
      (𝐞) = ↳[𝟎]p.
* // qed.

lemma path_head_empty (n):
      (𝗟∗∗n) = ↳[n]𝐞.
* // qed.

lemma path_head_d_sn (p) (n) (m:pnat):
      (𝗱m◗↳[↑n+m]p) = ↳[↑n](𝗱m◗p).
// qed.

lemma path_head_m_sn (p) (n):
      (𝗺◗↳[↑n]p) = ↳[↑n](𝗺◗p).
// qed.

lemma path_head_L_sn (p) (n):
      (𝗟◗↳[n]p) = ↳[↑n](𝗟◗p).
#p #n
whd in ⊢ (???%); //
qed.

lemma path_head_A_sn (p) (n):
      (𝗔◗↳[↑n]p) = ↳[↑n](𝗔◗p).
// qed.

lemma path_head_S_sn (p) (n):
      (𝗦◗↳[↑n]p) = ↳[↑n](𝗦◗p).
// qed.

(* Basic inversions *********************************************************)

lemma eq_inv_path_head_zero_dx (q) (p):
      q = ↳[𝟎]p → 𝐞 = q.
#q * //
qed-.

lemma eq_inv_path_empty_head (p) (n):
      (𝐞) = ↳[n]p → 𝟎 = n.
*
[ #m <path_head_empty #H0
  <(eq_inv_empty_labels … H0) -m //
| * [ #n ] #p #n @(nat_ind_succ … n) -n // #m #_
  [ <path_head_d_sn
  | <path_head_m_sn
  | <path_head_L_sn
  | <path_head_A_sn
  | <path_head_S_sn
  ] #H0 destruct
]
qed-.

(* Constructions with list_append *******************************************)

lemma path_head_refl_append (p) (q) (n):
      q = ↳[n]q → q = ↳[n](q●p).
#p #q elim q -q
[ #n #Hn <(eq_inv_path_empty_head … Hn) -Hn //
| #l #q #IH #n @(nat_ind_succ … n) -n
  [ #Hq | #n #_ cases l [ #m ] ]
  [ lapply (eq_inv_path_head_zero_dx … Hq) -Hq #Hq destruct
  | <path_head_d_sn <path_head_d_sn
  | <path_head_m_sn <path_head_m_sn
  | <path_head_L_sn <path_head_L_sn
  | <path_head_A_sn <path_head_A_sn
  | <path_head_S_sn <path_head_S_sn
  ] #Hq
  elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
  /3 width=1 by eq_f/
]
qed-.

(* Inversions with list_append **********************************************)

lemma eq_inv_path_head_refl_append (p) (q) (n):
      q = ↳[n](q●p) → q = ↳[n]q.
#p #q elim q -q
[ #n #Hn <(eq_inv_path_empty_head … Hn) -p //
| #l #q #IH #n @(nat_ind_succ … n) -n //
  #n #_ cases l [ #m ]
  [ <path_head_d_sn <path_head_d_sn
  | <path_head_m_sn <path_head_m_sn
  | <path_head_L_sn <path_head_L_sn
  | <path_head_A_sn <path_head_A_sn
  | <path_head_S_sn <path_head_S_sn
  ] #Hq
  elim (eq_inv_list_lcons_bi ????? Hq) -Hq #_ #Hq
  /3 width=1 by eq_f/
]
qed-.
