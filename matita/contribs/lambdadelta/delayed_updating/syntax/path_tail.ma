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

(* TAIL FOR PATH ************************************************************)

rec definition tail (m) (p) on p: path ≝
match m with
[ nzero  ⇒ 𝐞
| ninj o ⇒ 
  match p with
  [ list_empty     ⇒ 𝗟∗∗m
  | list_lcons l q ⇒
    match l with
    [ label_d n ⇒ l◗(tail (m+n) q)
    | label_m   ⇒ l◗(tail m q)
    | label_L   ⇒ l◗(tail (↓o) q)
    | label_A   ⇒ l◗(tail m q)
    | label_S   ⇒ l◗(tail m q)
    ]
  ]
].

interpretation
  "tail (reversed path)"
  'DownArrowRight n p = (tail n p).

(* basic constructions ****************************************************)

lemma tail_zero (p):
      (𝐞) = ↳[𝟎]p.
* // qed.

lemma tail_empty (n):
      (𝗟∗∗n) = ↳[n]𝐞.
* // qed.

lemma tail_d_sn (p) (n) (m:pnat):
      (𝗱m◗↳[↑n+m]p) = ↳[↑n](𝗱m◗p).
// qed.

lemma tail_m_sn (p) (n):
      (𝗺◗↳[↑n]p) = ↳[↑n](𝗺◗p).
// qed.

lemma tail_L_sn (p) (n):
      (𝗟◗↳[n]p) = ↳[↑n](𝗟◗p).
#p #n
whd in ⊢ (???%); //
qed.

lemma tail_A_sn (p) (n):
      (𝗔◗↳[↑n]p) = ↳[↑n](𝗔◗p).
// qed.

lemma tail_S_sn (p) (n):
      (𝗦◗↳[↑n]p) = ↳[↑n](𝗦◗p).
// qed.
