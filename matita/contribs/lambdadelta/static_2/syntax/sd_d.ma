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

include "ground/generated/pull_2.ma".
include "ground/arith/pnat_pred.ma".
include "static_2/syntax/sh_props.ma".
include "static_2/syntax/sd.ma".

(* SORT DEGREE **************************************************************)

(* Basic_2A1: includes: deg_SO_pos *)
inductive deg_SO (h) (s) (s0): predicate nat ≝
| deg_SO_succ : ∀n. ⇡*[h,n]s0 = s → deg_SO h s s0 (↑n)
| deg_SO_zero: (∀n. ⇡*[h,n]s0 = s → ⊥) → deg_SO h s s0 𝟎
.

fact deg_SO_inv_succ_aux (h) (s) (s0):
     ∀n0. deg_SO h s s0 n0 → ∀n. n0 = ↑n → ⇡*[h,n]s0 = s.
#h #s #s0 #n0 * -n0
[ #n #Hn #x #H destruct //
| #_ #x #H elim (eq_inv_zero_nsucc … H)
]
qed-.

(* Basic_2A1: was: deg_SO_inv_pos *)
lemma deg_SO_inv_succ (h) (s) (s0):
      ∀n. deg_SO h s s0 (↑n) → ⇡*[h,n]s0 = s.
/2 width=3 by deg_SO_inv_succ_aux/ qed-.

lemma deg_SO_refl (h) (s):
      deg_SO h s s 𝟏.
#h #s @(deg_SO_succ … 𝟎 ?) //
qed.

definition sd_SO (h) (s):
           sd ≝ mk_sd (deg_SO h s).

lemma sd_SO_props (h) (s):
      sh_decidable h → sh_acyclic h →
      sd_props h (sd_SO h s).
#h #s #Hhd #Hha
@mk_sd_props
[ #s0
  elim (sh_nexts_dec … Hhd s0 s) -Hhd
  [ * /3 width=2 by deg_SO_succ, ex_intro/
  | /5 width=2 by deg_SO_zero, ex_intro/
  ]
| #s0 #d1 #d2 * [ #n1 ] #H1 * [1,3: #n2 ] #H2
  [ < H2 in H1; -H2 #H
    lapply (sh_nexts_inj … Hha … H) -H #H destruct //
  | elim H1 /2 width=2 by ex_intro/
  | elim H2 /2 width=2 by ex_intro/
  | //
  ]
| #s0 #d *
  [ #n #H destruct
    <npred_succ @(nat_ind_succ … n) -n
    [ @deg_SO_zero #n >sh_nexts_succ_next #H
      lapply (sh_nexts_inj … Hha … H) -H #H
      elim (eq_inv_nsucc_zero … H)
    | #n #_ /2 width=1 by deg_SO_succ/
    ]
  | #H0 @deg_SO_zero #n >sh_nexts_succ_next #H destruct
    /2 width=2 by/
  ]
]
qed.

rec definition sd_d_pnat (h) (s) (d) on d: sd ≝
match d with
[ punit   ⇒ sd_SO h s
| psucc d ⇒ sd_d_pnat h (⇡[h]s) d
].

definition sd_d (h) (s) (d): sd ≝
match d with
[ nzero  ⇒ sd_O
| ninj d ⇒ sd_d_pnat h s d
].

lemma sd_d_props (h) (s) (d):
      sh_decidable h → sh_acyclic h →
      sd_props h (sd_d h s d).
#h @pull_2 * [ // ]
#d elim d -d /2 width=1 by sd_SO_props/
qed.

(* Properties with sd_d *****************************************************)

lemma sd_d_SS (h):
      ∀s,d. sd_d h s (↑↑d) = sd_d h (⇡[h]s) (↑d).
// qed.

lemma sd_d_correct (h):
      sh_decidable h → sh_acyclic h →
      ∀s,d. deg (sd_d h s d) s d.
#h #Hhd #Hha @pull_2 * [ // ]
#d elim d -d [ // ] #d #IH #s
>(npsucc_pred d) in ⊢ (???%);
@(deg_inv_pred h)
[ /2 width=1 by sd_d_props/
| <nsucc_pnpred //
]
qed.
