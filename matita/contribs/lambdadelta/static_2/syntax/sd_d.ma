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

include "static_2/syntax/sh_props.ma".
include "static_2/syntax/sd.ma".

(* SORT DEGREE **************************************************************)

(* Basic_2A1: includes: deg_SO_pos *)
inductive deg_SO (h) (s) (s0): predicate nat ≝
| deg_SO_succ : ∀n. (next h)^n s0 = s → deg_SO h s s0 (↑n)
| deg_SO_zero: (∀n. (next h)^n s0 = s → ⊥) → deg_SO h s s0 0
.

fact deg_SO_inv_succ_aux (h) (s) (s0):
     ∀n0. deg_SO h s s0 n0 → ∀n. n0 = ↑n → (next h)^n s0 = s.
#h #s #s0 #n0 * -n0
[ #n #Hn #x #H destruct //
| #_ #x #H destruct
]
qed-.

(* Basic_2A1: was: deg_SO_inv_pos *)
lemma deg_SO_inv_succ (h) (s) (s0):
      ∀n. deg_SO h s s0 (↑n) → (next h)^n s0 = s.
/2 width=3 by deg_SO_inv_succ_aux/ qed-.

lemma deg_SO_refl (h) (s): deg_SO h s s 1.
#h #s @(deg_SO_succ … 0 ?) //
qed.

definition sd_SO (h) (s): sd ≝ mk_sd (deg_SO h s).

lemma sd_SO_props (h) (s): sh_decidable h → sh_acyclic h →
      sd_props h (sd_SO h s).
#h #s #Hhd #Hha
@mk_sd_props
[ #s0
  elim (nexts_dec … Hhd s0 s) -Hhd
  [ * /3 width=2 by deg_SO_succ, ex_intro/
  | /5 width=2 by deg_SO_zero, ex_intro/
  ]
| #s0 #d1 #d2 * [ #n1 ] #H1 * [1,3: #n2 ] #H2
  [ < H2 in H1; -H2 #H
    lapply (nexts_inj … Hha … H) -H #H destruct //
  | elim H1 /2 width=2 by ex_intro/
  | elim H2 /2 width=2 by ex_intro/
  | //
  ]
| #s0 #d *
  [ #n #H destruct cases n -n normalize
    [ @deg_SO_zero #n >iter_n_Sm #H
      lapply (nexts_inj … Hha … (↑n) 0 H) -H #H destruct
    | #n @deg_SO_succ >iter_n_Sm //
    ]
  | #H0 @deg_SO_zero #n >iter_n_Sm #H destruct
    /2 width=2 by/
  ]
]
qed.

rec definition sd_d (h:?) (s:?) (d:?) on d: sd ≝
   match d with
   [ O   ⇒ sd_O
   | S d ⇒ match d with
           [ O ⇒ sd_SO h s
           | _ ⇒ sd_d h (next h s) d
           ]
   ].

lemma sd_d_props (h) (s) (d): sh_decidable h → sh_acyclic h →
      sd_props h (sd_d h s d).
#h @pull_2 * [ // ]
#d elim d -d /2 width=1 by sd_SO_props/
qed.

(* Properties with sd_d *****************************************************)

lemma sd_d_SS (h):
      ∀s,d. sd_d h s (↑↑d) = sd_d h (⫯[h]s) (↑d).
// qed.

lemma sd_d_correct (h): sh_decidable h → sh_acyclic h →
      ∀s,d. deg (sd_d h s d) s d.
#h #Hhd #Hha @pull_2 #d elim d -d [ // ]
#d elim d -d /3 width=3 by deg_inv_pred, sd_d_props/
qed.
