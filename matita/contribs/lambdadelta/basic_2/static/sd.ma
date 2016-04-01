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

include "basic_2/static/sh.ma".

(* SORT DEGREE **************************************************************)

(* sort degree specification *)
record sd (h:sh): Type[0] ≝ {
   deg      : relation nat;                            (* degree of the sort *)
   deg_total: ∀s. ∃d. deg s d;                         (* functional relation axioms *)
   deg_mono : ∀s,d1,d2. deg s d1 → deg s d2 → d1 = d2;
   deg_next : ∀s,d. deg s d → deg (next h s) (⫰d)      (* compatibility condition *)
}.

(* Notable specifications ***************************************************)

definition deg_O: relation nat ≝ λs,d. d = 0.

definition sd_O: ∀h. sd h ≝ λh. mk_sd h deg_O ….
/2 width=2 by le_n_O_to_eq, le_n, ex_intro/ defined.

(* Basic_2A1: includes: deg_SO_pos *)
inductive deg_SO (h:sh) (s:nat) (s0:nat): predicate nat ≝
| deg_SO_succ : ∀n. (next h)^n s0 = s → deg_SO h s s0 (⫯n)
| deg_SO_zero: ((∃n. (next h)^n s0 = s) → ⊥) → deg_SO h s s0 0
.

fact deg_SO_inv_succ_aux: ∀h,s,s0,n0. deg_SO h s s0 n0 → ∀n. n0 = ⫯n →
                          (next h)^n s0 = s.
#h #s #s0 #n0 * -n0
[ #n #Hn #x #H destruct //
| #_ #x #H destruct
]
qed-.

(* Basic_2A1: was: deg_SO_inv_pos *)
lemma deg_SO_inv_succ: ∀h,s,s0,n. deg_SO h s s0 (⫯n) → (next h)^n s0 = s.
/2 width=3 by deg_SO_inv_succ_aux/ qed-.

lemma deg_SO_refl: ∀h,s. deg_SO h s s 1.
#h #s @(deg_SO_succ … 0 ?) //
qed.

lemma deg_SO_gt: ∀h,s1,s2. s1 < s2 → deg_SO h s1 s2 0.
#h #s1 #s2 #HK12 @deg_SO_zero * #n elim n -n normalize
[ #H destruct
  elim (lt_refl_false … HK12)
| #n #_ #H
  lapply (next_lt h ((next h)^n s2)) >H -H #H
  lapply (transitive_lt … H HK12) -s1 #H1
  lapply (nexts_le h s2 n) #H2
  lapply (le_to_lt_to_lt … H2 H1) -h -n #H
  elim (lt_refl_false … H)
]
qed.

definition sd_SO: ∀h. nat → sd h ≝ λh,s. mk_sd h (deg_SO h s) ….
[ #s0
  lapply (nexts_dec h s0 s) *
  [ * /3 width=2 by deg_SO_succ, ex_intro/ | /4 width=2 by deg_SO_zero, ex_intro/ ]
| #K0 #d1 #d2 * [ #n1 ] #H1 * [1,3: #n2 ] #H2 //
  [ < H2 in H1; -H2 #H
    lapply (nexts_inj … H) -H #H destruct //
  | elim H1 /2 width=2 by ex_intro/
  | elim H2 /2 width=2 by ex_intro/
  ]
| #s0 #n *
  [ #d #H destruct elim d -d normalize
    /2 width=1 by deg_SO_gt, deg_SO_succ, next_lt/
  | #H1 @deg_SO_zero * #d #H2 destruct
    @H1 -H1 @(ex_intro … (⫯d)) /2 width=1 by sym_eq/ (**) (* explicit constructor *)
  ]
]
defined.

rec definition sd_d (h:sh) (s:nat) (d:nat) on d : sd h ≝
   match d with
   [ O   ⇒ sd_O h
   | S d ⇒ match d with
           [ O ⇒ sd_SO h s
           | _ ⇒ sd_d h (next h s) d
           ]
   ].

(* Basic inversion lemmas ***************************************************)

lemma deg_inv_pred: ∀h,o,s,d. deg h o (next h s) (⫯d) → deg h o s (⫯⫯d).
#h #o #s #d #H1
elim (deg_total h o s) #n #H0
lapply (deg_next … H0) #H2
lapply (deg_mono … H1 H2) -H1 -H2 #H >H >S_pred /2 width=2 by ltn_to_ltO/
qed-.

lemma deg_inv_prec: ∀h,o,s,n,d. deg h o ((next h)^n s) (⫯d) → deg h o s (⫯(d+n)).
#h #o #s #n elim n -n normalize /3 width=1 by deg_inv_pred/
qed-.

(* Basic properties *********************************************************)

lemma deg_iter: ∀h,o,s,d,n. deg h o s d → deg h o ((next h)^n s) (d-n).
#h #o #s #d #n elim n -n normalize /3 width=1 by deg_next/
qed.

lemma deg_next_SO: ∀h,o,s,d. deg h o s (⫯d) → deg h o (next h s) d.
/2 width=1 by deg_next/ qed-.

lemma sd_d_SS: ∀h,s,d. sd_d h s (⫯⫯d) = sd_d h (next h s) (⫯d).
// qed.

lemma sd_d_correct: ∀h,d,s. deg h (sd_d h s d) s d.
#h #d elim d -d // #d elim d -d /3 width=1 by deg_inv_pred/
qed.
