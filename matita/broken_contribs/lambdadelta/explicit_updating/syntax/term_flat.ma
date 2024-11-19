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

include "ground/xoa/ex_3_2.ma".
include "explicit_updating/syntax/term.ma".
include "explicit_updating/notation/functions/flat_1.ma".

(* FLATTENING FOR TERM ******************************************************)

(* Source: ❘·❘ (Barendregt, The λ-Calculus, 11.1.2 iii) *)
rec definition term_flat (t:𝕋) on t : 𝕋 ≝
match t with
[ lref p   ⇒ 𝛏p
| abst b t ⇒ 𝛌ⓕ.(term_flat t)
| appl v t ⇒ ＠(term_flat v).(term_flat t)
| lift f t ⇒ 𝛗f.(term_flat t)
].

interpretation
  "flattening (term)"
  'Flat t = (term_flat t).

definition flattenable: relation2 (relation2 …) (relation2 …) ≝
           λR1,R2. ∀t1,t2. R1 t1 t2 → R2 (♭t1) (♭t2)
. 

(* Basic constructions ******************************************************)

lemma term_flat_lref (p):
      (𝛏p) = ♭(𝛏p).
//
qed.

lemma term_flat_abst (b) (t):
      (𝛌ⓕ.♭t) = ♭(𝛌b.t).
//
qed.

lemma term_flat_appl (v) (t):
      (＠♭v.♭t) = ♭(＠v.t).
//
qed.

lemma term_flat_lift (f) (t):
      (𝛗f.♭t) = ♭(𝛗f.t).
//
qed.

(* Basic inversions *********************************************************)

lemma eq_inv_lref_flat (p) (y):
      (𝛏p) = ♭y → 𝛏p = y.
#p *
[ #z <term_flat_lref #H0 destruct //
| #z #x <term_flat_abst #H0 destruct
| #z #x <term_flat_appl #H0 destruct
| #z #x <term_flat_lift #H0 destruct
]
qed-.

lemma eq_inv_abst_flat (b) (t) (y):
      (𝛌b.t) = ♭y →
      ∃∃c,u. b = ⓕ & t = ♭u & 𝛌c.u = y.
#b #t *
[ #z <term_flat_lref #H0 destruct
| #z #x <term_flat_abst #H0 destruct
  /2 width=4 by ex3_2_intro/
| #z #x <term_flat_appl #H0 destruct
| #z #x <term_flat_lift #H0 destruct
]
qed-.

lemma eq_inv_appl_flat (v) (t) (y):
      (＠v.t) = ♭y →
      ∃∃w,u. v = ♭w & t = ♭u & ＠w.u = y.
#v #t *
[ #z <term_flat_lref #H0 destruct
| #z #x <term_flat_abst #H0 destruct
| #z #x <term_flat_appl #H0 destruct
  /2 width=5 by ex3_2_intro/
| #z #x <term_flat_lift #H0 destruct
]
qed-.

lemma eq_inv_lift_flat (f) (t) (y):
      (𝛗f.t) = ♭y →
      ∃∃u. t = ♭u & 𝛗f.u = y.
#f #t *
[ #z <term_flat_lref #H0 destruct
| #z #x <term_flat_abst #H0 destruct
| #z #x <term_flat_appl #H0 destruct
| #z #x <term_flat_lift #H0 destruct
  /2 width=3 by ex2_intro/
]
qed-.

(* Advanced inversions ******************************************************)

lemma eq_inv_flat_lref (x) (p):
      ♭x = 𝛏p → x =  𝛏p.
#x #p
/2 width=1 by eq_inv_lref_flat/
qed-.

lemma eq_inv_flat_abst (x) (b) (t):
      ♭x = 𝛌b.t →
      ∃∃c,u. ⓕ = b & ♭u = t & x = 𝛌c.u.
#x #b #t #Hx
elim (eq_inv_abst_flat … (sym_eq … Hx)) -Hx
/2 width=5 by ex3_2_intro/
qed-.

lemma eq_inv_flat_appl (x) (v) (t):
      ♭x = ＠v.t →
      ∃∃w,u. ♭w = v & ♭u = t & x = ＠w.u.
#x #v #t #Hx
elim (eq_inv_appl_flat … (sym_eq … Hx)) -Hx
/2 width=5 by ex3_2_intro/
qed-.

lemma eq_inv_flat_lift (x) (f) (t):
      ♭x = 𝛗f.t →
      ∃∃u. ♭u = t & x = 𝛗f.u.
#x #f #t #Hx
elim (eq_inv_lift_flat … (sym_eq … Hx)) -Hx
/2 width=3 by ex2_intro/
qed-.
