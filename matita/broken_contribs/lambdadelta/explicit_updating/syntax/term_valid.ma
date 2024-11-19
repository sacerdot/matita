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

include "ground/xoa/ex_4_1.ma".
include "ground/generated/insert_eq_1.ma".
include "explicit_updating/syntax/term.ma".
include "explicit_updating/notation/relations/vdash_2.ma".

(* VALIDITY FOR TERM ********************************************************)

(* Source: Barendregt, The λ-Calculus, 11.1.2 ii *)
inductive term_valid (b): predicate (𝕋) ≝
| term_valid_lref (p):
  term_valid b (𝛏p)
| term_valid_abst (t):
  term_valid b t → term_valid b (𝛌ⓕ.t)
| term_valid_appl (v) (t):
  term_valid b v → term_valid b t → term_valid b (＠v.t)
| term_valid_lift (f) (t):
  term_valid b t → term_valid b (𝛗f.t)
| term_valid_beta (v) (t):
  term_valid b v → term_valid b t → term_valid b (＠v.𝛌b.t)
. 

interpretation
  "validity (term)"
  'VDash b t = (term_valid b t).

(* Basic inversions *********************************************************)

lemma term_valid_inv_abst (b1) (b2) (t):
      b1 ⊢ 𝛌b2.t →
      ∧∧ b1 ⊢ t & ⓕ = b2.
#b1 #b2 #u
@(insert_eq_1 … (𝛌b2.u)) #x * -x
[ #p #H0 destruct
| #b #t #H0 destruct
  /2 width=1 by conj/
| #v #t #_ #_ #H0 destruct
| #f #t #_ #H0 destruct
| #v #t #_ #_ #H0 destruct
]
qed-.

lemma term_valid_inv_appl (b) (v) (t):
      b ⊢ ＠v.t →
      ∨∨ ∧∧ b ⊢ v & b ⊢ t
       | ∃∃u. b ⊢ v & b ⊢ u & ⓣ = b & 𝛌ⓣ.u = t.
#z #w #u
@(insert_eq_1 … (＠w.u)) #x * -x
[ #p #H0 destruct
| #b #t #H0 destruct
| #v #t #Hv #Ht #H0 destruct
  /3 width=1 by or_introl, conj/
| #f #t #_ #H0 destruct
| #v #t cases z #Hv #Ht #H0 destruct
  [ /3 width=3 by or_intror, ex4_intro/
  | /4 width=1 by term_valid_abst, or_introl, conj/
  ]
]
qed-.

lemma term_valid_inv_lift (b) (f) (t):
      b ⊢ 𝛗f.t → b ⊢ t.
#x #g #u
@(insert_eq_1 … (𝛗g.u)) #x * -x
[ #p #H0 destruct
| #b #t #H0 destruct
| #v #t #_ #_ #H0 destruct
| #f #t #Ht #H0 destruct //
| #v #t #_ #_ #H0 destruct
]
qed-.

(* Advanced inversions ******************************************************)

lemma term_valid_inv_appl_false (v) (t):
      (ⓕ) ⊢ ＠v.t →
      ∧∧ ⓕ ⊢ v & ⓕ ⊢ t.
#v #t #H0
elim (term_valid_inv_appl … H0) -H0 *
[ /2 width=1 by conj/
| #x #_ #_ #H0 destruct
]
qed-.

(* Advanced constructions ***************************************************)

lemma term_valid_false (b) (t):
      (ⓕ) ⊢ t → b ⊢ t.
#z #t elim t -t
[ #p #H0 //
| #b #t #IH #H0
  elim (term_valid_inv_abst … H0) -H0 #Ht #H0 destruct
  /3 width=1 by term_valid_abst/
| #v #t #IHv #IHt #H0
  elim (term_valid_inv_appl … H0) -H0 *
  [ /3 width=1 by term_valid_appl/
  | #x #_ #_ #H0 #_ -x destruct
  ]
| #f #t #IH #H0
  lapply (term_valid_inv_lift … H0) -H0 #Ht
  /3 width=1 by term_valid_lift/
]
qed-.
