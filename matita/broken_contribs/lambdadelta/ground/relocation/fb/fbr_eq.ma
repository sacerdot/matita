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

include "ground/relocation/fb/fbr_map.ma".
include "ground/lib/list_length.ma".
include "ground/lib/functions.ma".
include "ground/arith/wf2_ind_nlt.ma".
include "ground/arith/nat_plus.ma".
include "ground/notation/relations/doteq_2.ma".

(* EQUIVALENCE FOR FINITE RELOCATION MAPS WITH BOOLEANS *********************)

inductive fbr_eq: relation2 … ≝
(* Note: this is fbr_rcons_eq_repl *)
| fbr_eq_rcons_bi (b) (f1) (f2):
  fbr_eq f1 f2 → fbr_eq (f1◖b) (f2◖b)
| fbr_eq_id_push (f2):
  fbr_eq (𝐢) f2 → fbr_eq (𝐢) (⫯f2)
| fbr_eq_push_id (f1):
  fbr_eq f1 (𝐢) → fbr_eq (⫯f1) (𝐢)
| fbr_eq_id_bi:
  fbr_eq (𝐢) (𝐢)
.

interpretation
  "extensional equivalence (finite relocation maps with booleans)"
  'DotEq f1 f2 = (fbr_eq f1 f2).

(* Basic inversions *********************************************************)

lemma fbr_eq_inv_next_dx (x1) (f2):
      x1 ≐ ↑f2 →
      ∃∃f1. f1 ≐ f2 & ↑f1 = x1.
#x1 #g2
@(insert_eq_1 … (↑g2))
#x2 * -x1 -x2
[ * #f1 #f2 #Hf #H0 destruct
  /2 width=3 by ex2_intro/
| #f2 #_ #H0 destruct
| #f1 #_ #H0 destruct
| #H0 destruct
]
qed-.

lemma fbr_eq_inv_push_dx (x1) (f2):
      x1 ≐ ⫯f2 →
      ∨∨ ∃∃f1. f1 ≐ f2 & ⫯f1 = x1
       | ∧∧ (𝐢) ≐ f2 & (𝐢) = x1.
#x1 #g2
@(insert_eq_1 … (⫯g2))
#x2 * -x1 -x2
[ * #f1 #f2 #Hf #H0 destruct
  /3 width=3 by ex2_intro, or_introl/
| #f2 #Hf #H0 destruct
  /3 width=1 by or_intror, conj/
| #f1 #_ #H0 destruct
| #H0 destruct
]
qed-.

lemma fbr_eq_inv_id_dx (x1):
      x1 ≐ (𝐢) →
      ∨∨ ∃∃f1. f1 ≐ (𝐢) & ⫯f1 = x1
       | (𝐢) = x1.
#x1
@(insert_eq_1 … (𝐢))
#x2 * -x1 -x2
[ * #f1 #f2 #_ #H0 destruct
| #f2 #_ #H0 destruct
| #f1 #Hf #_
  /3 width=3 by ex2_intro, or_introl/
| #_ //
]
qed-.

lemma fbr_eq_inv_next_sx (f1) (x2):
      ↑f1 ≐ x2 →
      ∃∃f2. f1 ≐ f2 & ↑f2 = x2.
#g1 #x2
@(insert_eq_1 … (↑g1))
#x1 * -x1 -x2
[ * #f1 #f2 #Hf #H0 destruct
  /2 width=3 by ex2_intro/
| #f2 #_ #H0 destruct
| #f1 #_ #H0 destruct
| #H0 destruct
]
qed-.

lemma fbr_eq_inv_push_sx (f1) (x2):
      (⫯f1) ≐ x2 →
      ∨∨ ∃∃f2. f1 ≐ f2 & ⫯f2 = x2
       | ∧∧ f1 ≐ (𝐢) & (𝐢) = x2.
#g1 #x2
@(insert_eq_1 … (⫯g1))
#x1 * -x1 -x2
[ * #f1 #f2 #Hf #H0 destruct
  /3 width=3 by ex2_intro, or_introl/
| #f2 #_ #H0 destruct
| #f1 #Hf #H0 destruct
  /3 width=1 by or_intror, conj/
| #H0 destruct
]
qed-.

lemma fbr_eq_inv_id_sx (x2):
      (𝐢) ≐ x2 →
      ∨∨ ∃∃f2. (𝐢) ≐ f2 & ⫯f2 = x2
       | (𝐢) = x2.
#x2
@(insert_eq_1 … (𝐢))
#x1 * -x1 -x2
[ * #f1 #f2 #_ #H0 destruct
| #f2 #Hf #_
  /3 width=3 by ex2_intro, or_introl/
| #f1 #_ #H0 destruct
| #_ //
]
qed-.

(* Advanced invesions *******************************************************)

lemma fbr_eq_inv_next_bi (f1) (f2):
      ↑f1 ≐ ↑f2 → f1 ≐ f2.
#f1 #f2 #Hf
elim (fbr_eq_inv_next_dx … Hf) -Hf
#g2 #Hg #H0 destruct //
qed-.

lemma fbr_eq_inv_next_push (f1) (f2):
      ↑f1 ≐ ⫯f2 → ⊥.
#f1 #f2 #Hf
elim (fbr_eq_inv_next_sx … Hf) -Hf
#g1 #_ #H0 destruct
qed-.

lemma fbr_eq_inv_push_next (f1) (f2):
      (⫯f1) ≐ ↑f2 → ⊥.
#f1 #f2 #Hf
elim (fbr_eq_inv_next_dx … Hf) -Hf
#g2 #_ #H0 destruct
qed-.

lemma fbr_eq_inv_next_id (f1):
      ↑f1 ≐ (𝐢) → ⊥.
#f1 #Hf
elim (fbr_eq_inv_next_sx … Hf) -Hf
#g1 #_ #H0 destruct
qed-.

lemma fbr_eq_inv_id_next (f2):
      (𝐢) ≐ ↑f2 → ⊥.
#f2 #Hf
elim (fbr_eq_inv_next_dx … Hf) -Hf
#g2 #_ #H0 destruct
qed-.

lemma fbr_eq_inv_push_bi (f1) (f2):
      (⫯f1) ≐ ⫯f2 → f1 ≐ f2.
#f1 #f2 #Hf
elim (fbr_eq_inv_push_sx … Hf) -Hf *
[ #g1 #Hg #H0 destruct //
| #_ #H0 destruct
]
qed-.

lemma fbr_eq_inv_id_push (f2):
      (𝐢) ≐ ⫯f2 → (𝐢) ≐ f2.
#f2 #Hf
elim (fbr_eq_inv_push_dx … Hf) -Hf *
[ #g1 #_ #H0 destruct
| #Hg #_ //
]
qed-.

lemma fbr_eq_inv_push_id (f1):
      (⫯f1) ≐ (𝐢) → f1 ≐ (𝐢).
#f1 #Hf
elim (fbr_eq_inv_push_sx … Hf) -Hf *
[ #g2 #_ #H0 destruct
| #Hg #_ //
]
qed-.

(* Basic constructions ******************************************************)

lemma fbr_eq_refl:
      reflexive … fbr_eq.
#f elim f -f //
* #f #IH
/2 width=1 by fbr_eq_rcons_bi/
qed.

theorem fbr_eq_repl:
        replace_2 … fbr_eq fbr_eq fbr_eq.
#f1 #f2 #Hf elim Hf -f1 -f2
[ * #f1 #f2 #_ #IH #x1 #Hx1 #x2 #Hx2
  [ elim (fbr_eq_inv_next_sx … Hx1) -Hx1
    elim (fbr_eq_inv_next_sx … Hx2) -Hx2
    #g2 #Hfg2 #H2 #g1 #Hfg1 #H1 destruct
    /3 width=1 by fbr_eq_rcons_bi/
  | elim (fbr_eq_inv_push_sx … Hx1) -Hx1 *
    elim (fbr_eq_inv_push_sx … Hx2) -Hx2 *
    [ #g2 #Hfg2 #H2 #g1 #Hfg1 #H1 destruct
      /3 width=1 by fbr_eq_rcons_bi/
    | #Hf2 #H2 #g1 #Hfg1 #H1 destruct
      /3 width=1 by fbr_eq_push_id/
    | #g2 #Hfg2 #H2 #Hf1 #H1 destruct
      /3 width=1 by fbr_eq_id_push/
    | #Hf2 #H2 #Hf1 #H1 destruct //
    ]
  ]
| #f2 #_ #IH #x1 #Hx1 #x2 #Hx2
  elim (fbr_eq_inv_id_sx … Hx1) -Hx1
  elim (fbr_eq_inv_push_sx … Hx2) -Hx2 *
  [ #g2 #Hfg2 #H2 * #g1 #Hg1 #H1 destruct
    /3 width=1 by fbr_eq_rcons_bi/
  | #Hf2 #H2 * #g1 #Hg1 #H1 destruct
    /3 width=1 by fbr_eq_push_id/
  | #g2 #Hfg2 #H2 #H1 destruct
    /3 width=1 by fbr_eq_id_push/
  | #Hf2 #H2 #H1 destruct //
  ]
| #f1 #_ #IH #x1 #Hx1 #x2 #Hx2
  elim (fbr_eq_inv_push_sx … Hx1) -Hx1 *
  elim (fbr_eq_inv_id_sx … Hx2) -Hx2
  [ * #g2 #Hg2 #H2 #g1 #Hfg1 #H1 destruct
    /3 width=1 by fbr_eq_rcons_bi/
  | #H2 #g1 #Hfg1 #H1 destruct
    /3 width=1 by fbr_eq_push_id/
  | * #g2 #Hg2 #H2 #Hf1 #H1 destruct
    /3 width=1 by fbr_eq_id_push/
  | #H2 #Hf1 #H1 destruct //
  ]
| #x1 #Hx1 #x2
  generalize in match Hx1; -Hx1
  @(wf2_ind_nlt … (λx1,x2.❘x1❘+❘x2❘) … x1 x2) -x1 -x2
  #n #IH #x1 #x2 #Hn #Hx1 #Hx2 destruct
  elim (fbr_eq_inv_id_sx … Hx1) -Hx1
  elim (fbr_eq_inv_id_sx … Hx2) -Hx2
  [ * #g2 #Hg2 #H2 * #g1 #Hg1 #H1 destruct
    /3 width=1 by fbr_eq_rcons_bi/
  | #H2 * #g1 #Hg1 #H1 destruct
    /3 width=1 by fbr_eq_push_id/
  | * #g2 #Hg2 #H2 #H1 destruct
    /3 width=1 by fbr_eq_id_push/
  | #H2 #H1 destruct //
  ]
]
qed-.

(* Advanced constructions ***************************************************)

lemma fbr_eq_sym:
      symmetric … fbr_eq.
/2 width=5 by fbr_eq_repl/
qed-.

lemma fbr_eq_trans:
      Transitive … fbr_eq.
/2 width=5 by fbr_eq_repl/
qed-.

lemma fbr_eq_canc_sx:
      left_cancellable … fbr_eq.
/2 width=5 by fbr_eq_repl/
qed-.

lemma fbr_eq_canc_dx:
      right_cancellable … fbr_eq.
/3 width=5 by fbr_eq_sym, fbr_eq_repl/
qed-.

lemma fbr_eq_replace_sym (Q):
      replace_1_back … fbr_eq Q → replace_1_fwd … fbr_eq Q.
/3 width=3 by fbr_eq_sym/
qed-.

lemma fbr_id_push_id:
      (𝐢) ≐ ⫯𝐢.
/2 width=1 by fbr_eq_id_push, fbr_eq_id_bi/
qed.

lemma fbr_append_eq_repl_sx (f):
      compatible_2_fwd … fbr_eq fbr_eq (λg.g●f).
#f elim f -f //
#b #f #IH #g1 #g2 #Hg
/3 width=1 by fbr_eq_rcons_bi/
qed.

lemma fbr_push_sx_eq_repl:
      compatible_2_fwd … fbr_eq fbr_eq (λf.𝗽◗f).
#f1 #f2 #Hf elim Hf -f1 -f2 //
[ /2 width=1 by fbr_eq_rcons_bi/
| /3 width=3 by fbr_eq_rcons_bi, fbr_eq_trans/
| /3 width=3 by fbr_eq_rcons_bi, fbr_eq_canc_dx/
]
qed.
