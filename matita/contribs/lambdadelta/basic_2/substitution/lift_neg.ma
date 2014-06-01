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

include "basic_2/substitution/lift.ma".

(* BASIC TERM RELOCATION ****************************************************)

(* Properties on negated basic relocation ***********************************)

lemma nlift_lref_be_SO: ∀X,i. ⇧[i, 1] X ≡ #i → ⊥.
/2 width=7 by lift_inv_lref2_be/ qed-.

lemma nlift_bind_sn: ∀W,d,e. (∀V. ⇧[d, e] V ≡ W → ⊥) →
                     ∀a,I,U. (∀X. ⇧[d, e] X ≡ ⓑ{a,I}W.U → ⊥).
#W #d #e #HW #a #I #U #X #H elim (lift_inv_bind2 … H) -H /2 width=2 by/
qed-.

lemma nlift_bind_dx: ∀U,d,e. (∀T. ⇧[d+1, e] T ≡ U → ⊥) →
                     ∀a,I,W. (∀X. ⇧[d, e] X ≡ ⓑ{a,I}W.U → ⊥).
#U #d #e #HU #a #I #W #X #H elim (lift_inv_bind2 … H) -H /2 width=2 by/
qed-.

lemma nlift_flat_sn: ∀W,d,e. (∀V. ⇧[d, e] V ≡ W → ⊥) →
                     ∀I,U. (∀X. ⇧[d, e] X ≡ ⓕ{I}W.U → ⊥).
#W #d #e #HW #I #U #X #H elim (lift_inv_flat2 … H) -H /2 width=2 by/
qed-.

lemma nlift_flat_dx: ∀U,d,e. (∀T. ⇧[d, e] T ≡ U → ⊥) →
                     ∀I,W. (∀X. ⇧[d, e] X ≡ ⓕ{I}W.U → ⊥).
#U #d #e #HU #I #W #X #H elim (lift_inv_flat2 … H) -H /2 width=2 by/
qed-.

(* Inversion lemmas on negated basic relocation *****************************)

lemma nlift_inv_lref_be_SO: ∀i,j. (∀X. ⇧[i, 1] X ≡ #j → ⊥) → j = i.
#i #j elim (lt_or_eq_or_gt i j) // #Hij #H
[ elim (H (#(j-1))) -H /2 width=1 by lift_lref_ge_minus/
| elim (H (#j)) -H /2 width=1 by lift_lref_lt/
]
qed-.

lemma nlift_inv_bind: ∀a,I,W,U,d,e. (∀X. ⇧[d, e] X ≡ ⓑ{a,I}W.U → ⊥) →
                      (∀V. ⇧[d, e] V ≡ W → ⊥) ∨ (∀T. ⇧[d+1, e] T ≡ U → ⊥).
#a #I #W #U #d #e #H elim (is_lift_dec W d e)
[ * /4 width=2 by lift_bind, or_intror/
| /4 width=2 by ex_intro, or_introl/
]
qed-.

lemma nlift_inv_flat: ∀I,W,U,d,e. (∀X. ⇧[d, e] X ≡ ⓕ{I}W.U → ⊥) →
                      (∀V. ⇧[d, e] V ≡ W → ⊥) ∨ (∀T. ⇧[d, e] T ≡ U → ⊥).
#I #W #U #d #e #H elim (is_lift_dec W d e)
[ * /4 width=2 by lift_flat, or_intror/
| /4 width=2 by ex_intro, or_introl/
]
qed-.
