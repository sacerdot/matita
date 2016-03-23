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

include "basic_2/notation/relations/lazyeq_3.ma".
include "basic_2/grammar/ceq.ma".
include "basic_2/relocation/lexs.ma".

(* RANGED EQUIVALENCE FOR LOCAL ENVIRONMENTS ********************************)

(* Basic_2A1: includes: lreq_atom lreq_zero lreq_pair lreq_succ *)
definition lreq: relation3 rtmap lenv lenv ≝ lexs ceq cfull.

interpretation
  "ranged equivalence (local environment)"
  'LazyEq f L1 L2 = (lreq f L1 L2).

(* Basic properties *********************************************************)

lemma lreq_eq_repl_back: ∀L1,L2. eq_repl_back … (λf. L1 ≡[f] L2).
/2 width=3 by lexs_eq_repl_back/ qed-.

lemma lreq_eq_repl_fwd: ∀L1,L2. eq_repl_fwd … (λf. L1 ≡[f] L2).
/2 width=3 by lexs_eq_repl_fwd/ qed-.

lemma sle_lreq_trans: ∀L1,L2,f2. L1 ≡[f2] L2 →
                      ∀f1. f1 ⊆ f2 → L1 ≡[f1] L2.
/2 width=3 by sle_lexs_trans/ qed-.

(* Basic_2A1: includes: lreq_refl *)
lemma lreq_refl: ∀f. reflexive … (lreq f).
/2 width=1 by lexs_refl/ qed.

(* Basic_2A1: includes: lreq_sym *)
lemma lreq_sym: ∀f. symmetric … (lreq f).
#f #L1 #L2 #H elim H -L1 -L2 -f
/2 width=1 by lexs_next, lexs_push/
qed-.

(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: includes: lreq_inv_atom1 *)
lemma lreq_inv_atom1: ∀Y,f. ⋆ ≡[f] Y → Y = ⋆.
/2 width=4 by lexs_inv_atom1/ qed-.

(* Basic_2A1: includes: lreq_inv_pair1 *)
lemma lreq_inv_next1: ∀J,K1,Y,W1,g. K1.ⓑ{J}W1 ≡[⫯g] Y →
                      ∃∃K2. K1 ≡[g] K2 & Y = K2.ⓑ{J}W1.
#J #K1 #Y #W1 #g #H elim (lexs_inv_next1 … H) -H /2 width=3 by ex2_intro/
qed-.

(* Basic_2A1: includes: lreq_inv_zero1 lreq_inv_succ1 *)
lemma lreq_inv_push1: ∀J,K1,Y,W1,g. K1.ⓑ{J}W1 ≡[↑g] Y →
                      ∃∃K2,W2. K1 ≡[g] K2 & Y = K2.ⓑ{J}W2.
#J #K1 #Y #W1 #g #H elim (lexs_inv_push1 … H) -H /2 width=4 by ex2_2_intro/ qed-.

(* Basic_2A1: includes: lreq_inv_atom2 *)
lemma lreq_inv_atom2: ∀X,f. X ≡[f] ⋆ → X = ⋆.
/2 width=4 by lexs_inv_atom2/ qed-.

(* Basic_2A1: includes: lreq_inv_pair2 *)
lemma lreq_inv_next2: ∀J,X,K2,W2,g. X ≡[⫯g] K2.ⓑ{J}W2 →
                      ∃∃K1. K1 ≡[g] K2 & X = K1.ⓑ{J}W2.
#J #X #K2 #W2 #g #H elim (lexs_inv_next2 … H) -H /2 width=3 by ex2_intro/ qed-.

(* Basic_2A1: includes: lreq_inv_zero2 lreq_inv_succ2 *)
lemma lreq_inv_push2: ∀J,X,K2,W2,g. X ≡[↑g] K2.ⓑ{J}W2 →
                      ∃∃K1,W1. K1 ≡[g] K2 & X = K1.ⓑ{J}W1.
#J #X #K2 #W2 #g #H elim (lexs_inv_push2 … H) -H /2 width=4 by ex2_2_intro/ qed-.

(* Basic_2A1: includes: lreq_inv_pair *)
lemma lreq_inv_next: ∀I1,I2,L1,L2,V1,V2,f.
                     L1.ⓑ{I1}V1 ≡[⫯f] (L2.ⓑ{I2}V2) →
                     ∧∧ L1 ≡[f] L2 & V1 = V2 & I1 = I2.
/2 width=1 by lexs_inv_next/ qed-.

(* Basic_2A1: includes: lreq_inv_succ *)
lemma lreq_inv_push: ∀I1,I2,L1,L2,V1,V2,f.
                     L1.ⓑ{I1}V1 ≡[↑f] (L2.ⓑ{I2}V2) →
                     L1 ≡[f] L2 ∧ I1 = I2.
#I1 #I2 #L1 #L2 #V1 #V2 #f #H elim (lexs_inv_push … H) -H /2 width=1 by conj/
qed-.

lemma lreq_inv_tl: ∀I,L1,L2,V,f. L1 ≡[⫱f] L2 → L1.ⓑ{I}V ≡[f] L2.ⓑ{I}V.
/2 width=1 by lexs_inv_tl/ qed-.

(* Basic_2A1: removed theorems 5:
              lreq_pair_lt lreq_succ_lt lreq_pair_O_Y lreq_O2 lreq_inv_O_Y
*)
