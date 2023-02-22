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

include "static_2/notation/relations/ideq_2.ma".
include "static_2/syntax/teqg.ma".

(* SYNTACTIC EQUIVALENCE ON TERMS *******************************************)

definition teq: relation term ≝
           teqg (eq …).

interpretation
  "context-free syntactic equivalence (term)"
  'IdEq T1 T2 = (teq T1 T2).

(* Basic properties *********************************************************)

lemma teq_refl:
      reflexive … teq.
/2 width=1 by teqg_refl/ qed.

lemma teq_sym:
      symmetric … teq.
/2 width=1 by teqg_sym/ qed-.

(* Basic inversion lemmas ***************************************************)

lemma teq_inv_eq:
      ∀T1,T2. T1 ≡ T2 → T1 = T2.
#T1 #T2 #H elim H -H //
qed-.

(* Advanced forward lemmas **************************************************)

lemma teq_repl_1 (R:predicate …):
      ∀T1. R T1 → ∀T2. T1 ≡ T2 → R T2.
#R #T1 #HT1 #T2 #HT12
<(teq_inv_eq … HT12) -T2 //
qed-.

lemma teq_sym_repl_1 (R:predicate …):
      ∀T1. R T1 → ∀T2. T2 ≡ T1 → R T2.
#R #T1 #HT1 #T2 #HT12
>(teq_inv_eq … HT12) -T2 //
qed-.
