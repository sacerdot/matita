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

include "basic_2/syntax/ceq_ext_ceq_ext.ma".
include "basic_2/relocation/sex_sex.ma".

(* SYNTACTIC EQUIVALENCE FOR SELECTED LOCAL ENVIRONMENTS ********************)

(* Main properties **********************************************************)

theorem seq_trans: ∀f. Transitive … (seq f).
/3 width=5 by sex_trans, ceq_ext_trans/ qed-.

theorem seq_canc_sn: ∀f. left_cancellable … (seq f).
/3 width=3 by sex_canc_sn, seq_trans, seq_sym/ qed-.

theorem seq_canc_dx: ∀f. right_cancellable … (seq f).
/3 width=3 by sex_canc_dx, seq_trans, seq_sym/ qed-.

theorem seq_join: ∀f1,L1,L2. L1 ≡[f1] L2 → ∀f2. L1 ≡[f2] L2 →
                  ∀f. f1 ⋓ f2 ≘ f → L1 ≡[f] L2.
/2 width=5 by sex_join/ qed-.

theorem seq_meet: ∀f1,L1,L2. L1 ≡[f1] L2 → ∀f2. L1 ≡[f2] L2 →
                  ∀f. f1 ⋒ f2 ≘ f → L1 ≡[f] L2.
/2 width=5 by sex_meet/ qed-.
