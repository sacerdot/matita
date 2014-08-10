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

include "basic_2/grammar/tsts.ma".

(* SAME TOP TERM STRUCTURE **************************************************)

(* Main properties **********************************************************)

(* Basic_1: was: iso_trans *)
theorem tsts_trans: Transitive … tsts.
#T1 #T * -T1 -T //
#I #V1 #V #T1 #T #X #H
elim (tsts_inv_pair1 … H) -H #V2 #T2 #H destruct //
qed-.

theorem tsts_canc_sn: ∀T,T1. T ≂ T1 → ∀T2. T ≂ T2 → T1 ≂ T2.
/3 width=3 by tsts_trans, tsts_sym/ qed-.

theorem tsts_canc_dx: ∀T1,T. T1 ≂ T → ∀T2. T2 ≂ T → T1 ≂ T2.
/3 width=3 by tsts_trans, tsts_sym/ qed-.
