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

include "basic_2/syntax/term_simple.ma".
include "basic_2/syntax/tsts.ma".

(* SAME TOP TERM STRUCTURE **************************************************)

(* Properies with simple (neutral) terms ************************************)

lemma simple_tsts_repl_dx: ∀h,o,T1,T2. T1 ⩳[h, o] T2 → 𝐒⦃T1⦄ → 𝐒⦃T2⦄.
#h #o #T1 #T2 * -T1 -T2 //
#I #V1 #V2 #T1 #T2 #H
elim (simple_inv_pair … H) -H #J #H destruct //
qed-.

lemma simple_tsts_repl_sn: ∀h,o,T1,T2. T1 ⩳[h, o] T2 → 𝐒⦃T2⦄ → 𝐒⦃T1⦄.
/3 width=5 by simple_tsts_repl_dx, tsts_sym/ qed-.
