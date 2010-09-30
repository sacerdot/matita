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

include "Class/defs.ma".

(* CLASSES:
   - Here we prove the standard properties of the equality.
*)

theorem ceq_cin_fw: ∀C,c1,c2. ceq C c1 c2 → cin ? c1 → cin ? c2.
intros 4; elim H; clear H c1 c2; autobatch.
qed.

theorem ceq_cin_bw: ∀C,c1,c2. ceq C c1 c2 → cin ? c2 → cin ? c1.
intros 4; elim H; clear H c1 c2; autobatch.
qed.

theorem ceq_trans: ∀C,c1,c2. ceq C c1 c2 → ∀c3. ceq ? c2 c3 → ceq ? c1 c3.
intros 4; elim H; clear H c1 c2; autobatch.
qed.

theorem ceq_sym: ∀ C,c1,c2. ceq C c1 c2 → ceq ? c2 c1.
intros; elim H; clear H c1 c2; autobatch.
qed.

theorem ceq_conf: ∀C,c1,c2. ceq C c1 c2 → ∀c3. ceq ? c1 c3 → ceq ? c2 c3.
intros; autobatch.
qed.

theorem ceq_repl: ∀C,c1,c2. ceq C c1 c2 →
                  ∀d1. ceq ? c1 d1 → ∀d2. ceq ? c2 d2 → ceq ? d1 d2.
intros; autobatch.
qed.
