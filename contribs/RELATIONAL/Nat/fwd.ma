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

set "baseuri" "cic:/matita/RELATIONAL/Nat/fwd".

include "logic/equality.ma".

include "Nat/defs.ma".

theorem eq_gen_zero_succ: \forall (P:Prop). \forall m2. zero = succ m2 \to P.
 intros. discriminate H.
qed.

theorem eq_gen_succ_zero: \forall (P:Prop). \forall m1. succ m1 = zero \to P.
 intros. discriminate H.
qed.

theorem eq_gen_succ_succ: \forall m1,m2. succ m1 = succ m2 \to m1 = m2.
 intros. injection H. assumption.
qed.
