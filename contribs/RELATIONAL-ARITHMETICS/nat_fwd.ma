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

set "baseuri" "cic:/matita/RELATIONAL-ARITHMETICS/nat_gen".

include "library/logic/equality.ma".
include "nat_defs.ma".

theorem eq_gen_O_S: \forall (P:Prop). \forall m2. O = S m2 \to P.
 intros. discriminate H.
qed.

theorem eq_gen_S_O: \forall (P:Prop). \forall m1. S m1 = O \to P.
 intros. discriminate H.
qed.

theorem eq_gen_S_S: \forall m1,m2. S m1 = S m2 \to m1 = m2.
 intros. injection H. assumption.
qed.
