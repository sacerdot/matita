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



include "NPlus/fun.ma".
include "ZEq/defs.ma".

theorem zeq_refl: ∀z. z ≈ z.
 intros; elim z. clear z.
 lapply (nplus_total a b); decompose;
 autobatch.
qed.

theorem zeq_sym: ∀z1,z2. z1 ≈ z2 → z2 ≈ z1.
 intros; elim H; clear H z1 z2; autobatch.
qed.
(*
theorem zeq_trans: \forall z1,z2. z1 = z2 \to 
                   \forall z3. z2 = z3 \to z1 = z3.
 intros 3. elim H. clear H z1 z2. 
 inversion H3. clear H3. intros. destruct.
 lapply (nplus_total n5 n6). decompose.
 lapply (nplus_total n4 n9). decompose.
 apply zeq.
*)
