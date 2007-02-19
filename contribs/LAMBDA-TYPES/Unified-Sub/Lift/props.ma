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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Unified-Sub/Lift/props".

include "Lift/fun.ma".

(* NOTE: this holds because of nplus_comm_1 *)
theorem lift_comp: \forall l1,i1,t1,t2. Lift l1 i1 t1 t2 \to
                   \forall l2,i2,u1. Lift l2 i2 t1 u1 \to
                   \forall x. Lift l2 i2 t2 x \to
                   \forall i,y. Lift l1 i u1 y \to
                   i1 >= i2 \to (l2 + i1 == i) \to x = y.
 intros 5. elim H; clear H i1 t1 t2;
 [ lapply lift_mono to H1, H2. clear H2. subst.
   lapply linear lift_inv_sort_1 to H1. subst.
   lapply linear lift_inv_sort_1 to H3. subst. auto
 | lapply lift_mono to H2, H3. clear H3. subst.
   lapply linear lift_inv_lref_1 to H2.
   decompose; subst; clear H2 H5;
   lapply linear lift_inv_lref_1_gt to H4; subst; auto width = 4
 | lapply lift_inv_lref_1_le to H3; [ 2: auto ]. clear H3.
   lapply lift_inv_lref_1_le to H4; [ 2: auto ]. clear H4.
   decompose. subst. clear H6 i2.
   lapply lift_inv_lref_1_le to H5; [ 2: auto depth = 4 width = 4 ]. 
   decompose. subst. clear H5 H1 H7 i. auto depth = 4
 | clear H1 H3.
   lapply linear lift_inv_bind_1 to H5.
   lapply linear lift_inv_bind_1 to H6. decompose. subst.
   lapply linear lift_inv_bind_1 to H7. decompose. subst.
   auto width = 5
 | clear H1 H3.
   lapply linear lift_inv_flat_1 to H5.
   lapply linear lift_inv_flat_1 to H6. decompose. subst.
   lapply linear lift_inv_flat_1 to H7. decompose. subst.
   auto width = 5
 ].
qed.

theorem lift_comp_rew_dx: \forall l1,i1,t1,t2. Lift l1 i1 t1 t2 \to
                          \forall l2,i2,u1. Lift l2 i2 t1 u1 \to
                          \forall u2. Lift l2 i2 t2 u2 \to
                          i1 >= i2 \to \forall i. (l2 + i1 == i) \to
                          Lift l1 i u1 u2.
 intros.
 lapply (lift_total l1 u1 i). decompose.
 lapply lift_comp to H, H1, H2, H5, H3, H4. subst. auto.
qed.

theorem lift_comp_rew_sx: \forall l1,i1,t1,t2. Lift l1 i1 t1 t2 \to
                          \forall l2,i2,u1. Lift l2 i2 t1 u1 \to
                          \forall i,u2. Lift l2 i t2 u2 \to
                          i2 >= i1 \to (l1 + i2 == i) \to
                          Lift l1 i1 u1 u2.
 intros.
 lapply (lift_total l1 u1 i1). decompose.
 lapply lift_comp to H1, H, H5, H2, H3, H4. subst. auto.
qed.
(*
theorem lift_trans_le: \forall l1,i1,t1,t2. Lift l1 i1 t1 t2 \to
                       \forall l2,i2,z. Lift l2 i2 t2 t3 \to
		       i1 <= i2 \to 
		       \forall i. \to i2 <= i \to (l1 + i1 == i) \to
		       \forall l. (l1 + l2 == l) \to Lift l i1 t1 t3.

axiom lift_conf_back_ge: \forall l1,i1,u1,u2. Lift l1 i1 u1 u2 \to
	                 \forall l2,i,t2. Lift l2 i t2 u2 \to
	                 \forall i2. i2 >= i1 \to (l1 + i2 == i) \to
                         \exists t1. | Lift l2 i2 t1 u1 \land
                                       Lift l1 i1 t1 t2.

*)
