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



(*
*)

include "Insert/defs.ma".
(*
theorem insert_inv_zero: \forall S,P,Q. Insert S zero P Q \to Q = abst P S.
 intros; inversion H; clear H; intros; destruct; autobatch.
qed.

theorem insert_inv_succ: \forall S,Q1,Q2,i. Insert S (succ i) Q1 Q2 \to
                         \exists P1,P2,R. Insert S i P1 P2 \land
                                          Q1 = abst P1 R \land Q2 = abst P2 R.
 intros; inversion H; clear H; intros; destruct; autobatch depth = 6 size = 8.
qed.

theorem insert_inv_leaf_1: \forall Q,S,i. Insert S i leaf Q \to
                           i = zero \land Q = S.
 intros. inversion H; clear H; intros; destruct. autobatch.
qed.

theorem insert_inv_abst_1: \forall P,Q,R,S,i. Insert S i (abst P R) Q \to
                           (i = zero \land Q = (abst (abst P R) S)) \lor
                           \exists n, c1. 
                           i = succ n \land Q = abst c1 R \land 
                           Insert S n P c1.
 intros. inversion H; clear H; intros; destruct; autobatch depth = 6 size =  8.
qed.

theorem insert_inv_leaf_2: \forall P,S,i. Insert S i P leaf \to False.
 intros. inversion H; clear H; intros; destruct.
qed.

theorem insert_inv_abst_2: \forall P,i. \forall R,S:Sequent.
                           Insert S i P R \to 
                           i = zero \land P = leaf \land R = S.
 intros. inversion H; clear H; intros; destruct; 
 [ autobatch
 | clear H1. lapply linear insert_inv_leaf_2 to H. decompose
 ].
qed.
*)
