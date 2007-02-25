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

set "baseuri" "cic:/matita/RELATIONAL/NLE/inv".

include "NLE/defs.ma".

theorem nle_inv_succ_1: \forall x,y. x < y \to 
                        \exists z. y = succ z \land x <= z.
 intros. inversion H; clear H; intros; subst;
 [ destruct H
 | destruct H2. clear H2. subst. auto
 ]
qed.

theorem nle_inv_succ_succ: \forall x,y. x < succ y \to x <= y.
 intros. inversion H; clear H; intros; subst;
 [ destruct H
 | destruct H2. destruct H3. clear H2 H3. subst. auto
 ]
qed.

theorem nle_inv_succ_zero: \forall x. x < zero \to False.
 intros. inversion H; clear H; intros; subst;
 [ destruct H
 | destruct H3
 ]
qed.

theorem nle_inv_zero_2: \forall x. x <= zero \to x = zero.
 intros. inversion H; clear H; intros; subst;
 [ auto
 | destruct H3
 ].
qed.

theorem nle_inv_succ_2: \forall y,x. x <= succ y \to
                        x = zero \lor \exists z. x = succ z \land z <= y.
 intros. inversion H; clear H; intros; subst;
 [ auto
 | destruct H3. clear H3. subst. auto depth = 4
 ].
qed.
