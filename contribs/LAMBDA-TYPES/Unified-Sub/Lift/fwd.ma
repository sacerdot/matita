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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Unified-Sub/Lift/fwd".

include "Lift/defs.ma".

theorem lift_inv_sort_1: \forall l, i, h, x.
                         Lift l i (leaf (sort h)) x \to
                         x = leaf (sort h).
 intros. inversion H; clear H; intros;
 [ auto
 | destruct H2
 | destruct H3
 | destruct H5
 | destruct H5
 ].
qed.

theorem lift_inv_lref_1: \forall l, i, j1, x.
                         Lift l i (leaf (lref j1)) x \to
                         (i > j1 \land x = leaf (lref j1)) \lor
                         (i <= j1 \land 
                          \exists j2. (l + j1 == j2) \land x = leaf (lref j2)
                         ).
 intros. inversion H; clear H; intros;
 [ destruct H1
 | destruct H2. clear H2. subst. auto
 | destruct H3. clear H3. subst. auto depth = 5
 | destruct H5
 | destruct H5
 ].
qed.

theorem lift_inv_bind_1: \forall l, i, r, u1, t1, x.
                         Lift l i (intb r u1 t1) x \to
                         \exists u2, t2. 
                         Lift l i u1 u2 \land
                         Lift l (succ i) t1 t2 \land
                         x = intb r u2 t2.
 intros. inversion H; clear H; intros;
 [ destruct H1
 | destruct H2
 | destruct H3
 | destruct H5. clear H5 H1 H3. subst. auto depth = 5
 | destruct H5
 ].
qed.

theorem lift_inv_flat_1: \forall l, i, r, u1, t1, x.
                         Lift l i (intf r u1 t1) x \to
                         \exists u2, t2. 
                         Lift l i u1 u2 \land
                         Lift l i t1 t2 \land
                         x = intf r u2 t2.
 intros. inversion H; clear H; intros;
 [ destruct H1
 | destruct H2
 | destruct H3
 | destruct H5 
 | destruct H5. clear H5 H1 H3. subst. auto depth = 5
 ].
qed.
