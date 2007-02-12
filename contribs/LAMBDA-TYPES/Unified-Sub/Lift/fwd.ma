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

theorem lift_sort_1: \forall q, h, d, k, x.
                     Lift q h d (leaf (sort k)) x \to
                     x = leaf (sort k).
 intros. inversion H; clear H; intros;
 [ auto
 | destruct H3
 | destruct H4
 | destruct H5
 | destruct H7
 | destruct H7
 | destruct H8
 ].
qed.

theorem lift_lref_1: \forall q, h, d, k, x.
                     Lift q h d (leaf (lref k)) x \to
                     (q = false \land x = leaf (lref k)) \lor
                     (q = true \land k < d \land x = leaf (lref k)) \lor
                     (q = true \land d <= k \land 
		      \exists e. (k + h == e) \land x = leaf (lref e)
		     ). 
 intros. inversion H; clear H; intros;
 [ destruct H3
 | destruct H3. clear H3. subst. auto depth = 4
 | destruct H4. clear H4. subst. auto depth = 5
 | destruct H5. clear H5. subst. auto depth = 5
 | destruct H7
 | destruct H7
 | destruct H8
 ].
qed.

theorem lift_head_1: \forall q, l, i, p, z, u1, t1, x.
                     Lift q l i (head p z u1 t1) x \to
                     (p = q \land
		                  \exists r, u2, t2. 
		                  z = bind r \land
		                  Lift true l i u1 u2 \land Lift q l (succ i) t1 t2 \land
		                  x = head p z u2 t2
		                 ) \lor
		                 (p = q \land 
		                  \exists r,u2,t2. 
		                  z = flat r \land
		                  Lift true l i u1 u2 \land Lift q l i t1 t2 \land
		                  x = head p z u2 t2
		                 ) \lor
		                 ((p = q \to False) \land
		                  \exists u2,t2.
		                  Lift true l i u1 u2 \land Lift q l i t1 t2 \land
		                  x = head p z u2 t2
		                 ).
 intros. inversion H; clear H; intros;
 [ destruct H3
 | destruct H3
 | destruct H4
 | destruct H5
 | destruct H7. clear H7 H1 H3. subst. auto depth = 10
 | destruct H7. clear H7 H1 H3. subst. auto depth = 10
 | destruct H8. clear H8 H2 H4. subst. auto depth = 7
 ].
qed.