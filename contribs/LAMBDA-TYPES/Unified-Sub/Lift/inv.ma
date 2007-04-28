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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Unified-Sub/Lift/inv".

include "Lift/defs.ma".

(* Inversion properties *****************************************************)

theorem lift_inv_sort_1: \forall l, i, h, x.
                         Lift l i (sort h) x \to
                         x = sort h.
 intros. inversion H; clear H; intros; subst. auto.
qed.

theorem lift_inv_lref_1: \forall l, i, j1, x.
                         Lift l i (lref j1) x \to
                         (i > j1 \land x = lref j1) \lor
                         (i <= j1 \land 
                          \exists j2. (l + j1 == j2) \land x = lref j2
                         ).
 intros. inversion H; clear H; intros; subst; auto depth = 5.
qed.

theorem lift_inv_bind_1: \forall l, i, r, u1, t1, x.
                         Lift l i (intb r u1 t1) x \to
                         \exists u2, t2. 
                         Lift l i u1 u2 \land
                         Lift l (succ i) t1 t2 \land
                         x = intb r u2 t2.
 intros. inversion H; clear H; intros; subst. auto depth = 5.
qed.

theorem lift_inv_flat_1: \forall l, i, r, u1, t1, x.
                         Lift l i (intf r u1 t1) x \to
                         \exists u2, t2. 
                         Lift l i u1 u2 \land
                         Lift l i t1 t2 \land
                         x = intf r u2 t2.
 intros. inversion H; clear H; intros; subst. auto depth = 5.
qed.

theorem lift_inv_sort_2: \forall l, i, x, h.
                         Lift l i x (sort h) \to
                         x = sort h.
 intros. inversion H; clear H; intros; subst. auto.
qed.

theorem lift_inv_lref_2: \forall l, i, x, j2.
                         Lift l i x (lref j2) \to
                         (i > j2 \land x = lref j2) \lor
                         (i <= j2 \land 
                          \exists j1. (l + j1 == j2) \land x = lref j1
                         ).
 intros. inversion H; clear H; intros; subst; auto depth = 5.
qed.

theorem lift_inv_bind_2: \forall l, i, r, x, u2, t2.
                         Lift l i x (intb r u2 t2) \to
                         \exists u1, t1. 
                         Lift l i u1 u2 \land
                         Lift l (succ i) t1 t2 \land
                         x = intb r u1 t1.
 intros. inversion H; clear H; intros; subst. auto depth = 5.
qed.

theorem lift_inv_flat_2: \forall l, i, r, x, u2, t2.
                         Lift l i x (intf r u2 t2) \to
                         \exists u1, t1. 
                         Lift l i u1 u2 \land
                         Lift l i t1 t2 \land
                         x = intf r u1 t1.
 intros. inversion H; clear H; intros; subst. auto depth = 5.
qed.

(* Corollaries of inversion properties ***************************************)

theorem lift_inv_lref_1_gt: \forall l, i, j1, x.
                            Lift l i (lref j1) x \to
                            i > j1 \to x = lref j1.
 intros.
 lapply linear lift_inv_lref_1 to H. decompose; subst;
 [ auto
 | lapply linear nle_false to H2, H1. decompose
 ].
qed.

theorem lift_inv_lref_1_le: \forall l, i, j1, x.
                            Lift l i (lref j1) x \to i <= j1 \to 
                            \exists j2. (l + j1 == j2) \land x = lref j2.
 intros.
 lapply linear lift_inv_lref_1 to H. decompose; subst;
 [ lapply linear nle_false to H1, H2. decompose
 | auto
 ].
qed.

theorem lift_inv_lref_1_le_nplus: \forall l, i, j1, x.
                                 Lift l i (lref j1) x \to
                                 i <= j1 \to \forall j2. (l + j1 == j2) \to
                                 x = lref j2.
 intros.
 lapply linear lift_inv_lref_1 to H. decompose; subst;
 [ lapply linear nle_false to H1, H3. decompose
 | lapply linear nplus_mono to H2, H4. subst. auto
 ].
qed.

theorem lift_inv_lref_2_gt: \forall l, i, x, j2.
                            Lift l i x (lref j2) \to
                            i > j2 \to x = lref j2.
 intros.
 lapply linear lift_inv_lref_2 to H. decompose; subst;
 [ auto
 | lapply linear nle_false to H2, H1. decompose
 ].
 qed.

theorem lift_inv_lref_2_le: \forall l, i, x, j2.
                            Lift l i x (lref j2) \to i <= j2 \to 
                            \exists j1. (l + j1 == j2) \land x = lref j1.
 intros.
 lapply linear lift_inv_lref_2 to H. decompose; subst;
 [ lapply linear nle_false to H1, H2. decompose
 | auto
 ].
qed.

theorem lift_inv_lref_2_le_nplus: \forall l, i, x, j2.
                                  Lift l i x (lref j2) \to
                                  i <= j2 \to \forall j1. (l + j1 == j2) \to
                                  x = lref j1.
 intros.
 lapply linear lift_inv_lref_2 to H. decompose; subst;
 [ lapply linear nle_false to H1, H3. decompose
 | lapply linear nplus_inj_2 to H2, H4. subst. auto
 ].
qed.
