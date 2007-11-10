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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Unified-Sub/Lift/fun".

include "Lift/inv.ma".

(* Functional properties ****************************************************)

theorem lift_total: \forall l, t, i. \exists u. Lift l i t u.
 intros 2. elim t; clear t;
 [ autobatch
 | lapply (nle_gt_or_le n i). decompose;
   [ autobatch
   | lapply (nplus_total l n). decompose. autobatch
   ]
 | lapply (H i1). lapply (H1 (succ i1)). decompose. autobatch
 | lapply (H i1). lapply (H1 i1). decompose. autobatch  
 ].
qed.

theorem lift_mono: \forall l,i,t,t1. Lift l i t t1 \to
                   \forall t2. Lift l i t t2 \to
                   t1 = t2.
 intros 5. elim H; clear H i t t1;
 [ lapply linear lift_inv_sort_1 to H1
 | lapply linear lift_inv_lref_1_gt to H2, H1
 | lapply linear lift_inv_lref_1_le_nplus to H3, H1, H2
 | lapply linear lift_inv_bind_1 to H5. decompose
 | lapply linear lift_inv_flat_1 to H5. decompose
 ]; destruct; autobatch.
qed.

theorem lift_inj: \forall l,i,t1,t. Lift l i t1 t \to
                  \forall t2. Lift l i t2 t \to
                  t2 = t1.
 intros 5. elim H; clear H i t1 t;
 [ lapply linear lift_inv_sort_2 to H1
 | lapply linear lift_inv_lref_2_gt to H2, H1
 | lapply nle_nplus to H2 as H.
   lapply linear nle_trans to H1, H as H0.
   lapply lift_inv_lref_2_le_nplus to H3, H0, H2
 | lapply linear lift_inv_bind_2 to H5. decompose
 | lapply linear lift_inv_flat_2 to H5. decompose
 ]; destruct; autobatch.
qed.
