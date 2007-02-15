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

include "Lift/inv.ma".

theorem lift_conf: \forall l,i,t,x. Lift l i t x \to
                   \forall y. Lift l i t y \to
                   x = y.
 intros 5. elim H; clear H i t x;
 [ lapply linear lift_inv_sort_1 to H1.
   subst. auto
 | lapply linear lift_inv_lref_1 to H2.
   decompose; subst;
   [ auto | lapply nle_false to H2, H1. decompose ]
 | lapply linear lift_inv_lref_1 to H3.
   decompose; subst;
   [ lapply linear nle_false to H1, H3. decompose
   | lapply linear nplus_conf to H2, H4. subst. auto
   ]
 | lapply linear lift_inv_bind_1 to H5.
   decompose. subst. auto.
 | lapply linear lift_inv_flat_1 to H5.
   decompose. subst. auto.
 ].
qed.

theorem lift_comp_le: \forall l1,i1,t,y. (Lift l1 i1 t y) \to
                      \forall l2,i2,x. (Lift l2 i2 t x) \to
                      \forall z. (Lift l2 i2 y z) \to
                      i2 <= i1 \to \forall i. (l2 + i1 == i) \to
                      (Lift l1 i x z).
 intros 5. elim H; clear H i1 t y;
 [ lapply lift_conf to H1, H2. clear H2. subst.
   lapply linear lift_inv_sort_1 to H1.
   subst. auto
 | lapply lift_conf to H2, H3. clear H3. subst.
   lapply linear lift_inv_lref_1 to H2.
   decompose; subst; clear H2 H4 i2;
   [ lapply linear nle_nplus to H5 as H0. clear l2. (**)
     lapply linear nle_trans to H1, H0.
     auto
   | lapply nle_nplus_comp_lt_2 to H3, H5; auto.
   ]
 | lapply linear lift_inv_lref_1 to H3.
   decompose; subst;
   [ clear H2 H4 H6 n3 l2.
     lapply linear nle_trans to H3, H5 as H0.
     lapply linear nle_false to H1, H0. decompose
   | lapply linear lift_inv_lref_1 to H4.
     decompose; subst;
     [ clear H1 H5 H6 H7 n1.
       lapply linear nle_nplus to H2 as H0. (**)
       lapply linear nle_trans to H3, H0 as H2.
       lapply linear nle_false to H2, H4. decompose
     | clear H3 H4 H5.
       lapply nle_nplus_comp to H6, H7; auto.
     ]
   ]
 |