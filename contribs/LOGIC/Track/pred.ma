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



(**)

include "datatypes_props/Sequent.ma".
include "Track/inv.ma".
include "PRed/defs.ma".

theorem track_pred: \forall Q1,Q2,p1,p2,S1,S2. [Q1, p1, S1] => [Q2, p2, S2] \to
                    Track Q1 p1 S1 \to Track Q2 p2 S2.
 intros 7; elim H; clear H Q1 Q2 p1 p2 S1 S2;
 [ autobatch
 | autobatch
 | lapply linear track_inv_impw to H3; decompose; destruct; autobatch
 | lapply linear track_inv_impr to H3; decompose; destruct; autobatch
 | lapply linear track_inv_impi to H7; decompose; destruct; autobatch size = 7
 | lapply linear track_inv_scut to H5; decompose; destruct; autobatch
 | lapply linear track_inv_scut to H4; decompose; destruct;
   lapply linear track_inv_lref to H6; decompose; autobatch
 | lapply linear track_inv_scut to H4; decompose; destruct;
   lapply linear track_inv_lref to H5; decompose; autobatch
 | lapply linear track_inv_scut to H3; decompose; destruct;
   lapply linear track_inv_prin to H5; destruct;
   lapply linear rinj_inj to Hcut1; destruct; autobatch
 | lapply linear track_inv_scut to H3; decompose; destruct;
   lapply linear track_inv_prin to H4; destruct; 
   lapply linear linj_inj to Hcut; destruct; autobatch
 | lapply linear track_inv_scut to H3; decompose; destruct;
   lapply linear track_inv_impw to H4; decompose; destruct;
   lapply linear track_inv_impr to H5; decompose; destruct; autobatch
 ].
qed.
