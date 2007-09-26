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

set "baseuri" "cic:/matita/LOGIC/Track/pred".

(**)

include "Track/inv.ma".
include "PRed/defs.ma".

theorem track_pred: \forall Q1,Q2,p1,p2,S1,S2. PRed Q1 p1 S1 Q2 p2 S2 \to
                    Track Q1 p1 S1 \to Track Q2 p2 S2.
 intros 7; elim H; clear H Q1 Q2 p1 p2 S1 S2;
 [ autobatch
 | autobatch
 | lapply linear track_inv_impw to H3; decompose; subst; autobatch
 | lapply linear track_inv_impr to H3; decompose; subst; autobatch
 | lapply linear track_inv_impi to H7; decompose; subst; autobatch size = 7
 | lapply linear track_inv_scut to H5; decompose; subst; autobatch
 | lapply linear track_inv_scut to H4; decompose; subst;
   lapply linear track_inv_lref to H6; decompose; autobatch
 | lapply linear track_inv_scut to H4; decompose; subst;
   lapply linear track_inv_lref to H5; decompose; autobatch
 | lapply linear track_inv_scut to H3; decompose; subst;
   lapply linear track_inv_prin to H5; subst; autobatch
 | lapply linear track_inv_scut to H3; decompose; subst;
   lapply linear track_inv_prin to H4; subst; autobatch
 | lapply linear track_inv_scut to H3; decompose; subst;
   lapply linear track_inv_impw to H4; decompose; subst;
   lapply linear track_inv_impr to H5; decompose; subst; autobatch
 ].
qed.
