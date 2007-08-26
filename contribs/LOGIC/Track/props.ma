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

set "baseuri" "cic:/matita/LOGIC/Track/props".

include "Insert/props.ma".
include "Track/inv.ma".

theorem track_weak: \forall R,p,P,Q,S,i. 
                    Track P p S \to Insert R i P Q \to 
                    \exists q. Track Q q S.
 intros 2; elim p; clear p;
 [ lapply linear track_inv_lref to H as H0; decompose;
   lapply linear insert_trans to H, H1; decompose; autobatch
 | lapply linear track_inv_parx to H; subst; autobatch
 | lapply linear track_inv_impw to H1; decompose; subst;
   lapply linear H to H4, H2; decompose; autobatch
 | lapply linear track_inv_impr to H1; decompose; subst;
   lapply linear H to H4, H2; decompose; autobatch
 | lapply linear track_inv_impi to H3; decompose; subst;
   lapply insert_conf to H4, H6; clear H6; decompose;
   lapply H to H9, H4; clear H H9; lapply linear H1 to H8, H4;
   lapply linear H2 to H7, H6; decompose; autobatch width = 4
 | lapply linear track_inv_scut to H2; decompose
 ]
qed.

theorem track_comp: \forall R,q,p,P,Q,S,i. 
                    Track P p R \to Track Q q S \to Insert R i P Q \to
                    \exists r. Track P r S.
 intros 2; elim q; clear q;
 [ lapply linear track_inv_lref to H1 as H0; decompose;
   lapply linear insert_conf_rev_full to H1,H2; decompose; subst; autobatch
 | lapply linear track_inv_parx to H1; subst; autobatch
 | lapply linear track_inv_impw to H2; decompose; subst;
   lapply linear H to H1, H5, H3; decompose; autobatch
 | lapply linear track_inv_impr to H2; decompose; subst;
   lapply linear H to H1, H5, H3; decompose; autobatch
 | lapply linear track_inv_impi to H4; decompose; subst;
   lapply insert_trans to H5, H7; clear H7; decompose;
   lapply track_weak to H3, H6; decompose;
   lapply H to H3, H10, H5; clear H H10; lapply linear H1 to H3, H9, H5;
   lapply linear H2 to H4, H8, H7; decompose; autobatch width = 4
 | lapply linear track_inv_scut to H3; decompose
 ].
qed.
