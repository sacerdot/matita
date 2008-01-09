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



include "Insert/props.ma".
include "Track/defs.ma".
include "NTrack/inv.ma".
(*
theorem ntrack_weak: \forall R,p,P,Q,S,i. 
                     NTrack P p S \to Insert R i P Q \to 
                     \exists q. NTrack Q q S.
 intros 2; elim p; clear p;
 [ lapply linear ntrack_inv_lref to H as H0; decompose;
   lapply linear insert_trans to H, H1; decompose; autobatch
 | lapply linear ntrack_inv_parx to H; destruct; autobatch
 | lapply linear ntrack_inv_impw to H1; decompose; destruct;
   lapply linear H to H4, H2; decompose; autobatch
 | lapply linear ntrack_inv_impr to H1; decompose; destruct;
   lapply linear H to H4, H2; decompose; autobatch
 | lapply linear ntrack_inv_impi to H3; decompose; destruct;
   lapply insert_conf to H4, H6; clear H6; decompose;
   lapply H to H9, H4; clear H H9; lapply linear H1 to H8, H4;
   lapply linear H2 to H7, H6; decompose; autobatch width = 4
 | lapply linear ntrack_inv_scut to H2; decompose
 ]
qed.

theorem ntrack_comp: \forall R,q,p,P,Q,S,i. 
                     NTrack P p R \to NTrack Q q S \to Insert R i P Q \to
                     \exists r. NTrack P r S.
 intros 2; elim q; clear q;
 [ lapply linear ntrack_inv_lref to H1 as H0; decompose;
   lapply linear insert_conf_rev_full to H1,H2; decompose; destruct; autobatch
 | lapply linear ntrack_inv_parx to H1; destruct; autobatch
 | lapply linear ntrack_inv_impw to H2; decompose; destruct;
   lapply linear H to H1, H5, H3; decompose; autobatch
 | lapply linear ntrack_inv_impr to H2; decompose; destruct;
   lapply linear H to H1, H5, H3; decompose; autobatch
 | lapply linear ntrack_inv_impi to H4; decompose; destruct;
   lapply insert_trans to H5, H7; clear H7; decompose;
   lapply ntrack_weak to H3, H6; decompose;
   lapply H to H3, H10, H5; clear H H10; lapply linear H1 to H3, H9, H5;
   lapply linear H2 to H4, H8, H7; decompose; autobatch width = 4
 | lapply linear ntrack_inv_scut to H3; decompose
 ].
qed.

theorem ntrack_track: \forall R,p,P. NTrack P p R \to Track P p R.
 intros; elim H names 0; clear H P p R; intros; autobatch width = 4.
qed.
*)
