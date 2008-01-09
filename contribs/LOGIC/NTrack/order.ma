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



include "Track/order.ma".
include "NTrack/props.ma".

(* Order properties *********************************************************)
(*
theorem ntrack_refl: \forall P. \forall c:Formula. \exists r. 
                     NTrack P r (pair c c).
 intros; elim c; clear c;
 [ autobatch
 | lapply (insert_total (pair f f1) zero P); [2:autobatch];
   decompose; autobatch depth = 5 width = 4 size = 8
 ].
qed.
(*
theorem ntrack_trans: \forall p,q,A,B. \forall c:Formula.
                      NTrack leaf p (pair A c) \to NTrack leaf q (pair c B) \to
                      \exists r. NTrack leaf r (pair A B).
 intros;
 lapply linear ntrack_track to H as H0;
 lapply linear ntrack_track to H1 as H;
 lapply linear track_trans to H0, H as H1; decompose;
*)
*)
