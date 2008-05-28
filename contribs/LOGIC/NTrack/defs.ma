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



(* NORMAL PROOF TREE TRACKS
*)

include "Insert/defs.ma".
(*
inductive NTrack: Context \to Proof \to Sequent \to Prop \def
   | ntrack_proj: \forall P,Q,S,i. Insert S i P Q \to NTrack Q (lref i) S
   | ntrack_posr: \forall P,h.
                  NTrack P (parx h) (pair (posr h) (posr h))
   | ntrack_impw: \forall P,r,D,a,b. NTrack P r (pair lleaf D) \to
                  NTrack P (impw r) (pair (impl a b) D)
   | ntrack_impr: \forall P,r. \forall a,b:Formula. 
                  NTrack P r (pair a b) \to 
                  NTrack P (impr r) (pair lleaf (impl a b))
   | ntrack_impi: \forall P,Q,p,q,r,A,B,D,i. \forall a,b:Formula.
                  NTrack P p (pair A a) \to
                  NTrack P q (pair b B) \to
		  NTrack Q r (pair lleaf D) \to
		  Insert (pair A B) i P Q \to
		  NTrack P (impi p q r) (pair (impl a b) D)
.
*)
