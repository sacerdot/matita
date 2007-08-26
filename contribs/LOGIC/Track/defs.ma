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

set "baseuri" "cic:/matita/LOGIC/Track/defs".

(* PROOF TREE TRACKS
*)

include "datatypes/Proof.ma".
include "Insert/defs.ma".

inductive Track: Context \to Proof \to Sequent \to Prop \def
   | track_proj: \forall P,Q,S,i. Insert S i P Q \to Track Q (lref i) S
   | track_posr: \forall P,h.
                 Track P (parx h) (pair (posr h) (posr h))
   | track_impw: \forall P,r,D,a,b. Track P r (pair lleaf D) \to
                 Track P (impw r) (pair (impl a b) D)
   | track_impr: \forall P,r. \forall a,b:Formula. 
                 Track P r (pair a b) \to 
                 Track P (impr r) (pair lleaf (impl a b))
   | track_impi: \forall P,Q,p,q,r,A,B,D,i. \forall a,b:Formula.
                 Track P p (pair A a) \to
                 Track P q (pair b B) \to
		 Track Q r (pair lleaf D) \to
		 Insert (pair A B) i P Q \to
		 Track P (impi p q r) (pair (impl a b) D)
.
