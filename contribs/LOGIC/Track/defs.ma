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
   | track_impi: \forall P,r. \forall a,b:Formula. 
                 Track P r (pair a b) \to 
                 Track P (impi r) (pair lleaf (impl a b))
   | track_impe: \forall P,Q,r,D,i. \forall a,b:Formula.
                 Track Q r (pair lleaf D) \to
                 Insert (pair a b) i P Q \to
                 Track P (impe r) (pair (impl a b) D) 
(*   
   | track_impe: \forall P,p,q,r,A,B,D,a,b.
                 Track P p (pair A (rinj a)) \to
                 Track P q (pair (linj b) B) \to
		 Track (abst P (pair A B)) r (pair lleaf D) \to
		 Track P (impe p q r) (pair (linj (impl a b)) D)
*)
.
