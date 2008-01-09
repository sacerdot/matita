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



include "Track/defs.ma".

(* Main inversion lemmas ****************************************************)

theorem track_inv_lref: \forall Q,S,i. Track Q (lref i) S \to
                        \exists p1,p2,P. Insert p1 p2 S i P Q.
 intros; inversion H; clear H; intros; destruct; autobatch depth = 4.
qed.

theorem track_inv_prin: \forall P,S,h. Track P (prin h) S \to
                        S = pair (posr h) (posr h).
 intros; inversion H; clear H; intros; destruct; autobatch.
qed.

theorem track_inv_impw: \forall P,p,S. Track P (impw p) S \to
                        \exists B,a,b. 
                        S = pair (impl a b) B \land 
                        Track P p (pair lleaf B).
 intros; inversion H; clear H; intros; destruct; autobatch depth = 5.
qed.

theorem track_inv_impr: \forall Q,p,S. Track Q (impr p) S \to
                        \exists a,b:Formula. 
                        S = pair lleaf (impl a b) \land
                        Track Q p (pair a b).
 intros; inversion H; clear H; intros; destruct; autobatch depth = 4.
qed.

theorem track_inv_impi: \forall P,p,q,r,S. Track P (impi p q r) S \to
                        \exists A,B,D. \exists a,b:Formula.
                        S = pair (impl a b) D \land
                        Track P p (pair A a) \land
                        Track P q (pair b B) \land
                        Track (abst P p q (pair A B)) r (pair lleaf D).
 intros; inversion H; clear H; intros; destruct; autobatch depth = 9 width = 4 size = 12.
qed.

theorem track_inv_scut: \forall P,q,r,S. Track P (scut q r) S \to
                        \exists A,B. \exists c:Formula.
                        S = pair A B \land
                        Track P q (pair A c) \land
                        Track P r (pair c B).
 intros; inversion H; clear H; intros; destruct; autobatch depth = 6 size = 8. 
qed.
