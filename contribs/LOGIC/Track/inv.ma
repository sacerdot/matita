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

set "baseuri" "cic:/matita/LOGIC/Track/inv".

include "Track/defs.ma".

theorem track_inv_lref: \forall Q,S,i. Track Q (lref i) S \to
                        \exists P. Insert S i P Q.
 intros. inversion H; clear H; intros; subst. autobatch.
qed.     

theorem track_inv_parx: \forall P,S,h. Track P (parx h) S \to
                        S = pair (posr h) (posr h).
 intros. inversion H; clear H; intros; subst. autobatch.
qed.

theorem track_inv_impw: \forall P,p,S. Track P (impw p) S \to
                        \exists B,a,b. 
                        S = pair (impl a b) B \land 
                        Track P p (pair lleaf B).
 intros. inversion H; clear H; intros; subst. autobatch depth = 5.
qed.

theorem track_inv_impi: \forall P,p,S. Track P (impi p) S \to
                        \exists a,b:Formula. 
                        S = pair lleaf (impl a b) \land
                        Track P p (pair a b).
 intros. inversion H; clear H; intros; subst. autobatch depth = 4.
qed.

theorem track_inv_impe: \forall P,r,S. Track P (impe r) S \to
                        \exists Q,D,i. \exists a,b:Formula.
                        S = pair (impl a b) D \land
                        Track Q r (pair lleaf D) \land
                        Insert (pair a b) i P Q.
 intros. inversion H; clear H; intros; subst. autobatch depth = 8 size = 10.
qed.

theorem track_inv_lleaf_impl: 
   \forall Q,p,a,b. Track Q p (pair lleaf (impl a b)) \to
   (\exists P,i. p = lref i \land Insert (pair lleaf (impl a b)) i P Q) \lor
   (\exists r. p = impi r \land Track Q r (pair a b)).
 intros. inversion H; clear H; intros; subst;
 [ autobatch depth = 5
 | subst. autobatch depth = 4
 ].
qed.
(*
theorem track_inv_impe: \forall P,p,q,r,S. Track P (impe p q r) S \to
                        \exists A,B,D. \exists a,b:Formula.
                        S = pair (impl a b) D \land
                        Track P p (pair A a) \land
                        Track P q (pair b B) \land
                        Track (abst P (pair A B)) r (pair lleaf D).
 intros. inversion H; clear H; intros; subst;
 [ destruct H2
 | destruct H1
 | destruct H3
 | destruct H3
 | destruct H7. clear H7. subst. autobatch depth = 9
 ].
qed.
*)
