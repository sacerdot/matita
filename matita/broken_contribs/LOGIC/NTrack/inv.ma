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



include "NTrack/defs.ma".
(*
theorem ntrack_inv_lref: \forall Q,S,i. NTrack Q (lref i) S \to
                         \exists P. Insert S i P Q.
 intros; inversion H; clear H; intros; destruct; autobatch.
qed.

theorem ntrack_inv_parx: \forall P,S,h. NTrack P (parx h) S \to
                         S = pair (posr h) (posr h).
 intros; inversion H; clear H; intros; destruct; autobatch.
qed.

theorem ntrack_inv_impw: \forall P,p,S. NTrack P (impw p) S \to
                         \exists B,a,b. 
                         S = pair (impl a b) B \land 
                         NTrack P p (pair lleaf B).
 intros; inversion H; clear H; intros; destruct; autobatch depth = 5.
qed.

theorem ntrack_inv_impr: \forall P,p,S. NTrack P (impr p) S \to
                         \exists a,b:Formula. 
                         S = pair lleaf (impl a b) \land
                         NTrack P p (pair a b).
 intros; inversion H; clear H; intros; destruct; autobatch depth = 4.
qed.

theorem ntrack_inv_impi: \forall P,p,q,r,S. NTrack P (impi p q r) S \to
                         \exists Q,A,B,D,i. \exists a,b:Formula.
                         S = pair (impl a b) D \land
                         NTrack P p (pair A a) \land
                         NTrack P q (pair b B) \land
                         NTrack Q r (pair lleaf D) \land
                         Insert (pair A B) i P Q.
 intros; inversion H; clear H; intros; destruct; autobatch depth = 12 width = 5 size = 16.
qed.

theorem ntrack_inv_scut: \forall P,q,r,S. NTrack P (scut q r) S \to False.
 intros; inversion H; clear H; intros; destruct.
qed.

theorem ntrack_inv_lleaf_impl: 
   \forall Q,p,a,b. NTrack Q p (pair lleaf (impl a b)) \to
   (\exists P,i. p = lref i \land Insert (pair lleaf (impl a b)) i P Q) \lor
   (\exists r. p = impr r \land NTrack Q r (pair a b)).
 intros; inversion H; clear H; intros; destruct;
 [ autobatch depth = 5
 | destruct; autobatch depth = 4
 ].
qed.
*)
