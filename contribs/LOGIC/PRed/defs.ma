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



(* SINGLE STEP PARALLEL REDUCTION
   For cut elimination 
*)

include "Insert/defs.ma".
 
inductive PRed: Context \to Proof \to Sequent \to 
                Context \to Proof \to Sequent \to Prop \def
   | pred_lref: \forall P,i,S. PRed P (lref i) S P (lref i) S
   | pred_prin: \forall P,h,S. PRed P (prin h) S P (prin h) S
   | pred_impw: \forall Q1,Q2,p1,p2. (\forall S. PRed Q1 p1 S Q2 p2 S) \to 
                \forall S. PRed Q1 (impw p1) S Q2 (impw p2) S
   | pred_impr: \forall Q1,Q2,p1,p2. (\forall S. PRed Q1 p1 S Q2 p2 S) \to
                \forall S. PRed Q1 (impr p1) S Q2 (impr p2) S
   | pred_impi: \forall Q1,Q2,p1,p2. (\forall S. PRed Q1 p1 S Q2 p2 S) \to
                \forall q1,q2. (\forall S. PRed Q1 q1 S Q2 q2 S) \to
                \forall r1,r2. (\forall S,R. PRed (abst Q1 p1 q1 R) r1 S (abst Q2 p2 q2 R) r2 S) \to 
                \forall S. PRed Q1 (impi p1 q1 r1) S Q2 (impi p2 q2 r2) S
   | pred_scut: \forall Q1,Q2,p1,p2. (\forall S. PRed Q1 p1 S Q2 p2 S) \to 
                \forall q1,q2. (\forall S. PRed Q1 q1 S Q2 q2 S) \to
                \forall S. PRed Q1 (scut p1 q1) S Q2 (scut p2 q2) S
   | pred_a_sx: \forall p1,p2,R,P,Q1,i. Insert p1 p2 R i P Q1 \to
                \forall q0,S,Q2. Insert p1 (scut p2 q0) S i P Q2 \to
                \forall q. Lift zero i q0 q \to
		PRed Q1 (scut (lref i) q) S Q2 (lref i) S
   | pred_a_dx: \forall q1,q2,R,P,Q1,i. Insert q1 q2 R i P Q1 \to
                \forall p0,S,Q2. Insert (scut p0 q1) q2 S i P Q2 \to
                \forall p. Lift zero i p0 p \to
		PRed Q1 (scut p (lref i)) S Q2 (lref i) S
   | pred_b_sx: \forall q1,q2,P1,P2,S. PRed P1 q1 S P2 q2 S \to 
                \forall h. PRed P1 (scut (prin h) q1) S P2 q2 S
   | pred_b_dx: \forall p1,p2,Q1,Q2,S. PRed Q1 p1 S Q2 p2 S \to
                \forall h. PRed Q1 (scut p1 (prin h)) S Q2 p2 S
   | pred_c   : \forall p1,p2,Q1,Q2,S. PRed Q1 p1 S Q2 p2 S \to 
                \forall p. PRed Q1 (scut (impr p) (impw p1)) S Q2 p2 S    
.

(*CSC: the URI must disappear: there is a bug now *)
interpretation 
   "single step parallel reduction in B->"
   'parred3 x1 y1 z1 x2 y2 z2 = 
      (cic:/matita/LOGIC/PRed/defs/PRed.ind#xpointer(1/1) x1 y1 z1 x2 y2 z2)
.

notation "hvbox([a1,b1,c1] break => [a2,b2,c2])" 
  non associative with precedence 45
for @{ 'parred3 $a1 $b1 $c1 $a2 $b2 $c2 }.
