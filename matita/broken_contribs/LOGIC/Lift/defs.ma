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



(* PROOF RELOCATION
*)

include "datatypes_defs/Proof.ma".

inductive Lift: Nat \to Nat \to Proof \to Proof \to Prop \def
   | lift_lref_lt: \forall jd,jh,i. i < jd \to Lift jd jh (lref i) (lref i)
   | lift_lref_ge: \forall jd,jh,i1,i2. jd <= i1 \to (i1 + jh == i2) \to 
                   Lift jd jh (lref i1) (lref i2)
   | lift_prin   : \forall jd,jh,h. Lift jd jh (prin h) (prin h)
   | lift_impw   : \forall jd,jh,p1,p2. 
                   Lift jd jh p1 p2 \to Lift jd jh (impw p1) (impw p2)
   | lift_impr   : \forall jd,jh,p1,p2. 
                   Lift jd jh p1 p2 \to Lift jd jh (impr p1) (impr p2)
   | lift_impi   : \forall jd,jh,p1,p2. Lift jd jh p1 p2 \to 
                   \forall q1,q2. Lift jd jh q1 q2 \to
                   \forall r1,r2. Lift (succ jd) jh r1 r2 \to 
                   Lift jd jh (impi p1 q1 r1) (impi p2 q2 r2)
   | lift_scut   : \forall jd,jh,p1,p2. Lift jd jh p1 p2 \to 
                   \forall q1,q2. Lift jd jh q1 q2 \to
                   Lift jd jh (scut p1 q1) (scut p2 q2)
.
