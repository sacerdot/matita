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

set "baseuri" "cic:/matita/LOGIC/PRed/defs".

(* SINGLE STEP PARALLEL REDUCTION
   For cut elimination 
*)

include "datatypes/Proof.ma".

inductive PRed: Proof \to Proof \to Prop \def
   | pred_lref: \forall i. PRed (lref i) (lref i)
   | pred_parx: \forall h. PRed (parx h) (parx h)
   | pred_impw: \forall p1,p2. PRed p1 p2 \to PRed (impw p1) (impw p2)
   | pred_impr: \forall p1,p2. PRed p1 p2 \to PRed (impr p1) (impr p2)
   | pred_impi: \forall p1,p2. PRed p1 p2 \to \forall q1,q2. PRed q1 q2 \to
                \forall r1,r2. PRed r1 r2 \to 
		PRed (impi p1 q1 r1) (impi p2 q2 r2)
   | pred_scut: \forall p1,p2. PRed p1 p2 \to \forall q1,q2. PRed q1 q2 \to
                PRed (scut p1 q1) (scut p2 q2)
.

(*CSC: the URI must disappear: there is a bug now *)
interpretation 
   "single step parallel reduction in B->"
   'parred x y = (cic:/matita/LOGIC/PRed/defs/PRed.ind#xpointer(1/1) x y)
.
