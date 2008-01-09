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



(* PROOF WEIGHT
   For cut elimination and confluence
*)

include "datatypes_defs/Context.ma".


inductive Weight: Nat \to Context \to Proof \to Nat \to Prop \def
   | weight_prin: \forall Q,n,m. Weight m Q (prin n) m
   | weight_impw: \forall p,Q,m0,m1. Weight m0 Q p m1 \to
                  \forall m. (m1 + m0 == m) \to
                  Weight m0 Q (impw p) m
   | weight_impr: \forall p,Q,m0,m1. Weight m0 Q p m1 \to
                  \forall m. (m1 + m0 == m) \to
                  Weight m0 Q (impr p) m
   | weight_scut: \forall p1,Q,m0,m1. Weight (succ m0) Q p1 m1 \to
                  \forall p2,m2. Weight (succ m0) Q p2 m2 \to
                  \forall m. (m1 + m2 == m) \to
                  Weight m0 Q (scut p1 p2) m
.
