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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Unified/Inc/defs".

(* DISPLACEMENT INCREMENT RELATION
*)

include "logic/equality.ma".

include "P/defs.ma".

inductive Inc (i:Nat): Bool \to Head \to Nat \to Prop \def
   | inc_bind: \forall x. Inc i true (bind x) (succ i)
   | inc_flat: \forall y. Inc i true (flat y) i   
   | inc_neg : \forall z. Inc i false z i
.
