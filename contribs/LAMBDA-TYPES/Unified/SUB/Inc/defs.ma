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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Unified-Sub/Inc/defs".

(* DISPLACEMENT INCREMENT RELATION
*)

include "SUB/Term/defs.ma".

inductive Inc (i:Nat): Bool \to Head \to Nat \to Prop \def
   | inc_bind: \forall r. Inc i true (bind r) (succ i)
   | inc_skip: \forall r. Inc i false (bind r) i
   | inc_flat: \forall r,q. Inc i q (flat r) i   
.
