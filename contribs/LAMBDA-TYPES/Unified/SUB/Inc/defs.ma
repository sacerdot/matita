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

inductive Inc (q:Bool) (i:Nat): Head \to Nat \to Prop \def
   | inc_bind: \forall r. Inc q i (bind q r) (succ i)
   | inc_skip: \forall p. (q = p \to False) \to
               \forall r. Inc q i (bind p r) i
   | inc_flat: \forall p,r. Inc q i (flat p r) i   
.
