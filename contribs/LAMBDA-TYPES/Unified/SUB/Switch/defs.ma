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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Unified/SUB/Switch/defs".

(* POLARITY SWITCH RELATION
*)

include "SUB/Term/defs.ma".

inductive Switch (q1:Bool): Head \to Bool \to Prop \def
   | switch_bind: \forall q2,p. (p -- q1 == q2) \to
                  \forall r. Switch q1 (bind p r) q2 
   | switch_flat: \forall q2,p. (p -- q1 == q2) \to
                  \forall r. Switch q1 (flat p r) q2 
.
