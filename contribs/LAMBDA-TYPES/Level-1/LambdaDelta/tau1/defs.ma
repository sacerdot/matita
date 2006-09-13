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

(* This file was automatically generated: do not edit *********************)

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/tau1/defs".

include "tau0/defs.ma".

inductive tau1 (g:G) (c:C) (t1:T): T \to Prop \def
| tau1_tau0: \forall (t2: T).((tau0 g c t1 t2) \to (tau1 g c t1 t2))
| tau1_sing: \forall (t: T).((tau1 g c t1 t) \to (\forall (t2: T).((tau0 g c 
t t2) \to (tau1 g c t1 t2)))).

