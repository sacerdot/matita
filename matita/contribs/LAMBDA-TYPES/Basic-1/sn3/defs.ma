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

include "Basic-1/pr3/defs.ma".

inductive sn3 (c: C): T \to Prop \def
| sn3_sing: \forall (t1: T).(((\forall (t2: T).((((eq T t1 t2) \to (\forall 
(P: Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c t2))))) \to (sn3 c t1)).

definition sns3:
 C \to (TList \to Prop)
\def
 let rec sns3 (c: C) (ts: TList) on ts: Prop \def (match ts with [TNil 
\Rightarrow True | (TCons t ts0) \Rightarrow (land (sn3 c t) (sns3 c ts0))]) 
in sns3.

