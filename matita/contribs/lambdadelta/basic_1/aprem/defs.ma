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

include "Basic-1/A/defs.ma".

inductive aprem: nat \to (A \to (A \to Prop)) \def
| aprem_zero: \forall (a1: A).(\forall (a2: A).(aprem O (AHead a1 a2) a1))
| aprem_succ: \forall (a2: A).(\forall (a: A).(\forall (i: nat).((aprem i a2 
a) \to (\forall (a1: A).(aprem (S i) (AHead a1 a2) a))))).

