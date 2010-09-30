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

include "Basic-1/T/defs.ma".

inductive cnt: T \to Prop \def
| cnt_sort: \forall (n: nat).(cnt (TSort n))
| cnt_head: \forall (t: T).((cnt t) \to (\forall (k: K).(\forall (v: T).(cnt 
(THead k v t))))).

