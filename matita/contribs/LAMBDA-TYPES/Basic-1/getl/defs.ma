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

include "Basic-1/drop/defs.ma".

include "Basic-1/clear/defs.ma".

inductive getl (h: nat) (c1: C) (c2: C): Prop \def
| getl_intro: \forall (e: C).((drop h O c1 e) \to ((clear e c2) \to (getl h 
c1 c2))).

