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

include "Basic-1/getl/defs.ma".

definition cimp:
 C \to (C \to Prop)
\def
 \lambda (c1: C).(\lambda (c2: C).(\forall (b: B).(\forall (d1: C).(\forall 
(w: T).(\forall (h: nat).((getl h c1 (CHead d1 (Bind b) w)) \to (ex C 
(\lambda (d2: C).(getl h c2 (CHead d2 (Bind b) w)))))))))).

