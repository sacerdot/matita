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

include "Basic-1/C/defs.ma".

include "Basic-1/lift/defs.ma".

include "Basic-1/r/defs.ma".

inductive drop: nat \to (nat \to (C \to (C \to Prop))) \def
| drop_refl: \forall (c: C).(drop O O c c)
| drop_drop: \forall (k: K).(\forall (h: nat).(\forall (c: C).(\forall (e: 
C).((drop (r k h) O c e) \to (\forall (u: T).(drop (S h) O (CHead c k u) 
e))))))
| drop_skip: \forall (k: K).(\forall (h: nat).(\forall (d: nat).(\forall (c: 
C).(\forall (e: C).((drop h (r k d) c e) \to (\forall (u: T).(drop h (S d) 
(CHead c k (lift h (r k d) u)) (CHead e k u)))))))).

