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

include "Basic-1/pr0/defs.ma".

include "Basic-1/getl/defs.ma".

inductive pr2: C \to (T \to (T \to Prop)) \def
| pr2_free: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to 
(pr2 c t1 t2))))
| pr2_delta: \forall (c: C).(\forall (d: C).(\forall (u: T).(\forall (i: 
nat).((getl i c (CHead d (Bind Abbr) u)) \to (\forall (t1: T).(\forall (t2: 
T).((pr0 t1 t2) \to (\forall (t: T).((subst0 i u t2 t) \to (pr2 c t1 
t)))))))))).

