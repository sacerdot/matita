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

inductive clear: C \to (C \to Prop) \def
| clear_bind: \forall (b: B).(\forall (e: C).(\forall (u: T).(clear (CHead e 
(Bind b) u) (CHead e (Bind b) u))))
| clear_flat: \forall (e: C).(\forall (c: C).((clear e c) \to (\forall (f: 
F).(\forall (u: T).(clear (CHead e (Flat f) u) c))))).

