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

include "Basic-1/ty3/defs.ma".

inductive wf3 (g: G): C \to (C \to Prop) \def
| wf3_sort: \forall (m: nat).(wf3 g (CSort m) (CSort m))
| wf3_bind: \forall (c1: C).(\forall (c2: C).((wf3 g c1 c2) \to (\forall (u: 
T).(\forall (t: T).((ty3 g c1 u t) \to (\forall (b: B).(wf3 g (CHead c1 (Bind 
b) u) (CHead c2 (Bind b) u))))))))
| wf3_void: \forall (c1: C).(\forall (c2: C).((wf3 g c1 c2) \to (\forall (u: 
T).(((\forall (t: T).((ty3 g c1 u t) \to False))) \to (\forall (b: B).(wf3 g 
(CHead c1 (Bind b) u) (CHead c2 (Bind Void) (TSort O))))))))
| wf3_flat: \forall (c1: C).(\forall (c2: C).((wf3 g c1 c2) \to (\forall (u: 
T).(\forall (f: F).(wf3 g (CHead c1 (Flat f) u) c2))))).

