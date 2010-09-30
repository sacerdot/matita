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

inductive csubv: C \to (C \to Prop) \def
| csubv_sort: \forall (n: nat).(csubv (CSort n) (CSort n))
| csubv_void: \forall (c1: C).(\forall (c2: C).((csubv c1 c2) \to (\forall 
(v1: T).(\forall (v2: T).(csubv (CHead c1 (Bind Void) v1) (CHead c2 (Bind 
Void) v2))))))
| csubv_bind: \forall (c1: C).(\forall (c2: C).((csubv c1 c2) \to (\forall 
(b1: B).((not (eq B b1 Void)) \to (\forall (b2: B).(\forall (v1: T).(\forall 
(v2: T).(csubv (CHead c1 (Bind b1) v1) (CHead c2 (Bind b2) v2)))))))))
| csubv_flat: \forall (c1: C).(\forall (c2: C).((csubv c1 c2) \to (\forall 
(f1: F).(\forall (f2: F).(\forall (v1: T).(\forall (v2: T).(csubv (CHead c1 
(Flat f1) v1) (CHead c2 (Flat f2) v2)))))))).

