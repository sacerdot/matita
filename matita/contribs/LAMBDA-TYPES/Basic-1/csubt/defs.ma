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

inductive csubt (g: G): C \to (C \to Prop) \def
| csubt_sort: \forall (n: nat).(csubt g (CSort n) (CSort n))
| csubt_head: \forall (c1: C).(\forall (c2: C).((csubt g c1 c2) \to (\forall 
(k: K).(\forall (u: T).(csubt g (CHead c1 k u) (CHead c2 k u))))))
| csubt_void: \forall (c1: C).(\forall (c2: C).((csubt g c1 c2) \to (\forall 
(b: B).((not (eq B b Void)) \to (\forall (u1: T).(\forall (u2: T).(csubt g 
(CHead c1 (Bind Void) u1) (CHead c2 (Bind b) u2))))))))
| csubt_abst: \forall (c1: C).(\forall (c2: C).((csubt g c1 c2) \to (\forall 
(u: T).(\forall (t: T).((ty3 g c1 u t) \to ((ty3 g c2 u t) \to (csubt g 
(CHead c1 (Bind Abst) t) (CHead c2 (Bind Abbr) u)))))))).

