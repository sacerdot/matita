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

include "Basic-1/leq/defs.ma".

include "Basic-1/getl/defs.ma".

inductive arity (g: G): C \to (T \to (A \to Prop)) \def
| arity_sort: \forall (c: C).(\forall (n: nat).(arity g c (TSort n) (ASort O 
n)))
| arity_abbr: \forall (c: C).(\forall (d: C).(\forall (u: T).(\forall (i: 
nat).((getl i c (CHead d (Bind Abbr) u)) \to (\forall (a: A).((arity g d u a) 
\to (arity g c (TLRef i) a)))))))
| arity_abst: \forall (c: C).(\forall (d: C).(\forall (u: T).(\forall (i: 
nat).((getl i c (CHead d (Bind Abst) u)) \to (\forall (a: A).((arity g d u 
(asucc g a)) \to (arity g c (TLRef i) a)))))))
| arity_bind: \forall (b: B).((not (eq B b Abst)) \to (\forall (c: 
C).(\forall (u: T).(\forall (a1: A).((arity g c u a1) \to (\forall (t: 
T).(\forall (a2: A).((arity g (CHead c (Bind b) u) t a2) \to (arity g c 
(THead (Bind b) u t) a2)))))))))
| arity_head: \forall (c: C).(\forall (u: T).(\forall (a1: A).((arity g c u 
(asucc g a1)) \to (\forall (t: T).(\forall (a2: A).((arity g (CHead c (Bind 
Abst) u) t a2) \to (arity g c (THead (Bind Abst) u t) (AHead a1 a2))))))))
| arity_appl: \forall (c: C).(\forall (u: T).(\forall (a1: A).((arity g c u 
a1) \to (\forall (t: T).(\forall (a2: A).((arity g c t (AHead a1 a2)) \to 
(arity g c (THead (Flat Appl) u t) a2)))))))
| arity_cast: \forall (c: C).(\forall (u: T).(\forall (a: A).((arity g c u 
(asucc g a)) \to (\forall (t: T).((arity g c t a) \to (arity g c (THead (Flat 
Cast) u t) a))))))
| arity_repl: \forall (c: C).(\forall (t: T).(\forall (a1: A).((arity g c t 
a1) \to (\forall (a2: A).((leq g a1 a2) \to (arity g c t a2)))))).

