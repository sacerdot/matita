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

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/tau0/defs".

include "G/defs.ma".

include "getl/defs.ma".

inductive tau0 (g: G): C \to (T \to (T \to Prop)) \def
| tau0_sort: \forall (c: C).(\forall (n: nat).(tau0 g c (TSort n) (TSort 
(next g n))))
| tau0_abbr: \forall (c: C).(\forall (d: C).(\forall (v: T).(\forall (i: 
nat).((getl i c (CHead d (Bind Abbr) v)) \to (\forall (w: T).((tau0 g d v w) 
\to (tau0 g c (TLRef i) (lift (S i) O w))))))))
| tau0_abst: \forall (c: C).(\forall (d: C).(\forall (v: T).(\forall (i: 
nat).((getl i c (CHead d (Bind Abst) v)) \to (\forall (w: T).((tau0 g d v w) 
\to (tau0 g c (TLRef i) (lift (S i) O v))))))))
| tau0_bind: \forall (b: B).(\forall (c: C).(\forall (v: T).(\forall (t1: 
T).(\forall (t2: T).((tau0 g (CHead c (Bind b) v) t1 t2) \to (tau0 g c (THead 
(Bind b) v t1) (THead (Bind b) v t2)))))))
| tau0_appl: \forall (c: C).(\forall (v: T).(\forall (t1: T).(\forall (t2: 
T).((tau0 g c t1 t2) \to (tau0 g c (THead (Flat Appl) v t1) (THead (Flat 
Appl) v t2))))))
| tau0_cast: \forall (c: C).(\forall (v1: T).(\forall (v2: T).((tau0 g c v1 
v2) \to (\forall (t1: T).(\forall (t2: T).((tau0 g c t1 t2) \to (tau0 g c 
(THead (Flat Cast) v1 t1) (THead (Flat Cast) v2 t2)))))))).

