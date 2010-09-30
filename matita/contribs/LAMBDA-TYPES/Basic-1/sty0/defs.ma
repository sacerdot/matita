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

include "Basic-1/G/defs.ma".

include "Basic-1/getl/defs.ma".

inductive sty0 (g: G): C \to (T \to (T \to Prop)) \def
| sty0_sort: \forall (c: C).(\forall (n: nat).(sty0 g c (TSort n) (TSort 
(next g n))))
| sty0_abbr: \forall (c: C).(\forall (d: C).(\forall (v: T).(\forall (i: 
nat).((getl i c (CHead d (Bind Abbr) v)) \to (\forall (w: T).((sty0 g d v w) 
\to (sty0 g c (TLRef i) (lift (S i) O w))))))))
| sty0_abst: \forall (c: C).(\forall (d: C).(\forall (v: T).(\forall (i: 
nat).((getl i c (CHead d (Bind Abst) v)) \to (\forall (w: T).((sty0 g d v w) 
\to (sty0 g c (TLRef i) (lift (S i) O v))))))))
| sty0_bind: \forall (b: B).(\forall (c: C).(\forall (v: T).(\forall (t1: 
T).(\forall (t2: T).((sty0 g (CHead c (Bind b) v) t1 t2) \to (sty0 g c (THead 
(Bind b) v t1) (THead (Bind b) v t2)))))))
| sty0_appl: \forall (c: C).(\forall (v: T).(\forall (t1: T).(\forall (t2: 
T).((sty0 g c t1 t2) \to (sty0 g c (THead (Flat Appl) v t1) (THead (Flat 
Appl) v t2))))))
| sty0_cast: \forall (c: C).(\forall (v1: T).(\forall (v2: T).((sty0 g c v1 
v2) \to (\forall (t1: T).(\forall (t2: T).((sty0 g c t1 t2) \to (sty0 g c 
(THead (Flat Cast) v1 t1) (THead (Flat Cast) v2 t2)))))))).

