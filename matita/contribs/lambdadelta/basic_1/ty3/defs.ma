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

include "Basic-1/pc3/defs.ma".

inductive ty3 (g: G): C \to (T \to (T \to Prop)) \def
| ty3_conv: \forall (c: C).(\forall (t2: T).(\forall (t: T).((ty3 g c t2 t) 
\to (\forall (u: T).(\forall (t1: T).((ty3 g c u t1) \to ((pc3 c t1 t2) \to 
(ty3 g c u t2))))))))
| ty3_sort: \forall (c: C).(\forall (m: nat).(ty3 g c (TSort m) (TSort (next 
g m))))
| ty3_abbr: \forall (n: nat).(\forall (c: C).(\forall (d: C).(\forall (u: 
T).((getl n c (CHead d (Bind Abbr) u)) \to (\forall (t: T).((ty3 g d u t) \to 
(ty3 g c (TLRef n) (lift (S n) O t))))))))
| ty3_abst: \forall (n: nat).(\forall (c: C).(\forall (d: C).(\forall (u: 
T).((getl n c (CHead d (Bind Abst) u)) \to (\forall (t: T).((ty3 g d u t) \to 
(ty3 g c (TLRef n) (lift (S n) O u))))))))
| ty3_bind: \forall (c: C).(\forall (u: T).(\forall (t: T).((ty3 g c u t) \to 
(\forall (b: B).(\forall (t1: T).(\forall (t2: T).((ty3 g (CHead c (Bind b) 
u) t1 t2) \to (ty3 g c (THead (Bind b) u t1) (THead (Bind b) u t2)))))))))
| ty3_appl: \forall (c: C).(\forall (w: T).(\forall (u: T).((ty3 g c w u) \to 
(\forall (v: T).(\forall (t: T).((ty3 g c v (THead (Bind Abst) u t)) \to (ty3 
g c (THead (Flat Appl) w v) (THead (Flat Appl) w (THead (Bind Abst) u 
t)))))))))
| ty3_cast: \forall (c: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c t1 t2) 
\to (\forall (t0: T).((ty3 g c t2 t0) \to (ty3 g c (THead (Flat Cast) t2 t1) 
(THead (Flat Cast) t0 t2))))))).

inductive tys3 (g: G) (c: C): TList \to (T \to Prop) \def
| tys3_nil: \forall (u: T).(\forall (u0: T).((ty3 g c u u0) \to (tys3 g c 
TNil u)))
| tys3_cons: \forall (t: T).(\forall (u: T).((ty3 g c t u) \to (\forall (ts: 
TList).((tys3 g c ts u) \to (tys3 g c (TCons t ts) u))))).

