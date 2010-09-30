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

include "Basic-1/subst0/defs.ma".

inductive pr0: T \to (T \to Prop) \def
| pr0_refl: \forall (t: T).(pr0 t t)
| pr0_comp: \forall (u1: T).(\forall (u2: T).((pr0 u1 u2) \to (\forall (t1: 
T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (k: K).(pr0 (THead k u1 t1) 
(THead k u2 t2))))))))
| pr0_beta: \forall (u: T).(\forall (v1: T).(\forall (v2: T).((pr0 v1 v2) \to 
(\forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (pr0 (THead (Flat Appl) v1 
(THead (Bind Abst) u t1)) (THead (Bind Abbr) v2 t2))))))))
| pr0_upsilon: \forall (b: B).((not (eq B b Abst)) \to (\forall (v1: 
T).(\forall (v2: T).((pr0 v1 v2) \to (\forall (u1: T).(\forall (u2: T).((pr0 
u1 u2) \to (\forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (pr0 (THead 
(Flat Appl) v1 (THead (Bind b) u1 t1)) (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t2)))))))))))))
| pr0_delta: \forall (u1: T).(\forall (u2: T).((pr0 u1 u2) \to (\forall (t1: 
T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (w: T).((subst0 O u2 t2 w) \to 
(pr0 (THead (Bind Abbr) u1 t1) (THead (Bind Abbr) u2 w)))))))))
| pr0_zeta: \forall (b: B).((not (eq B b Abst)) \to (\forall (t1: T).(\forall 
(t2: T).((pr0 t1 t2) \to (\forall (u: T).(pr0 (THead (Bind b) u (lift (S O) O 
t1)) t2))))))
| pr0_tau: \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (u: 
T).(pr0 (THead (Flat Cast) u t1) t2)))).

