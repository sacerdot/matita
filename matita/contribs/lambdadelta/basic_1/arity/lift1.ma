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

include "Basic-1/arity/props.ma".

include "Basic-1/drop1/fwd.ma".

theorem arity_lift1:
 \forall (g: G).(\forall (a: A).(\forall (c2: C).(\forall (hds: 
PList).(\forall (c1: C).(\forall (t: T).((drop1 hds c1 c2) \to ((arity g c2 t 
a) \to (arity g c1 (lift1 hds t) a))))))))
\def
 \lambda (g: G).(\lambda (a: A).(\lambda (c2: C).(\lambda (hds: 
PList).(PList_ind (\lambda (p: PList).(\forall (c1: C).(\forall (t: 
T).((drop1 p c1 c2) \to ((arity g c2 t a) \to (arity g c1 (lift1 p t) a)))))) 
(\lambda (c1: C).(\lambda (t: T).(\lambda (H: (drop1 PNil c1 c2)).(\lambda 
(H0: (arity g c2 t a)).(let H_y \def (drop1_gen_pnil c1 c2 H) in (eq_ind_r C 
c2 (\lambda (c: C).(arity g c t a)) H0 c1 H_y)))))) (\lambda (n: 
nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda (H: ((\forall (c1: 
C).(\forall (t: T).((drop1 p c1 c2) \to ((arity g c2 t a) \to (arity g c1 
(lift1 p t) a))))))).(\lambda (c1: C).(\lambda (t: T).(\lambda (H0: (drop1 
(PCons n n0 p) c1 c2)).(\lambda (H1: (arity g c2 t a)).(let H_x \def 
(drop1_gen_pcons c1 c2 p n n0 H0) in (let H2 \def H_x in (ex2_ind C (\lambda 
(c3: C).(drop n n0 c1 c3)) (\lambda (c3: C).(drop1 p c3 c2)) (arity g c1 
(lift n n0 (lift1 p t)) a) (\lambda (x: C).(\lambda (H3: (drop n n0 c1 
x)).(\lambda (H4: (drop1 p x c2)).(arity_lift g x (lift1 p t) a (H x t H4 H1) 
c1 n n0 H3)))) H2))))))))))) hds)))).
(* COMMENTS
Initial nodes: 289
END *)

