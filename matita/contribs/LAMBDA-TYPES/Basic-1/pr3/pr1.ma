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

include "Basic-1/pr3/defs.ma".

include "Basic-1/pr1/defs.ma".

theorem pr3_pr1:
 \forall (t1: T).(\forall (t2: T).((pr1 t1 t2) \to (\forall (c: C).(pr3 c t1 
t2))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr1 t1 t2)).(pr1_ind (\lambda 
(t: T).(\lambda (t0: T).(\forall (c: C).(pr3 c t t0)))) (\lambda (t: 
T).(\lambda (c: C).(pr3_refl c t))) (\lambda (t0: T).(\lambda (t3: 
T).(\lambda (H0: (pr0 t3 t0)).(\lambda (t4: T).(\lambda (_: (pr1 t0 
t4)).(\lambda (H2: ((\forall (c: C).(pr3 c t0 t4)))).(\lambda (c: 
C).(pr3_sing c t0 t3 (pr2_free c t3 t0 H0) t4 (H2 c))))))))) t1 t2 H))).
(* COMMENTS
Initial nodes: 95
END *)

