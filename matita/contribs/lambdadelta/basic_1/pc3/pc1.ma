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

include "Basic-1/pc3/defs.ma".

include "Basic-1/pc1/defs.ma".

include "Basic-1/pr3/pr1.ma".

theorem pc3_pc1:
 \forall (t1: T).(\forall (t2: T).((pc1 t1 t2) \to (\forall (c: C).(pc3 c t1 
t2))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc1 t1 t2)).(\lambda (c: 
C).(let H0 \def H in (ex2_ind T (\lambda (t: T).(pr1 t1 t)) (\lambda (t: 
T).(pr1 t2 t)) (pc3 c t1 t2) (\lambda (x: T).(\lambda (H1: (pr1 t1 
x)).(\lambda (H2: (pr1 t2 x)).(ex_intro2 T (\lambda (t: T).(pr3 c t1 t)) 
(\lambda (t: T).(pr3 c t2 t)) x (pr3_pr1 t1 x H1 c) (pr3_pr1 t2 x H2 c))))) 
H0))))).
(* COMMENTS
Initial nodes: 103
END *)

