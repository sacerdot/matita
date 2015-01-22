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

include "Basic-1/nf2/defs.ma".

include "Basic-1/pr3/pr3.ma".

theorem nf2_pr3_unfold:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to ((nf2 c 
t1) \to (eq T t1 t2)))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr3 c t1 
t2)).(pr3_ind c (\lambda (t: T).(\lambda (t0: T).((nf2 c t) \to (eq T t 
t0)))) (\lambda (t: T).(\lambda (H0: (nf2 c t)).(H0 t (pr2_free c t t 
(pr0_refl t))))) (\lambda (t0: T).(\lambda (t3: T).(\lambda (H0: (pr2 c t3 
t0)).(\lambda (t4: T).(\lambda (_: (pr3 c t0 t4)).(\lambda (H2: (((nf2 c t0) 
\to (eq T t0 t4)))).(\lambda (H3: (nf2 c t3)).(let H4 \def H3 in (let H5 \def 
(eq_ind T t3 (\lambda (t: T).(nf2 c t)) H3 t0 (H4 t0 H0)) in (let H6 \def 
(eq_ind T t3 (\lambda (t: T).(pr2 c t t0)) H0 t0 (H4 t0 H0)) in (eq_ind_r T 
t0 (\lambda (t: T).(eq T t t4)) (H2 H5) t3 (H4 t0 H0)))))))))))) t1 t2 H)))).
(* COMMENTS
Initial nodes: 187
END *)

theorem nf2_pr3_confluence:
 \forall (c: C).(\forall (t1: T).((nf2 c t1) \to (\forall (t2: T).((nf2 c t2) 
\to (\forall (t: T).((pr3 c t t1) \to ((pr3 c t t2) \to (eq T t1 t2))))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (H: (nf2 c t1)).(\lambda (t2: 
T).(\lambda (H0: (nf2 c t2)).(\lambda (t: T).(\lambda (H1: (pr3 c t 
t1)).(\lambda (H2: (pr3 c t t2)).(ex2_ind T (\lambda (t0: T).(pr3 c t2 t0)) 
(\lambda (t0: T).(pr3 c t1 t0)) (eq T t1 t2) (\lambda (x: T).(\lambda (H3: 
(pr3 c t2 x)).(\lambda (H4: (pr3 c t1 x)).(let H_y \def (nf2_pr3_unfold c t1 
x H4 H) in (let H5 \def (eq_ind_r T x (\lambda (t0: T).(pr3 c t1 t0)) H4 t1 
H_y) in (let H6 \def (eq_ind_r T x (\lambda (t0: T).(pr3 c t2 t0)) H3 t1 H_y) 
in (let H_y0 \def (nf2_pr3_unfold c t2 t1 H6 H0) in (let H7 \def (eq_ind T t2 
(\lambda (t0: T).(pr3 c t0 t1)) H6 t1 H_y0) in (eq_ind_r T t1 (\lambda (t0: 
T).(eq T t1 t0)) (refl_equal T t1) t2 H_y0))))))))) (pr3_confluence c t t2 H2 
t1 H1))))))))).
(* COMMENTS
Initial nodes: 215
END *)

