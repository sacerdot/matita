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

include "Basic-1/sn3/defs.ma".

include "Basic-1/nf2/dec.ma".

include "Basic-1/nf2/pr3.ma".

theorem sn3_nf2:
 \forall (c: C).(\forall (t: T).((nf2 c t) \to (sn3 c t)))
\def
 \lambda (c: C).(\lambda (t: T).(\lambda (H: (nf2 c t)).(sn3_sing c t 
(\lambda (t2: T).(\lambda (H0: (((eq T t t2) \to (\forall (P: 
Prop).P)))).(\lambda (H1: (pr3 c t t2)).(let H_y \def (nf2_pr3_unfold c t t2 
H1 H) in (let H2 \def (eq_ind_r T t2 (\lambda (t0: T).(pr3 c t t0)) H1 t H_y) 
in (let H3 \def (eq_ind_r T t2 (\lambda (t0: T).((eq T t t0) \to (\forall (P: 
Prop).P))) H0 t H_y) in (eq_ind T t (\lambda (t0: T).(sn3 c t0)) (H3 
(refl_equal T t) (sn3 c t)) t2 H_y)))))))))).
(* COMMENTS
Initial nodes: 129
END *)

theorem nf2_sn3:
 \forall (c: C).(\forall (t: T).((sn3 c t) \to (ex2 T (\lambda (u: T).(pr3 c 
t u)) (\lambda (u: T).(nf2 c u)))))
\def
 \lambda (c: C).(\lambda (t: T).(\lambda (H: (sn3 c t)).(sn3_ind c (\lambda 
(t0: T).(ex2 T (\lambda (u: T).(pr3 c t0 u)) (\lambda (u: T).(nf2 c u)))) 
(\lambda (t1: T).(\lambda (_: ((\forall (t2: T).((((eq T t1 t2) \to (\forall 
(P: Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c t2)))))).(\lambda (H1: ((\forall 
(t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to 
(ex2 T (\lambda (u: T).(pr3 c t2 u)) (\lambda (u: T).(nf2 c u)))))))).(let 
H_x \def (nf2_dec c t1) in (let H2 \def H_x in (or_ind (nf2 c t1) (ex2 T 
(\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: 
T).(pr2 c t1 t2))) (ex2 T (\lambda (u: T).(pr3 c t1 u)) (\lambda (u: T).(nf2 
c u))) (\lambda (H3: (nf2 c t1)).(ex_intro2 T (\lambda (u: T).(pr3 c t1 u)) 
(\lambda (u: T).(nf2 c u)) t1 (pr3_refl c t1) H3)) (\lambda (H3: (ex2 T 
(\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) (\lambda (t2: 
T).(pr2 c t1 t2)))).(ex2_ind T (\lambda (t2: T).((eq T t1 t2) \to (\forall 
(P: Prop).P))) (\lambda (t2: T).(pr2 c t1 t2)) (ex2 T (\lambda (u: T).(pr3 c 
t1 u)) (\lambda (u: T).(nf2 c u))) (\lambda (x: T).(\lambda (H4: (((eq T t1 
x) \to (\forall (P: Prop).P)))).(\lambda (H5: (pr2 c t1 x)).(let H_y \def (H1 
x H4) in (let H6 \def (H_y (pr3_pr2 c t1 x H5)) in (ex2_ind T (\lambda (u: 
T).(pr3 c x u)) (\lambda (u: T).(nf2 c u)) (ex2 T (\lambda (u: T).(pr3 c t1 
u)) (\lambda (u: T).(nf2 c u))) (\lambda (x0: T).(\lambda (H7: (pr3 c x 
x0)).(\lambda (H8: (nf2 c x0)).(ex_intro2 T (\lambda (u: T).(pr3 c t1 u)) 
(\lambda (u: T).(nf2 c u)) x0 (pr3_sing c x t1 H5 x0 H7) H8)))) H6)))))) H3)) 
H2)))))) t H))).
(* COMMENTS
Initial nodes: 443
END *)

