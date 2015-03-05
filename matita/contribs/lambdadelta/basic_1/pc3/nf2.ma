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

include "basic_1/pc3/defs.ma".

include "basic_1/nf2/pr3.ma".

theorem pc3_nf2:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3 c t1 t2) \to ((nf2 c 
t1) \to ((nf2 c t2) \to (eq T t1 t2))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc3 c t1 
t2)).(\lambda (H0: (nf2 c t1)).(\lambda (H1: (nf2 c t2)).(let H2 \def H in 
(let TMP_1 \def (\lambda (t: T).(pr3 c t1 t)) in (let TMP_2 \def (\lambda (t: 
T).(pr3 c t2 t)) in (let TMP_3 \def (eq T t1 t2) in (let TMP_9 \def (\lambda 
(x: T).(\lambda (H3: (pr3 c t1 x)).(\lambda (H4: (pr3 c t2 x)).(let H_y \def 
(nf2_pr3_unfold c t1 x H3 H0) in (let TMP_4 \def (\lambda (t: T).(pr3 c t2 
t)) in (let H5 \def (eq_ind_r T x TMP_4 H4 t1 H_y) in (let TMP_5 \def 
(\lambda (t: T).(pr3 c t1 t)) in (let H6 \def (eq_ind_r T x TMP_5 H3 t1 H_y) 
in (let H_y0 \def (nf2_pr3_unfold c t2 t1 H5 H1) in (let TMP_6 \def (\lambda 
(t: T).(pr3 c t t1)) in (let H7 \def (eq_ind T t2 TMP_6 H5 t1 H_y0) in (let 
TMP_7 \def (\lambda (t: T).(eq T t1 t)) in (let TMP_8 \def (refl_equal T t1) 
in (eq_ind_r T t1 TMP_7 TMP_8 t2 H_y0)))))))))))))) in (ex2_ind T TMP_1 TMP_2 
TMP_3 TMP_9 H2))))))))))).

theorem pc3_nf2_unfold:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3 c t1 t2) \to ((nf2 c 
t2) \to (pr3 c t1 t2)))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc3 c t1 
t2)).(\lambda (H0: (nf2 c t2)).(let H1 \def H in (let TMP_1 \def (\lambda (t: 
T).(pr3 c t1 t)) in (let TMP_2 \def (\lambda (t: T).(pr3 c t2 t)) in (let 
TMP_3 \def (pr3 c t1 t2) in (let TMP_5 \def (\lambda (x: T).(\lambda (H2: 
(pr3 c t1 x)).(\lambda (H3: (pr3 c t2 x)).(let H_y \def (nf2_pr3_unfold c t2 
x H3 H0) in (let TMP_4 \def (\lambda (t: T).(pr3 c t1 t)) in (let H4 \def 
(eq_ind_r T x TMP_4 H2 t2 H_y) in H4)))))) in (ex2_ind T TMP_1 TMP_2 TMP_3 
TMP_5 H1)))))))))).

