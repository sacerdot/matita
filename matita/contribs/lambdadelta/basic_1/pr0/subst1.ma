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

include "Basic-1/pr0/props.ma".

include "Basic-1/subst1/defs.ma".

theorem pr0_delta1:
 \forall (u1: T).(\forall (u2: T).((pr0 u1 u2) \to (\forall (t1: T).(\forall 
(t2: T).((pr0 t1 t2) \to (\forall (w: T).((subst1 O u2 t2 w) \to (pr0 (THead 
(Bind Abbr) u1 t1) (THead (Bind Abbr) u2 w)))))))))
\def
 \lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr0 u1 u2)).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (H0: (pr0 t1 t2)).(\lambda (w: T).(\lambda (H1: 
(subst1 O u2 t2 w)).(subst1_ind O u2 t2 (\lambda (t: T).(pr0 (THead (Bind 
Abbr) u1 t1) (THead (Bind Abbr) u2 t))) (pr0_comp u1 u2 H t1 t2 H0 (Bind 
Abbr)) (\lambda (t0: T).(\lambda (H2: (subst0 O u2 t2 t0)).(pr0_delta u1 u2 H 
t1 t2 H0 t0 H2))) w H1)))))))).
(* COMMENTS
Initial nodes: 115
END *)

theorem pr0_subst1_back:
 \forall (u2: T).(\forall (t1: T).(\forall (t2: T).(\forall (i: nat).((subst1 
i u2 t1 t2) \to (\forall (u1: T).((pr0 u1 u2) \to (ex2 T (\lambda (t: 
T).(subst1 i u1 t1 t)) (\lambda (t: T).(pr0 t t2)))))))))
\def
 \lambda (u2: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (i: nat).(\lambda 
(H: (subst1 i u2 t1 t2)).(subst1_ind i u2 t1 (\lambda (t: T).(\forall (u1: 
T).((pr0 u1 u2) \to (ex2 T (\lambda (t0: T).(subst1 i u1 t1 t0)) (\lambda 
(t0: T).(pr0 t0 t)))))) (\lambda (u1: T).(\lambda (_: (pr0 u1 u2)).(ex_intro2 
T (\lambda (t: T).(subst1 i u1 t1 t)) (\lambda (t: T).(pr0 t t1)) t1 
(subst1_refl i u1 t1) (pr0_refl t1)))) (\lambda (t0: T).(\lambda (H0: (subst0 
i u2 t1 t0)).(\lambda (u1: T).(\lambda (H1: (pr0 u1 u2)).(ex2_ind T (\lambda 
(t: T).(subst0 i u1 t1 t)) (\lambda (t: T).(pr0 t t0)) (ex2 T (\lambda (t: 
T).(subst1 i u1 t1 t)) (\lambda (t: T).(pr0 t t0))) (\lambda (x: T).(\lambda 
(H2: (subst0 i u1 t1 x)).(\lambda (H3: (pr0 x t0)).(ex_intro2 T (\lambda (t: 
T).(subst1 i u1 t1 t)) (\lambda (t: T).(pr0 t t0)) x (subst1_single i u1 t1 x 
H2) H3)))) (pr0_subst0_back u2 t1 t0 i H0 u1 H1)))))) t2 H))))).
(* COMMENTS
Initial nodes: 251
END *)

theorem pr0_subst1_fwd:
 \forall (u2: T).(\forall (t1: T).(\forall (t2: T).(\forall (i: nat).((subst1 
i u2 t1 t2) \to (\forall (u1: T).((pr0 u2 u1) \to (ex2 T (\lambda (t: 
T).(subst1 i u1 t1 t)) (\lambda (t: T).(pr0 t2 t)))))))))
\def
 \lambda (u2: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (i: nat).(\lambda 
(H: (subst1 i u2 t1 t2)).(subst1_ind i u2 t1 (\lambda (t: T).(\forall (u1: 
T).((pr0 u2 u1) \to (ex2 T (\lambda (t0: T).(subst1 i u1 t1 t0)) (\lambda 
(t0: T).(pr0 t t0)))))) (\lambda (u1: T).(\lambda (_: (pr0 u2 u1)).(ex_intro2 
T (\lambda (t: T).(subst1 i u1 t1 t)) (\lambda (t: T).(pr0 t1 t)) t1 
(subst1_refl i u1 t1) (pr0_refl t1)))) (\lambda (t0: T).(\lambda (H0: (subst0 
i u2 t1 t0)).(\lambda (u1: T).(\lambda (H1: (pr0 u2 u1)).(ex2_ind T (\lambda 
(t: T).(subst0 i u1 t1 t)) (\lambda (t: T).(pr0 t0 t)) (ex2 T (\lambda (t: 
T).(subst1 i u1 t1 t)) (\lambda (t: T).(pr0 t0 t))) (\lambda (x: T).(\lambda 
(H2: (subst0 i u1 t1 x)).(\lambda (H3: (pr0 t0 x)).(ex_intro2 T (\lambda (t: 
T).(subst1 i u1 t1 t)) (\lambda (t: T).(pr0 t0 t)) x (subst1_single i u1 t1 x 
H2) H3)))) (pr0_subst0_fwd u2 t1 t0 i H0 u1 H1)))))) t2 H))))).
(* COMMENTS
Initial nodes: 251
END *)

theorem pr0_subst1:
 \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (v1: T).(\forall 
(w1: T).(\forall (i: nat).((subst1 i v1 t1 w1) \to (\forall (v2: T).((pr0 v1 
v2) \to (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst1 i v2 t2 
w2)))))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr0 t1 t2)).(\lambda (v1: 
T).(\lambda (w1: T).(\lambda (i: nat).(\lambda (H0: (subst1 i v1 t1 
w1)).(subst1_ind i v1 t1 (\lambda (t: T).(\forall (v2: T).((pr0 v1 v2) \to 
(ex2 T (\lambda (w2: T).(pr0 t w2)) (\lambda (w2: T).(subst1 i v2 t2 w2)))))) 
(\lambda (v2: T).(\lambda (_: (pr0 v1 v2)).(ex_intro2 T (\lambda (w2: T).(pr0 
t1 w2)) (\lambda (w2: T).(subst1 i v2 t2 w2)) t2 H (subst1_refl i v2 t2)))) 
(\lambda (t0: T).(\lambda (H1: (subst0 i v1 t1 t0)).(\lambda (v2: T).(\lambda 
(H2: (pr0 v1 v2)).(or_ind (pr0 t0 t2) (ex2 T (\lambda (w2: T).(pr0 t0 w2)) 
(\lambda (w2: T).(subst0 i v2 t2 w2))) (ex2 T (\lambda (w2: T).(pr0 t0 w2)) 
(\lambda (w2: T).(subst1 i v2 t2 w2))) (\lambda (H3: (pr0 t0 t2)).(ex_intro2 
T (\lambda (w2: T).(pr0 t0 w2)) (\lambda (w2: T).(subst1 i v2 t2 w2)) t2 H3 
(subst1_refl i v2 t2))) (\lambda (H3: (ex2 T (\lambda (w2: T).(pr0 t0 w2)) 
(\lambda (w2: T).(subst0 i v2 t2 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 t0 
w2)) (\lambda (w2: T).(subst0 i v2 t2 w2)) (ex2 T (\lambda (w2: T).(pr0 t0 
w2)) (\lambda (w2: T).(subst1 i v2 t2 w2))) (\lambda (x: T).(\lambda (H4: 
(pr0 t0 x)).(\lambda (H5: (subst0 i v2 t2 x)).(ex_intro2 T (\lambda (w2: 
T).(pr0 t0 w2)) (\lambda (w2: T).(subst1 i v2 t2 w2)) x H4 (subst1_single i 
v2 t2 x H5))))) H3)) (pr0_subst0 t1 t2 H v1 t0 i H1 v2 H2)))))) w1 H0))))))).
(* COMMENTS
Initial nodes: 385
END *)

