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

include "Basic-1/pr0/fwd.ma".

include "Basic-1/lift/tlt.ma".

theorem pr0_confluence__pr0_cong_upsilon_refl:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (u0: T).(\forall (u3: 
T).((pr0 u0 u3) \to (\forall (t4: T).(\forall (t5: T).((pr0 t4 t5) \to 
(\forall (u2: T).(\forall (v2: T).(\forall (x: T).((pr0 u2 x) \to ((pr0 v2 x) 
\to (ex2 T (\lambda (t: T).(pr0 (THead (Flat Appl) u2 (THead (Bind b) u0 t4)) 
t)) (\lambda (t: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O 
v2) t5)) t)))))))))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda (u0: T).(\lambda 
(u3: T).(\lambda (H0: (pr0 u0 u3)).(\lambda (t4: T).(\lambda (t5: T).(\lambda 
(H1: (pr0 t4 t5)).(\lambda (u2: T).(\lambda (v2: T).(\lambda (x: T).(\lambda 
(H2: (pr0 u2 x)).(\lambda (H3: (pr0 v2 x)).(ex_intro2 T (\lambda (t: T).(pr0 
(THead (Flat Appl) u2 (THead (Bind b) u0 t4)) t)) (\lambda (t: T).(pr0 (THead 
(Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) t5)) t)) (THead (Bind b) u3 
(THead (Flat Appl) (lift (S O) O x) t5)) (pr0_upsilon b H u2 x H2 u0 u3 H0 t4 
t5 H1) (pr0_comp u3 u3 (pr0_refl u3) (THead (Flat Appl) (lift (S O) O v2) t5) 
(THead (Flat Appl) (lift (S O) O x) t5) (pr0_comp (lift (S O) O v2) (lift (S 
O) O x) (pr0_lift v2 x H3 (S O) O) t5 t5 (pr0_refl t5) (Flat Appl)) (Bind 
b))))))))))))))).
(* COMMENTS
Initial nodes: 257
END *)

theorem pr0_confluence__pr0_cong_upsilon_cong:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (u2: T).(\forall (v2: 
T).(\forall (x: T).((pr0 u2 x) \to ((pr0 v2 x) \to (\forall (t2: T).(\forall 
(t5: T).(\forall (x0: T).((pr0 t2 x0) \to ((pr0 t5 x0) \to (\forall (u5: 
T).(\forall (u3: T).(\forall (x1: T).((pr0 u5 x1) \to ((pr0 u3 x1) \to (ex2 T 
(\lambda (t: T).(pr0 (THead (Flat Appl) u2 (THead (Bind b) u5 t2)) t)) 
(\lambda (t: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) 
t5)) t)))))))))))))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda (u2: T).(\lambda 
(v2: T).(\lambda (x: T).(\lambda (H0: (pr0 u2 x)).(\lambda (H1: (pr0 v2 
x)).(\lambda (t2: T).(\lambda (t5: T).(\lambda (x0: T).(\lambda (H2: (pr0 t2 
x0)).(\lambda (H3: (pr0 t5 x0)).(\lambda (u5: T).(\lambda (u3: T).(\lambda 
(x1: T).(\lambda (H4: (pr0 u5 x1)).(\lambda (H5: (pr0 u3 x1)).(ex_intro2 T 
(\lambda (t: T).(pr0 (THead (Flat Appl) u2 (THead (Bind b) u5 t2)) t)) 
(\lambda (t: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) 
t5)) t)) (THead (Bind b) x1 (THead (Flat Appl) (lift (S O) O x) x0)) 
(pr0_upsilon b H u2 x H0 u5 x1 H4 t2 x0 H2) (pr0_comp u3 x1 H5 (THead (Flat 
Appl) (lift (S O) O v2) t5) (THead (Flat Appl) (lift (S O) O x) x0) (pr0_comp 
(lift (S O) O v2) (lift (S O) O x) (pr0_lift v2 x H1 (S O) O) t5 x0 H3 (Flat 
Appl)) (Bind b))))))))))))))))))).
(* COMMENTS
Initial nodes: 269
END *)

theorem pr0_confluence__pr0_cong_upsilon_delta:
 (not (eq B Abbr Abst)) \to (\forall (u5: T).(\forall (t2: T).(\forall (w: 
T).((subst0 O u5 t2 w) \to (\forall (u2: T).(\forall (v2: T).(\forall (x: 
T).((pr0 u2 x) \to ((pr0 v2 x) \to (\forall (t5: T).(\forall (x0: T).((pr0 t2 
x0) \to ((pr0 t5 x0) \to (\forall (u3: T).(\forall (x1: T).((pr0 u5 x1) \to 
((pr0 u3 x1) \to (ex2 T (\lambda (t: T).(pr0 (THead (Flat Appl) u2 (THead 
(Bind Abbr) u5 w)) t)) (\lambda (t: T).(pr0 (THead (Bind Abbr) u3 (THead 
(Flat Appl) (lift (S O) O v2) t5)) t))))))))))))))))))))
\def
 \lambda (H: (not (eq B Abbr Abst))).(\lambda (u5: T).(\lambda (t2: 
T).(\lambda (w: T).(\lambda (H0: (subst0 O u5 t2 w)).(\lambda (u2: 
T).(\lambda (v2: T).(\lambda (x: T).(\lambda (H1: (pr0 u2 x)).(\lambda (H2: 
(pr0 v2 x)).(\lambda (t5: T).(\lambda (x0: T).(\lambda (H3: (pr0 t2 
x0)).(\lambda (H4: (pr0 t5 x0)).(\lambda (u3: T).(\lambda (x1: T).(\lambda 
(H5: (pr0 u5 x1)).(\lambda (H6: (pr0 u3 x1)).(or_ind (pr0 w x0) (ex2 T 
(\lambda (w2: T).(pr0 w w2)) (\lambda (w2: T).(subst0 O x1 x0 w2))) (ex2 T 
(\lambda (t: T).(pr0 (THead (Flat Appl) u2 (THead (Bind Abbr) u5 w)) t)) 
(\lambda (t: T).(pr0 (THead (Bind Abbr) u3 (THead (Flat Appl) (lift (S O) O 
v2) t5)) t))) (\lambda (H7: (pr0 w x0)).(ex_intro2 T (\lambda (t: T).(pr0 
(THead (Flat Appl) u2 (THead (Bind Abbr) u5 w)) t)) (\lambda (t: T).(pr0 
(THead (Bind Abbr) u3 (THead (Flat Appl) (lift (S O) O v2) t5)) t)) (THead 
(Bind Abbr) x1 (THead (Flat Appl) (lift (S O) O x) x0)) (pr0_upsilon Abbr H 
u2 x H1 u5 x1 H5 w x0 H7) (pr0_comp u3 x1 H6 (THead (Flat Appl) (lift (S O) O 
v2) t5) (THead (Flat Appl) (lift (S O) O x) x0) (pr0_comp (lift (S O) O v2) 
(lift (S O) O x) (pr0_lift v2 x H2 (S O) O) t5 x0 H4 (Flat Appl)) (Bind 
Abbr)))) (\lambda (H7: (ex2 T (\lambda (w2: T).(pr0 w w2)) (\lambda (w2: 
T).(subst0 O x1 x0 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 w w2)) (\lambda 
(w2: T).(subst0 O x1 x0 w2)) (ex2 T (\lambda (t: T).(pr0 (THead (Flat Appl) 
u2 (THead (Bind Abbr) u5 w)) t)) (\lambda (t: T).(pr0 (THead (Bind Abbr) u3 
(THead (Flat Appl) (lift (S O) O v2) t5)) t))) (\lambda (x2: T).(\lambda (H8: 
(pr0 w x2)).(\lambda (H9: (subst0 O x1 x0 x2)).(ex_intro2 T (\lambda (t: 
T).(pr0 (THead (Flat Appl) u2 (THead (Bind Abbr) u5 w)) t)) (\lambda (t: 
T).(pr0 (THead (Bind Abbr) u3 (THead (Flat Appl) (lift (S O) O v2) t5)) t)) 
(THead (Bind Abbr) x1 (THead (Flat Appl) (lift (S O) O x) x2)) (pr0_upsilon 
Abbr H u2 x H1 u5 x1 H5 w x2 H8) (pr0_delta u3 x1 H6 (THead (Flat Appl) (lift 
(S O) O v2) t5) (THead (Flat Appl) (lift (S O) O x) x0) (pr0_comp (lift (S O) 
O v2) (lift (S O) O x) (pr0_lift v2 x H2 (S O) O) t5 x0 H4 (Flat Appl)) 
(THead (Flat Appl) (lift (S O) O x) x2) (subst0_snd (Flat Appl) x1 x2 x0 O H9 
(lift (S O) O x))))))) H7)) (pr0_subst0 t2 x0 H3 u5 w O H0 x1 
H5))))))))))))))))))).
(* COMMENTS
Initial nodes: 769
END *)

theorem pr0_confluence__pr0_cong_upsilon_zeta:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (u0: T).(\forall (u3: 
T).((pr0 u0 u3) \to (\forall (u2: T).(\forall (v2: T).(\forall (x0: T).((pr0 
u2 x0) \to ((pr0 v2 x0) \to (\forall (x: T).(\forall (t3: T).(\forall (x1: 
T).((pr0 x x1) \to ((pr0 t3 x1) \to (ex2 T (\lambda (t: T).(pr0 (THead (Flat 
Appl) u2 t3) t)) (\lambda (t: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) 
(lift (S O) O v2) (lift (S O) O x))) t)))))))))))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda (u0: T).(\lambda 
(u3: T).(\lambda (_: (pr0 u0 u3)).(\lambda (u2: T).(\lambda (v2: T).(\lambda 
(x0: T).(\lambda (H1: (pr0 u2 x0)).(\lambda (H2: (pr0 v2 x0)).(\lambda (x: 
T).(\lambda (t3: T).(\lambda (x1: T).(\lambda (H3: (pr0 x x1)).(\lambda (H4: 
(pr0 t3 x1)).(eq_ind T (lift (S O) O (THead (Flat Appl) v2 x)) (\lambda (t: 
T).(ex2 T (\lambda (t0: T).(pr0 (THead (Flat Appl) u2 t3) t0)) (\lambda (t0: 
T).(pr0 (THead (Bind b) u3 t) t0)))) (ex_intro2 T (\lambda (t: T).(pr0 (THead 
(Flat Appl) u2 t3) t)) (\lambda (t: T).(pr0 (THead (Bind b) u3 (lift (S O) O 
(THead (Flat Appl) v2 x))) t)) (THead (Flat Appl) x0 x1) (pr0_comp u2 x0 H1 
t3 x1 H4 (Flat Appl)) (pr0_zeta b H (THead (Flat Appl) v2 x) (THead (Flat 
Appl) x0 x1) (pr0_comp v2 x0 H2 x x1 H3 (Flat Appl)) u3)) (THead (Flat Appl) 
(lift (S O) O v2) (lift (S O) O x)) (lift_flat Appl v2 x (S O) 
O)))))))))))))))).
(* COMMENTS
Initial nodes: 283
END *)

theorem pr0_confluence__pr0_cong_delta:
 \forall (u3: T).(\forall (t5: T).(\forall (w: T).((subst0 O u3 t5 w) \to 
(\forall (u2: T).(\forall (x: T).((pr0 u2 x) \to ((pr0 u3 x) \to (\forall 
(t3: T).(\forall (x0: T).((pr0 t3 x0) \to ((pr0 t5 x0) \to (ex2 T (\lambda 
(t: T).(pr0 (THead (Bind Abbr) u2 t3) t)) (\lambda (t: T).(pr0 (THead (Bind 
Abbr) u3 w) t))))))))))))))
\def
 \lambda (u3: T).(\lambda (t5: T).(\lambda (w: T).(\lambda (H: (subst0 O u3 
t5 w)).(\lambda (u2: T).(\lambda (x: T).(\lambda (H0: (pr0 u2 x)).(\lambda 
(H1: (pr0 u3 x)).(\lambda (t3: T).(\lambda (x0: T).(\lambda (H2: (pr0 t3 
x0)).(\lambda (H3: (pr0 t5 x0)).(or_ind (pr0 w x0) (ex2 T (\lambda (w2: 
T).(pr0 w w2)) (\lambda (w2: T).(subst0 O x x0 w2))) (ex2 T (\lambda (t: 
T).(pr0 (THead (Bind Abbr) u2 t3) t)) (\lambda (t: T).(pr0 (THead (Bind Abbr) 
u3 w) t))) (\lambda (H4: (pr0 w x0)).(ex_intro2 T (\lambda (t: T).(pr0 (THead 
(Bind Abbr) u2 t3) t)) (\lambda (t: T).(pr0 (THead (Bind Abbr) u3 w) t)) 
(THead (Bind Abbr) x x0) (pr0_comp u2 x H0 t3 x0 H2 (Bind Abbr)) (pr0_comp u3 
x H1 w x0 H4 (Bind Abbr)))) (\lambda (H4: (ex2 T (\lambda (w2: T).(pr0 w w2)) 
(\lambda (w2: T).(subst0 O x x0 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 w 
w2)) (\lambda (w2: T).(subst0 O x x0 w2)) (ex2 T (\lambda (t: T).(pr0 (THead 
(Bind Abbr) u2 t3) t)) (\lambda (t: T).(pr0 (THead (Bind Abbr) u3 w) t))) 
(\lambda (x1: T).(\lambda (H5: (pr0 w x1)).(\lambda (H6: (subst0 O x x0 
x1)).(ex_intro2 T (\lambda (t: T).(pr0 (THead (Bind Abbr) u2 t3) t)) (\lambda 
(t: T).(pr0 (THead (Bind Abbr) u3 w) t)) (THead (Bind Abbr) x x1) (pr0_delta 
u2 x H0 t3 x0 H2 x1 H6) (pr0_comp u3 x H1 w x1 H5 (Bind Abbr)))))) H4)) 
(pr0_subst0 t5 x0 H3 u3 w O H x H1))))))))))))).
(* COMMENTS
Initial nodes: 409
END *)

theorem pr0_confluence__pr0_upsilon_upsilon:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (v1: T).(\forall (v2: 
T).(\forall (x0: T).((pr0 v1 x0) \to ((pr0 v2 x0) \to (\forall (u1: 
T).(\forall (u2: T).(\forall (x1: T).((pr0 u1 x1) \to ((pr0 u2 x1) \to 
(\forall (t1: T).(\forall (t2: T).(\forall (x2: T).((pr0 t1 x2) \to ((pr0 t2 
x2) \to (ex2 T (\lambda (t: T).(pr0 (THead (Bind b) u1 (THead (Flat Appl) 
(lift (S O) O v1) t1)) t)) (\lambda (t: T).(pr0 (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t2)) t)))))))))))))))))))
\def
 \lambda (b: B).(\lambda (_: (not (eq B b Abst))).(\lambda (v1: T).(\lambda 
(v2: T).(\lambda (x0: T).(\lambda (H0: (pr0 v1 x0)).(\lambda (H1: (pr0 v2 
x0)).(\lambda (u1: T).(\lambda (u2: T).(\lambda (x1: T).(\lambda (H2: (pr0 u1 
x1)).(\lambda (H3: (pr0 u2 x1)).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(x2: T).(\lambda (H4: (pr0 t1 x2)).(\lambda (H5: (pr0 t2 x2)).(ex_intro2 T 
(\lambda (t: T).(pr0 (THead (Bind b) u1 (THead (Flat Appl) (lift (S O) O v1) 
t1)) t)) (\lambda (t: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t2)) t)) (THead (Bind b) x1 (THead (Flat Appl) (lift (S O) O x0) 
x2)) (pr0_comp u1 x1 H2 (THead (Flat Appl) (lift (S O) O v1) t1) (THead (Flat 
Appl) (lift (S O) O x0) x2) (pr0_comp (lift (S O) O v1) (lift (S O) O x0) 
(pr0_lift v1 x0 H0 (S O) O) t1 x2 H4 (Flat Appl)) (Bind b)) (pr0_comp u2 x1 
H3 (THead (Flat Appl) (lift (S O) O v2) t2) (THead (Flat Appl) (lift (S O) O 
x0) x2) (pr0_comp (lift (S O) O v2) (lift (S O) O x0) (pr0_lift v2 x0 H1 (S 
O) O) t2 x2 H5 (Flat Appl)) (Bind b))))))))))))))))))).
(* COMMENTS
Initial nodes: 347
END *)

theorem pr0_confluence__pr0_delta_delta:
 \forall (u2: T).(\forall (t3: T).(\forall (w: T).((subst0 O u2 t3 w) \to 
(\forall (u3: T).(\forall (t5: T).(\forall (w0: T).((subst0 O u3 t5 w0) \to 
(\forall (x: T).((pr0 u2 x) \to ((pr0 u3 x) \to (\forall (x0: T).((pr0 t3 x0) 
\to ((pr0 t5 x0) \to (ex2 T (\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) t)) 
(\lambda (t: T).(pr0 (THead (Bind Abbr) u3 w0) t))))))))))))))))
\def
 \lambda (u2: T).(\lambda (t3: T).(\lambda (w: T).(\lambda (H: (subst0 O u2 
t3 w)).(\lambda (u3: T).(\lambda (t5: T).(\lambda (w0: T).(\lambda (H0: 
(subst0 O u3 t5 w0)).(\lambda (x: T).(\lambda (H1: (pr0 u2 x)).(\lambda (H2: 
(pr0 u3 x)).(\lambda (x0: T).(\lambda (H3: (pr0 t3 x0)).(\lambda (H4: (pr0 t5 
x0)).(or_ind (pr0 w0 x0) (ex2 T (\lambda (w2: T).(pr0 w0 w2)) (\lambda (w2: 
T).(subst0 O x x0 w2))) (ex2 T (\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) 
t)) (\lambda (t: T).(pr0 (THead (Bind Abbr) u3 w0) t))) (\lambda (H5: (pr0 w0 
x0)).(or_ind (pr0 w x0) (ex2 T (\lambda (w2: T).(pr0 w w2)) (\lambda (w2: 
T).(subst0 O x x0 w2))) (ex2 T (\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) 
t)) (\lambda (t: T).(pr0 (THead (Bind Abbr) u3 w0) t))) (\lambda (H6: (pr0 w 
x0)).(ex_intro2 T (\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) t)) (\lambda 
(t: T).(pr0 (THead (Bind Abbr) u3 w0) t)) (THead (Bind Abbr) x x0) (pr0_comp 
u2 x H1 w x0 H6 (Bind Abbr)) (pr0_comp u3 x H2 w0 x0 H5 (Bind Abbr)))) 
(\lambda (H6: (ex2 T (\lambda (w2: T).(pr0 w w2)) (\lambda (w2: T).(subst0 O 
x x0 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 w w2)) (\lambda (w2: T).(subst0 
O x x0 w2)) (ex2 T (\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) t)) (\lambda 
(t: T).(pr0 (THead (Bind Abbr) u3 w0) t))) (\lambda (x1: T).(\lambda (H7: 
(pr0 w x1)).(\lambda (H8: (subst0 O x x0 x1)).(ex_intro2 T (\lambda (t: 
T).(pr0 (THead (Bind Abbr) u2 w) t)) (\lambda (t: T).(pr0 (THead (Bind Abbr) 
u3 w0) t)) (THead (Bind Abbr) x x1) (pr0_comp u2 x H1 w x1 H7 (Bind Abbr)) 
(pr0_delta u3 x H2 w0 x0 H5 x1 H8))))) H6)) (pr0_subst0 t3 x0 H3 u2 w O H x 
H1))) (\lambda (H5: (ex2 T (\lambda (w2: T).(pr0 w0 w2)) (\lambda (w2: 
T).(subst0 O x x0 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 w0 w2)) (\lambda 
(w2: T).(subst0 O x x0 w2)) (ex2 T (\lambda (t: T).(pr0 (THead (Bind Abbr) u2 
w) t)) (\lambda (t: T).(pr0 (THead (Bind Abbr) u3 w0) t))) (\lambda (x1: 
T).(\lambda (H6: (pr0 w0 x1)).(\lambda (H7: (subst0 O x x0 x1)).(or_ind (pr0 
w x0) (ex2 T (\lambda (w2: T).(pr0 w w2)) (\lambda (w2: T).(subst0 O x x0 
w2))) (ex2 T (\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) t)) (\lambda (t: 
T).(pr0 (THead (Bind Abbr) u3 w0) t))) (\lambda (H8: (pr0 w x0)).(ex_intro2 T 
(\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) t)) (\lambda (t: T).(pr0 (THead 
(Bind Abbr) u3 w0) t)) (THead (Bind Abbr) x x1) (pr0_delta u2 x H1 w x0 H8 x1 
H7) (pr0_comp u3 x H2 w0 x1 H6 (Bind Abbr)))) (\lambda (H8: (ex2 T (\lambda 
(w2: T).(pr0 w w2)) (\lambda (w2: T).(subst0 O x x0 w2)))).(ex2_ind T 
(\lambda (w2: T).(pr0 w w2)) (\lambda (w2: T).(subst0 O x x0 w2)) (ex2 T 
(\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) t)) (\lambda (t: T).(pr0 (THead 
(Bind Abbr) u3 w0) t))) (\lambda (x2: T).(\lambda (H9: (pr0 w x2)).(\lambda 
(H10: (subst0 O x x0 x2)).(or4_ind (eq T x2 x1) (ex2 T (\lambda (t: 
T).(subst0 O x x2 t)) (\lambda (t: T).(subst0 O x x1 t))) (subst0 O x x2 x1) 
(subst0 O x x1 x2) (ex2 T (\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) t)) 
(\lambda (t: T).(pr0 (THead (Bind Abbr) u3 w0) t))) (\lambda (H11: (eq T x2 
x1)).(let H12 \def (eq_ind T x2 (\lambda (t: T).(pr0 w t)) H9 x1 H11) in 
(ex_intro2 T (\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) t)) (\lambda (t: 
T).(pr0 (THead (Bind Abbr) u3 w0) t)) (THead (Bind Abbr) x x1) (pr0_comp u2 x 
H1 w x1 H12 (Bind Abbr)) (pr0_comp u3 x H2 w0 x1 H6 (Bind Abbr))))) (\lambda 
(H11: (ex2 T (\lambda (t: T).(subst0 O x x2 t)) (\lambda (t: T).(subst0 O x 
x1 t)))).(ex2_ind T (\lambda (t: T).(subst0 O x x2 t)) (\lambda (t: 
T).(subst0 O x x1 t)) (ex2 T (\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) 
t)) (\lambda (t: T).(pr0 (THead (Bind Abbr) u3 w0) t))) (\lambda (x3: 
T).(\lambda (H12: (subst0 O x x2 x3)).(\lambda (H13: (subst0 O x x1 
x3)).(ex_intro2 T (\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) t)) (\lambda 
(t: T).(pr0 (THead (Bind Abbr) u3 w0) t)) (THead (Bind Abbr) x x3) (pr0_delta 
u2 x H1 w x2 H9 x3 H12) (pr0_delta u3 x H2 w0 x1 H6 x3 H13))))) H11)) 
(\lambda (H11: (subst0 O x x2 x1)).(ex_intro2 T (\lambda (t: T).(pr0 (THead 
(Bind Abbr) u2 w) t)) (\lambda (t: T).(pr0 (THead (Bind Abbr) u3 w0) t)) 
(THead (Bind Abbr) x x1) (pr0_delta u2 x H1 w x2 H9 x1 H11) (pr0_comp u3 x H2 
w0 x1 H6 (Bind Abbr)))) (\lambda (H11: (subst0 O x x1 x2)).(ex_intro2 T 
(\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) t)) (\lambda (t: T).(pr0 (THead 
(Bind Abbr) u3 w0) t)) (THead (Bind Abbr) x x2) (pr0_comp u2 x H1 w x2 H9 
(Bind Abbr)) (pr0_delta u3 x H2 w0 x1 H6 x2 H11))) (subst0_confluence_eq x0 
x2 x O H10 x1 H7))))) H8)) (pr0_subst0 t3 x0 H3 u2 w O H x H1))))) H5)) 
(pr0_subst0 t5 x0 H4 u3 w0 O H0 x H2))))))))))))))).
(* COMMENTS
Initial nodes: 1501
END *)

theorem pr0_confluence__pr0_delta_tau:
 \forall (u2: T).(\forall (t3: T).(\forall (w: T).((subst0 O u2 t3 w) \to 
(\forall (t4: T).((pr0 (lift (S O) O t4) t3) \to (\forall (t2: T).(ex2 T 
(\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) t)) (\lambda (t: T).(pr0 t2 
t)))))))))
\def
 \lambda (u2: T).(\lambda (t3: T).(\lambda (w: T).(\lambda (H: (subst0 O u2 
t3 w)).(\lambda (t4: T).(\lambda (H0: (pr0 (lift (S O) O t4) t3)).(\lambda 
(t2: T).(ex2_ind T (\lambda (t5: T).(eq T t3 (lift (S O) O t5))) (\lambda 
(t5: T).(pr0 t4 t5)) (ex2 T (\lambda (t: T).(pr0 (THead (Bind Abbr) u2 w) t)) 
(\lambda (t: T).(pr0 t2 t))) (\lambda (x: T).(\lambda (H1: (eq T t3 (lift (S 
O) O x))).(\lambda (_: (pr0 t4 x)).(let H3 \def (eq_ind T t3 (\lambda (t: 
T).(subst0 O u2 t w)) H (lift (S O) O x) H1) in (subst0_gen_lift_false x u2 w 
(S O) O O (le_n O) (eq_ind_r nat (plus (S O) O) (\lambda (n: nat).(lt O n)) 
(le_n (plus (S O) O)) (plus O (S O)) (plus_sym O (S O))) H3 (ex2 T (\lambda 
(t: T).(pr0 (THead (Bind Abbr) u2 w) t)) (\lambda (t: T).(pr0 t2 t)))))))) 
(pr0_gen_lift t4 t3 (S O) O H0)))))))).
(* COMMENTS
Initial nodes: 257
END *)

theorem pr0_confluence:
 \forall (t0: T).(\forall (t1: T).((pr0 t0 t1) \to (\forall (t2: T).((pr0 t0 
t2) \to (ex2 T (\lambda (t: T).(pr0 t1 t)) (\lambda (t: T).(pr0 t2 t)))))))
\def
 \lambda (t0: T).(tlt_wf_ind (\lambda (t: T).(\forall (t1: T).((pr0 t t1) \to 
(\forall (t2: T).((pr0 t t2) \to (ex2 T (\lambda (t3: T).(pr0 t1 t3)) 
(\lambda (t3: T).(pr0 t2 t3)))))))) (\lambda (t: T).(\lambda (H: ((\forall 
(v: T).((tlt v t) \to (\forall (t1: T).((pr0 v t1) \to (\forall (t2: T).((pr0 
v t2) \to (ex2 T (\lambda (t3: T).(pr0 t1 t3)) (\lambda (t3: T).(pr0 t2 
t3))))))))))).(\lambda (t1: T).(\lambda (H0: (pr0 t t1)).(\lambda (t2: 
T).(\lambda (H1: (pr0 t t2)).(let H2 \def (match H0 in pr0 return (\lambda 
(t3: T).(\lambda (t4: T).(\lambda (_: (pr0 t3 t4)).((eq T t3 t) \to ((eq T t4 
t1) \to (ex2 T (\lambda (t5: T).(pr0 t1 t5)) (\lambda (t5: T).(pr0 t2 
t5)))))))) with [(pr0_refl t3) \Rightarrow (\lambda (H2: (eq T t3 
t)).(\lambda (H3: (eq T t3 t1)).(eq_ind T t (\lambda (t4: T).((eq T t4 t1) 
\to (ex2 T (\lambda (t5: T).(pr0 t1 t5)) (\lambda (t5: T).(pr0 t2 t5))))) 
(\lambda (H4: (eq T t t1)).(eq_ind T t1 (\lambda (_: T).(ex2 T (\lambda (t5: 
T).(pr0 t1 t5)) (\lambda (t5: T).(pr0 t2 t5)))) (let H5 \def (match H1 in pr0 
return (\lambda (t4: T).(\lambda (t5: T).(\lambda (_: (pr0 t4 t5)).((eq T t4 
t) \to ((eq T t5 t2) \to (ex2 T (\lambda (t6: T).(pr0 t1 t6)) (\lambda (t6: 
T).(pr0 t2 t6)))))))) with [(pr0_refl t4) \Rightarrow (\lambda (H5: (eq T t4 
t)).(\lambda (H6: (eq T t4 t2)).(eq_ind T t (\lambda (t5: T).((eq T t5 t2) 
\to (ex2 T (\lambda (t6: T).(pr0 t1 t6)) (\lambda (t6: T).(pr0 t2 t6))))) 
(\lambda (H7: (eq T t t2)).(eq_ind T t2 (\lambda (_: T).(ex2 T (\lambda (t6: 
T).(pr0 t1 t6)) (\lambda (t6: T).(pr0 t2 t6)))) (let H8 \def (eq_ind T t 
(\lambda (t5: T).(eq T t4 t5)) H5 t2 H7) in (let H9 \def (eq_ind T t (\lambda 
(t5: T).(eq T t5 t1)) H4 t2 H7) in (let H10 \def (eq_ind T t (\lambda (t5: 
T).(eq T t3 t5)) H2 t2 H7) in (let H11 \def (eq_ind T t (\lambda (t5: 
T).(\forall (v: T).((tlt v t5) \to (\forall (t6: T).((pr0 v t6) \to (\forall 
(t7: T).((pr0 v t7) \to (ex2 T (\lambda (t8: T).(pr0 t6 t8)) (\lambda (t8: 
T).(pr0 t7 t8)))))))))) H t2 H7) in (let H12 \def (eq_ind T t2 (\lambda (t5: 
T).(\forall (v: T).((tlt v t5) \to (\forall (t6: T).((pr0 v t6) \to (\forall 
(t7: T).((pr0 v t7) \to (ex2 T (\lambda (t8: T).(pr0 t6 t8)) (\lambda (t8: 
T).(pr0 t7 t8)))))))))) H11 t1 H9) in (eq_ind_r T t1 (\lambda (t5: T).(ex2 T 
(\lambda (t6: T).(pr0 t1 t6)) (\lambda (t6: T).(pr0 t5 t6)))) (let H13 \def 
(eq_ind T t2 (\lambda (t5: T).(eq T t3 t5)) H10 t1 H9) in (ex_intro2 T 
(\lambda (t5: T).(pr0 t1 t5)) (\lambda (t5: T).(pr0 t1 t5)) t1 (pr0_refl t1) 
(pr0_refl t1))) t2 H9)))))) t (sym_eq T t t2 H7))) t4 (sym_eq T t4 t H5) 
H6))) | (pr0_comp u1 u2 H5 t4 t5 H6 k) \Rightarrow (\lambda (H7: (eq T (THead 
k u1 t4) t)).(\lambda (H8: (eq T (THead k u2 t5) t2)).(eq_ind T (THead k u1 
t4) (\lambda (_: T).((eq T (THead k u2 t5) t2) \to ((pr0 u1 u2) \to ((pr0 t4 
t5) \to (ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t2 
t7))))))) (\lambda (H9: (eq T (THead k u2 t5) t2)).(eq_ind T (THead k u2 t5) 
(\lambda (t6: T).((pr0 u1 u2) \to ((pr0 t4 t5) \to (ex2 T (\lambda (t7: 
T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t6 t7)))))) (\lambda (H10: (pr0 u1 
u2)).(\lambda (H11: (pr0 t4 t5)).(let H12 \def (eq_ind_r T t (\lambda (t6: 
T).(eq T t6 t1)) H4 (THead k u1 t4) H7) in (eq_ind T (THead k u1 t4) (\lambda 
(t6: T).(ex2 T (\lambda (t7: T).(pr0 t6 t7)) (\lambda (t7: T).(pr0 (THead k 
u2 t5) t7)))) (let H13 \def (eq_ind_r T t (\lambda (t6: T).(eq T t3 t6)) H2 
(THead k u1 t4) H7) in (let H14 \def (eq_ind_r T t (\lambda (t6: T).(\forall 
(v: T).((tlt v t6) \to (\forall (t7: T).((pr0 v t7) \to (\forall (t8: 
T).((pr0 v t8) \to (ex2 T (\lambda (t9: T).(pr0 t7 t9)) (\lambda (t9: T).(pr0 
t8 t9)))))))))) H (THead k u1 t4) H7) in (ex_intro2 T (\lambda (t6: T).(pr0 
(THead k u1 t4) t6)) (\lambda (t6: T).(pr0 (THead k u2 t5) t6)) (THead k u2 
t5) (pr0_comp u1 u2 H10 t4 t5 H11 k) (pr0_refl (THead k u2 t5))))) t1 H12)))) 
t2 H9)) t H7 H8 H5 H6))) | (pr0_beta u v1 v2 H5 t4 t5 H6) \Rightarrow 
(\lambda (H7: (eq T (THead (Flat Appl) v1 (THead (Bind Abst) u t4)) 
t)).(\lambda (H8: (eq T (THead (Bind Abbr) v2 t5) t2)).(eq_ind T (THead (Flat 
Appl) v1 (THead (Bind Abst) u t4)) (\lambda (_: T).((eq T (THead (Bind Abbr) 
v2 t5) t2) \to ((pr0 v1 v2) \to ((pr0 t4 t5) \to (ex2 T (\lambda (t7: T).(pr0 
t1 t7)) (\lambda (t7: T).(pr0 t2 t7))))))) (\lambda (H9: (eq T (THead (Bind 
Abbr) v2 t5) t2)).(eq_ind T (THead (Bind Abbr) v2 t5) (\lambda (t6: T).((pr0 
v1 v2) \to ((pr0 t4 t5) \to (ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda 
(t7: T).(pr0 t6 t7)))))) (\lambda (H10: (pr0 v1 v2)).(\lambda (H11: (pr0 t4 
t5)).(let H12 \def (eq_ind_r T t (\lambda (t6: T).(eq T t6 t1)) H4 (THead 
(Flat Appl) v1 (THead (Bind Abst) u t4)) H7) in (eq_ind T (THead (Flat Appl) 
v1 (THead (Bind Abst) u t4)) (\lambda (t6: T).(ex2 T (\lambda (t7: T).(pr0 t6 
t7)) (\lambda (t7: T).(pr0 (THead (Bind Abbr) v2 t5) t7)))) (let H13 \def 
(eq_ind_r T t (\lambda (t6: T).(eq T t3 t6)) H2 (THead (Flat Appl) v1 (THead 
(Bind Abst) u t4)) H7) in (let H14 \def (eq_ind_r T t (\lambda (t6: 
T).(\forall (v: T).((tlt v t6) \to (\forall (t7: T).((pr0 v t7) \to (\forall 
(t8: T).((pr0 v t8) \to (ex2 T (\lambda (t9: T).(pr0 t7 t9)) (\lambda (t9: 
T).(pr0 t8 t9)))))))))) H (THead (Flat Appl) v1 (THead (Bind Abst) u t4)) H7) 
in (ex_intro2 T (\lambda (t6: T).(pr0 (THead (Flat Appl) v1 (THead (Bind 
Abst) u t4)) t6)) (\lambda (t6: T).(pr0 (THead (Bind Abbr) v2 t5) t6)) (THead 
(Bind Abbr) v2 t5) (pr0_beta u v1 v2 H10 t4 t5 H11) (pr0_refl (THead (Bind 
Abbr) v2 t5))))) t1 H12)))) t2 H9)) t H7 H8 H5 H6))) | (pr0_upsilon b H5 v1 
v2 H6 u1 u2 H7 t4 t5 H8) \Rightarrow (\lambda (H9: (eq T (THead (Flat Appl) 
v1 (THead (Bind b) u1 t4)) t)).(\lambda (H10: (eq T (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t5)) t2)).(eq_ind T (THead (Flat Appl) v1 
(THead (Bind b) u1 t4)) (\lambda (_: T).((eq T (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t5)) t2) \to ((not (eq B b Abst)) \to ((pr0 v1 
v2) \to ((pr0 u1 u2) \to ((pr0 t4 t5) \to (ex2 T (\lambda (t7: T).(pr0 t1 
t7)) (\lambda (t7: T).(pr0 t2 t7))))))))) (\lambda (H11: (eq T (THead (Bind 
b) u2 (THead (Flat Appl) (lift (S O) O v2) t5)) t2)).(eq_ind T (THead (Bind 
b) u2 (THead (Flat Appl) (lift (S O) O v2) t5)) (\lambda (t6: T).((not (eq B 
b Abst)) \to ((pr0 v1 v2) \to ((pr0 u1 u2) \to ((pr0 t4 t5) \to (ex2 T 
(\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t6 t7)))))))) (\lambda 
(H12: (not (eq B b Abst))).(\lambda (H13: (pr0 v1 v2)).(\lambda (H14: (pr0 u1 
u2)).(\lambda (H15: (pr0 t4 t5)).(let H16 \def (eq_ind_r T t (\lambda (t6: 
T).(eq T t6 t1)) H4 (THead (Flat Appl) v1 (THead (Bind b) u1 t4)) H9) in 
(eq_ind T (THead (Flat Appl) v1 (THead (Bind b) u1 t4)) (\lambda (t6: T).(ex2 
T (\lambda (t7: T).(pr0 t6 t7)) (\lambda (t7: T).(pr0 (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t5)) t7)))) (let H17 \def (eq_ind_r T t 
(\lambda (t6: T).(eq T t3 t6)) H2 (THead (Flat Appl) v1 (THead (Bind b) u1 
t4)) H9) in (let H18 \def (eq_ind_r T t (\lambda (t6: T).(\forall (v: 
T).((tlt v t6) \to (\forall (t7: T).((pr0 v t7) \to (\forall (t8: T).((pr0 v 
t8) \to (ex2 T (\lambda (t9: T).(pr0 t7 t9)) (\lambda (t9: T).(pr0 t8 
t9)))))))))) H (THead (Flat Appl) v1 (THead (Bind b) u1 t4)) H9) in 
(pr0_confluence__pr0_cong_upsilon_refl b H12 u1 u2 H14 t4 t5 H15 v1 v2 v2 H13 
(pr0_refl v2)))) t1 H16)))))) t2 H11)) t H9 H10 H5 H6 H7 H8))) | (pr0_delta 
u1 u2 H5 t4 t5 H6 w H7) \Rightarrow (\lambda (H8: (eq T (THead (Bind Abbr) u1 
t4) t)).(\lambda (H9: (eq T (THead (Bind Abbr) u2 w) t2)).(eq_ind T (THead 
(Bind Abbr) u1 t4) (\lambda (_: T).((eq T (THead (Bind Abbr) u2 w) t2) \to 
((pr0 u1 u2) \to ((pr0 t4 t5) \to ((subst0 O u2 t5 w) \to (ex2 T (\lambda 
(t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t2 t7)))))))) (\lambda (H10: (eq T 
(THead (Bind Abbr) u2 w) t2)).(eq_ind T (THead (Bind Abbr) u2 w) (\lambda 
(t6: T).((pr0 u1 u2) \to ((pr0 t4 t5) \to ((subst0 O u2 t5 w) \to (ex2 T 
(\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t6 t7))))))) (\lambda 
(H11: (pr0 u1 u2)).(\lambda (H12: (pr0 t4 t5)).(\lambda (H13: (subst0 O u2 t5 
w)).(let H14 \def (eq_ind_r T t (\lambda (t6: T).(eq T t6 t1)) H4 (THead 
(Bind Abbr) u1 t4) H8) in (eq_ind T (THead (Bind Abbr) u1 t4) (\lambda (t6: 
T).(ex2 T (\lambda (t7: T).(pr0 t6 t7)) (\lambda (t7: T).(pr0 (THead (Bind 
Abbr) u2 w) t7)))) (let H15 \def (eq_ind_r T t (\lambda (t6: T).(eq T t3 t6)) 
H2 (THead (Bind Abbr) u1 t4) H8) in (let H16 \def (eq_ind_r T t (\lambda (t6: 
T).(\forall (v: T).((tlt v t6) \to (\forall (t7: T).((pr0 v t7) \to (\forall 
(t8: T).((pr0 v t8) \to (ex2 T (\lambda (t9: T).(pr0 t7 t9)) (\lambda (t9: 
T).(pr0 t8 t9)))))))))) H (THead (Bind Abbr) u1 t4) H8) in (ex_intro2 T 
(\lambda (t6: T).(pr0 (THead (Bind Abbr) u1 t4) t6)) (\lambda (t6: T).(pr0 
(THead (Bind Abbr) u2 w) t6)) (THead (Bind Abbr) u2 w) (pr0_delta u1 u2 H11 
t4 t5 H12 w H13) (pr0_refl (THead (Bind Abbr) u2 w))))) t1 H14))))) t2 H10)) 
t H8 H9 H5 H6 H7))) | (pr0_zeta b H5 t4 t5 H6 u) \Rightarrow (\lambda (H7: 
(eq T (THead (Bind b) u (lift (S O) O t4)) t)).(\lambda (H8: (eq T t5 
t2)).(eq_ind T (THead (Bind b) u (lift (S O) O t4)) (\lambda (_: T).((eq T t5 
t2) \to ((not (eq B b Abst)) \to ((pr0 t4 t5) \to (ex2 T (\lambda (t7: 
T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t2 t7))))))) (\lambda (H9: (eq T t5 
t2)).(eq_ind T t2 (\lambda (t6: T).((not (eq B b Abst)) \to ((pr0 t4 t6) \to 
(ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t2 t7)))))) 
(\lambda (H10: (not (eq B b Abst))).(\lambda (H11: (pr0 t4 t2)).(let H12 \def 
(eq_ind_r T t (\lambda (t6: T).(eq T t6 t1)) H4 (THead (Bind b) u (lift (S O) 
O t4)) H7) in (eq_ind T (THead (Bind b) u (lift (S O) O t4)) (\lambda (t6: 
T).(ex2 T (\lambda (t7: T).(pr0 t6 t7)) (\lambda (t7: T).(pr0 t2 t7)))) (let 
H13 \def (eq_ind_r T t (\lambda (t6: T).(eq T t3 t6)) H2 (THead (Bind b) u 
(lift (S O) O t4)) H7) in (let H14 \def (eq_ind_r T t (\lambda (t6: 
T).(\forall (v: T).((tlt v t6) \to (\forall (t7: T).((pr0 v t7) \to (\forall 
(t8: T).((pr0 v t8) \to (ex2 T (\lambda (t9: T).(pr0 t7 t9)) (\lambda (t9: 
T).(pr0 t8 t9)))))))))) H (THead (Bind b) u (lift (S O) O t4)) H7) in 
(ex_intro2 T (\lambda (t6: T).(pr0 (THead (Bind b) u (lift (S O) O t4)) t6)) 
(\lambda (t6: T).(pr0 t2 t6)) t2 (pr0_zeta b H10 t4 t2 H11 u) (pr0_refl 
t2)))) t1 H12)))) t5 (sym_eq T t5 t2 H9))) t H7 H8 H5 H6))) | (pr0_tau t4 t5 
H5 u) \Rightarrow (\lambda (H6: (eq T (THead (Flat Cast) u t4) t)).(\lambda 
(H7: (eq T t5 t2)).(eq_ind T (THead (Flat Cast) u t4) (\lambda (_: T).((eq T 
t5 t2) \to ((pr0 t4 t5) \to (ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda 
(t7: T).(pr0 t2 t7)))))) (\lambda (H8: (eq T t5 t2)).(eq_ind T t2 (\lambda 
(t6: T).((pr0 t4 t6) \to (ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: 
T).(pr0 t2 t7))))) (\lambda (H9: (pr0 t4 t2)).(let H10 \def (eq_ind_r T t 
(\lambda (t6: T).(eq T t6 t1)) H4 (THead (Flat Cast) u t4) H6) in (eq_ind T 
(THead (Flat Cast) u t4) (\lambda (t6: T).(ex2 T (\lambda (t7: T).(pr0 t6 
t7)) (\lambda (t7: T).(pr0 t2 t7)))) (let H11 \def (eq_ind_r T t (\lambda 
(t6: T).(eq T t3 t6)) H2 (THead (Flat Cast) u t4) H6) in (let H12 \def 
(eq_ind_r T t (\lambda (t6: T).(\forall (v: T).((tlt v t6) \to (\forall (t7: 
T).((pr0 v t7) \to (\forall (t8: T).((pr0 v t8) \to (ex2 T (\lambda (t9: 
T).(pr0 t7 t9)) (\lambda (t9: T).(pr0 t8 t9)))))))))) H (THead (Flat Cast) u 
t4) H6) in (ex_intro2 T (\lambda (t6: T).(pr0 (THead (Flat Cast) u t4) t6)) 
(\lambda (t6: T).(pr0 t2 t6)) t2 (pr0_tau t4 t2 H9 u) (pr0_refl t2)))) t1 
H10))) t5 (sym_eq T t5 t2 H8))) t H6 H7 H5)))]) in (H5 (refl_equal T t) 
(refl_equal T t2))) t (sym_eq T t t1 H4))) t3 (sym_eq T t3 t H2) H3))) | 
(pr0_comp u1 u2 H2 t3 t4 H3 k) \Rightarrow (\lambda (H4: (eq T (THead k u1 
t3) t)).(\lambda (H5: (eq T (THead k u2 t4) t1)).(eq_ind T (THead k u1 t3) 
(\lambda (_: T).((eq T (THead k u2 t4) t1) \to ((pr0 u1 u2) \to ((pr0 t3 t4) 
\to (ex2 T (\lambda (t6: T).(pr0 t1 t6)) (\lambda (t6: T).(pr0 t2 t6))))))) 
(\lambda (H6: (eq T (THead k u2 t4) t1)).(eq_ind T (THead k u2 t4) (\lambda 
(t5: T).((pr0 u1 u2) \to ((pr0 t3 t4) \to (ex2 T (\lambda (t6: T).(pr0 t5 
t6)) (\lambda (t6: T).(pr0 t2 t6)))))) (\lambda (H7: (pr0 u1 u2)).(\lambda 
(H8: (pr0 t3 t4)).(let H9 \def (match H1 in pr0 return (\lambda (t5: 
T).(\lambda (t6: T).(\lambda (_: (pr0 t5 t6)).((eq T t5 t) \to ((eq T t6 t2) 
\to (ex2 T (\lambda (t7: T).(pr0 (THead k u2 t4) t7)) (\lambda (t7: T).(pr0 
t2 t7)))))))) with [(pr0_refl t5) \Rightarrow (\lambda (H9: (eq T t5 
t)).(\lambda (H10: (eq T t5 t2)).(eq_ind T t (\lambda (t6: T).((eq T t6 t2) 
\to (ex2 T (\lambda (t7: T).(pr0 (THead k u2 t4) t7)) (\lambda (t7: T).(pr0 
t2 t7))))) (\lambda (H11: (eq T t t2)).(eq_ind T t2 (\lambda (_: T).(ex2 T 
(\lambda (t7: T).(pr0 (THead k u2 t4) t7)) (\lambda (t7: T).(pr0 t2 t7)))) 
(let H12 \def (eq_ind_r T t (\lambda (t6: T).(eq T t6 t2)) H11 (THead k u1 
t3) H4) in (eq_ind T (THead k u1 t3) (\lambda (t6: T).(ex2 T (\lambda (t7: 
T).(pr0 (THead k u2 t4) t7)) (\lambda (t7: T).(pr0 t6 t7)))) (let H13 \def 
(eq_ind_r T t (\lambda (t6: T).(eq T t5 t6)) H9 (THead k u1 t3) H4) in (let 
H14 \def (eq_ind_r T t (\lambda (t6: T).(\forall (v: T).((tlt v t6) \to 
(\forall (t7: T).((pr0 v t7) \to (\forall (t8: T).((pr0 v t8) \to (ex2 T 
(\lambda (t9: T).(pr0 t7 t9)) (\lambda (t9: T).(pr0 t8 t9)))))))))) H (THead 
k u1 t3) H4) in (ex_intro2 T (\lambda (t6: T).(pr0 (THead k u2 t4) t6)) 
(\lambda (t6: T).(pr0 (THead k u1 t3) t6)) (THead k u2 t4) (pr0_refl (THead k 
u2 t4)) (pr0_comp u1 u2 H7 t3 t4 H8 k)))) t2 H12)) t (sym_eq T t t2 H11))) t5 
(sym_eq T t5 t H9) H10))) | (pr0_comp u0 u3 H9 t5 t6 H10 k0) \Rightarrow 
(\lambda (H11: (eq T (THead k0 u0 t5) t)).(\lambda (H12: (eq T (THead k0 u3 
t6) t2)).(eq_ind T (THead k0 u0 t5) (\lambda (_: T).((eq T (THead k0 u3 t6) 
t2) \to ((pr0 u0 u3) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead 
k u2 t4) t8)) (\lambda (t8: T).(pr0 t2 t8))))))) (\lambda (H13: (eq T (THead 
k0 u3 t6) t2)).(eq_ind T (THead k0 u3 t6) (\lambda (t7: T).((pr0 u0 u3) \to 
((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead k u2 t4) t8)) (\lambda 
(t8: T).(pr0 t7 t8)))))) (\lambda (H14: (pr0 u0 u3)).(\lambda (H15: (pr0 t5 
t6)).(let H16 \def (eq_ind_r T t (\lambda (t7: T).(eq T (THead k u1 t3) t7)) 
H4 (THead k0 u0 t5) H11) in (let H17 \def (f_equal T K (\lambda (e: T).(match 
e in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k1 _ _) \Rightarrow k1])) (THead k u1 t3) (THead k0 u0 
t5) H16) in ((let H18 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow u1 | (TLRef _) \Rightarrow u1 
| (THead _ t7 _) \Rightarrow t7])) (THead k u1 t3) (THead k0 u0 t5) H16) in 
((let H19 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead _ _ 
t7) \Rightarrow t7])) (THead k u1 t3) (THead k0 u0 t5) H16) in (\lambda (H20: 
(eq T u1 u0)).(\lambda (H21: (eq K k k0)).(let H22 \def (eq_ind_r T t 
(\lambda (t7: T).(\forall (v: T).((tlt v t7) \to (\forall (t8: T).((pr0 v t8) 
\to (\forall (t9: T).((pr0 v t9) \to (ex2 T (\lambda (t10: T).(pr0 t8 t10)) 
(\lambda (t10: T).(pr0 t9 t10)))))))))) H (THead k0 u0 t5) H11) in (eq_ind_r 
K k0 (\lambda (k1: K).(ex2 T (\lambda (t7: T).(pr0 (THead k1 u2 t4) t7)) 
(\lambda (t7: T).(pr0 (THead k0 u3 t6) t7)))) (let H23 \def (eq_ind T u1 
(\lambda (t7: T).(pr0 t7 u2)) H7 u0 H20) in (let H24 \def (eq_ind T t3 
(\lambda (t7: T).(pr0 t7 t4)) H8 t5 H19) in (ex2_ind T (\lambda (t7: T).(pr0 
t4 t7)) (\lambda (t7: T).(pr0 t6 t7)) (ex2 T (\lambda (t7: T).(pr0 (THead k0 
u2 t4) t7)) (\lambda (t7: T).(pr0 (THead k0 u3 t6) t7))) (\lambda (x: 
T).(\lambda (H25: (pr0 t4 x)).(\lambda (H26: (pr0 t6 x)).(ex2_ind T (\lambda 
(t7: T).(pr0 u2 t7)) (\lambda (t7: T).(pr0 u3 t7)) (ex2 T (\lambda (t7: 
T).(pr0 (THead k0 u2 t4) t7)) (\lambda (t7: T).(pr0 (THead k0 u3 t6) t7))) 
(\lambda (x0: T).(\lambda (H27: (pr0 u2 x0)).(\lambda (H28: (pr0 u3 
x0)).(ex_intro2 T (\lambda (t7: T).(pr0 (THead k0 u2 t4) t7)) (\lambda (t7: 
T).(pr0 (THead k0 u3 t6) t7)) (THead k0 x0 x) (pr0_comp u2 x0 H27 t4 x H25 
k0) (pr0_comp u3 x0 H28 t6 x H26 k0))))) (H22 u0 (tlt_head_sx k0 u0 t5) u2 
H23 u3 H14))))) (H22 t5 (tlt_head_dx k0 u0 t5) t4 H24 t6 H15)))) k H21))))) 
H18)) H17))))) t2 H13)) t H11 H12 H9 H10))) | (pr0_beta u v1 v2 H9 t5 t6 H10) 
\Rightarrow (\lambda (H11: (eq T (THead (Flat Appl) v1 (THead (Bind Abst) u 
t5)) t)).(\lambda (H12: (eq T (THead (Bind Abbr) v2 t6) t2)).(eq_ind T (THead 
(Flat Appl) v1 (THead (Bind Abst) u t5)) (\lambda (_: T).((eq T (THead (Bind 
Abbr) v2 t6) t2) \to ((pr0 v1 v2) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: 
T).(pr0 (THead k u2 t4) t8)) (\lambda (t8: T).(pr0 t2 t8))))))) (\lambda 
(H13: (eq T (THead (Bind Abbr) v2 t6) t2)).(eq_ind T (THead (Bind Abbr) v2 
t6) (\lambda (t7: T).((pr0 v1 v2) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: 
T).(pr0 (THead k u2 t4) t8)) (\lambda (t8: T).(pr0 t7 t8)))))) (\lambda (H14: 
(pr0 v1 v2)).(\lambda (H15: (pr0 t5 t6)).(let H16 \def (eq_ind_r T t (\lambda 
(t7: T).(eq T (THead k u1 t3) t7)) H4 (THead (Flat Appl) v1 (THead (Bind 
Abst) u t5)) H11) in (let H17 \def (f_equal T K (\lambda (e: T).(match e in T 
return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k0 _ _) \Rightarrow k0])) (THead k u1 t3) (THead (Flat 
Appl) v1 (THead (Bind Abst) u t5)) H16) in ((let H18 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u1 | (TLRef _) \Rightarrow u1 | (THead _ t7 _) \Rightarrow t7])) 
(THead k u1 t3) (THead (Flat Appl) v1 (THead (Bind Abst) u t5)) H16) in ((let 
H19 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead _ _ t7) 
\Rightarrow t7])) (THead k u1 t3) (THead (Flat Appl) v1 (THead (Bind Abst) u 
t5)) H16) in (\lambda (H20: (eq T u1 v1)).(\lambda (H21: (eq K k (Flat 
Appl))).(let H22 \def (eq_ind_r T t (\lambda (t7: T).(\forall (v: T).((tlt v 
t7) \to (\forall (t8: T).((pr0 v t8) \to (\forall (t9: T).((pr0 v t9) \to 
(ex2 T (\lambda (t10: T).(pr0 t8 t10)) (\lambda (t10: T).(pr0 t9 
t10)))))))))) H (THead (Flat Appl) v1 (THead (Bind Abst) u t5)) H11) in 
(eq_ind_r K (Flat Appl) (\lambda (k0: K).(ex2 T (\lambda (t7: T).(pr0 (THead 
k0 u2 t4) t7)) (\lambda (t7: T).(pr0 (THead (Bind Abbr) v2 t6) t7)))) (let 
H23 \def (eq_ind T u1 (\lambda (t7: T).(pr0 t7 u2)) H7 v1 H20) in (let H24 
\def (eq_ind T t3 (\lambda (t7: T).(pr0 t7 t4)) H8 (THead (Bind Abst) u t5) 
H19) in (let H25 \def (match H24 in pr0 return (\lambda (t7: T).(\lambda (t8: 
T).(\lambda (_: (pr0 t7 t8)).((eq T t7 (THead (Bind Abst) u t5)) \to ((eq T 
t8 t4) \to (ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t4) t9)) 
(\lambda (t9: T).(pr0 (THead (Bind Abbr) v2 t6) t9)))))))) with [(pr0_refl 
t7) \Rightarrow (\lambda (H25: (eq T t7 (THead (Bind Abst) u t5))).(\lambda 
(H26: (eq T t7 t4)).(eq_ind T (THead (Bind Abst) u t5) (\lambda (t8: T).((eq 
T t8 t4) \to (ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t4) t9)) 
(\lambda (t9: T).(pr0 (THead (Bind Abbr) v2 t6) t9))))) (\lambda (H27: (eq T 
(THead (Bind Abst) u t5) t4)).(eq_ind T (THead (Bind Abst) u t5) (\lambda 
(t8: T).(ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t8) t9)) (\lambda 
(t9: T).(pr0 (THead (Bind Abbr) v2 t6) t9)))) (ex2_ind T (\lambda (t8: 
T).(pr0 u2 t8)) (\lambda (t8: T).(pr0 v2 t8)) (ex2 T (\lambda (t8: T).(pr0 
(THead (Flat Appl) u2 (THead (Bind Abst) u t5)) t8)) (\lambda (t8: T).(pr0 
(THead (Bind Abbr) v2 t6) t8))) (\lambda (x: T).(\lambda (H28: (pr0 u2 
x)).(\lambda (H29: (pr0 v2 x)).(ex_intro2 T (\lambda (t8: T).(pr0 (THead 
(Flat Appl) u2 (THead (Bind Abst) u t5)) t8)) (\lambda (t8: T).(pr0 (THead 
(Bind Abbr) v2 t6) t8)) (THead (Bind Abbr) x t6) (pr0_beta u u2 x H28 t5 t6 
H15) (pr0_comp v2 x H29 t6 t6 (pr0_refl t6) (Bind Abbr)))))) (H22 v1 
(tlt_head_sx (Flat Appl) v1 (THead (Bind Abst) u t5)) u2 H23 v2 H14)) t4 
H27)) t7 (sym_eq T t7 (THead (Bind Abst) u t5) H25) H26))) | (pr0_comp u0 u3 
H25 t7 t8 H26 k0) \Rightarrow (\lambda (H27: (eq T (THead k0 u0 t7) (THead 
(Bind Abst) u t5))).(\lambda (H28: (eq T (THead k0 u3 t8) t4)).((let H29 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow t7 | (TLRef _) \Rightarrow t7 | (THead _ _ t9) 
\Rightarrow t9])) (THead k0 u0 t7) (THead (Bind Abst) u t5) H27) in ((let H30 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead _ t9 _) 
\Rightarrow t9])) (THead k0 u0 t7) (THead (Bind Abst) u t5) H27) in ((let H31 
\def (f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) 
with [(TSort _) \Rightarrow k0 | (TLRef _) \Rightarrow k0 | (THead k1 _ _) 
\Rightarrow k1])) (THead k0 u0 t7) (THead (Bind Abst) u t5) H27) in (eq_ind K 
(Bind Abst) (\lambda (k1: K).((eq T u0 u) \to ((eq T t7 t5) \to ((eq T (THead 
k1 u3 t8) t4) \to ((pr0 u0 u3) \to ((pr0 t7 t8) \to (ex2 T (\lambda (t9: 
T).(pr0 (THead (Flat Appl) u2 t4) t9)) (\lambda (t9: T).(pr0 (THead (Bind 
Abbr) v2 t6) t9))))))))) (\lambda (H32: (eq T u0 u)).(eq_ind T u (\lambda 
(t9: T).((eq T t7 t5) \to ((eq T (THead (Bind Abst) u3 t8) t4) \to ((pr0 t9 
u3) \to ((pr0 t7 t8) \to (ex2 T (\lambda (t10: T).(pr0 (THead (Flat Appl) u2 
t4) t10)) (\lambda (t10: T).(pr0 (THead (Bind Abbr) v2 t6) t10)))))))) 
(\lambda (H33: (eq T t7 t5)).(eq_ind T t5 (\lambda (t9: T).((eq T (THead 
(Bind Abst) u3 t8) t4) \to ((pr0 u u3) \to ((pr0 t9 t8) \to (ex2 T (\lambda 
(t10: T).(pr0 (THead (Flat Appl) u2 t4) t10)) (\lambda (t10: T).(pr0 (THead 
(Bind Abbr) v2 t6) t10))))))) (\lambda (H34: (eq T (THead (Bind Abst) u3 t8) 
t4)).(eq_ind T (THead (Bind Abst) u3 t8) (\lambda (t9: T).((pr0 u u3) \to 
((pr0 t5 t8) \to (ex2 T (\lambda (t10: T).(pr0 (THead (Flat Appl) u2 t9) 
t10)) (\lambda (t10: T).(pr0 (THead (Bind Abbr) v2 t6) t10)))))) (\lambda (_: 
(pr0 u u3)).(\lambda (H36: (pr0 t5 t8)).(ex2_ind T (\lambda (t9: T).(pr0 t8 
t9)) (\lambda (t9: T).(pr0 t6 t9)) (ex2 T (\lambda (t9: T).(pr0 (THead (Flat 
Appl) u2 (THead (Bind Abst) u3 t8)) t9)) (\lambda (t9: T).(pr0 (THead (Bind 
Abbr) v2 t6) t9))) (\lambda (x: T).(\lambda (H37: (pr0 t8 x)).(\lambda (H38: 
(pr0 t6 x)).(ex2_ind T (\lambda (t9: T).(pr0 u2 t9)) (\lambda (t9: T).(pr0 v2 
t9)) (ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 (THead (Bind Abst) u3 
t8)) t9)) (\lambda (t9: T).(pr0 (THead (Bind Abbr) v2 t6) t9))) (\lambda (x0: 
T).(\lambda (H39: (pr0 u2 x0)).(\lambda (H40: (pr0 v2 x0)).(ex_intro2 T 
(\lambda (t9: T).(pr0 (THead (Flat Appl) u2 (THead (Bind Abst) u3 t8)) t9)) 
(\lambda (t9: T).(pr0 (THead (Bind Abbr) v2 t6) t9)) (THead (Bind Abbr) x0 x) 
(pr0_beta u3 u2 x0 H39 t8 x H37) (pr0_comp v2 x0 H40 t6 x H38 (Bind 
Abbr)))))) (H22 v1 (tlt_head_sx (Flat Appl) v1 (THead (Bind Abst) u t5)) u2 
H23 v2 H14))))) (H22 t5 (tlt_trans (THead (Bind Abst) u t5) t5 (THead (Flat 
Appl) v1 (THead (Bind Abst) u t5)) (tlt_head_dx (Bind Abst) u t5) 
(tlt_head_dx (Flat Appl) v1 (THead (Bind Abst) u t5))) t8 H36 t6 H15)))) t4 
H34)) t7 (sym_eq T t7 t5 H33))) u0 (sym_eq T u0 u H32))) k0 (sym_eq K k0 
(Bind Abst) H31))) H30)) H29)) H28 H25 H26))) | (pr0_beta u0 v0 v3 H25 t7 t8 
H26) \Rightarrow (\lambda (H27: (eq T (THead (Flat Appl) v0 (THead (Bind 
Abst) u0 t7)) (THead (Bind Abst) u t5))).(\lambda (H28: (eq T (THead (Bind 
Abbr) v3 t8) t4)).((let H29 \def (eq_ind T (THead (Flat Appl) v0 (THead (Bind 
Abst) u0 t7)) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k0 _ _) 
\Rightarrow (match k0 in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind Abst) u t5) 
H27) in (False_ind ((eq T (THead (Bind Abbr) v3 t8) t4) \to ((pr0 v0 v3) \to 
((pr0 t7 t8) \to (ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t4) t9)) 
(\lambda (t9: T).(pr0 (THead (Bind Abbr) v2 t6) t9)))))) H29)) H28 H25 H26))) 
| (pr0_upsilon b H25 v0 v3 H26 u0 u3 H27 t7 t8 H28) \Rightarrow (\lambda 
(H29: (eq T (THead (Flat Appl) v0 (THead (Bind b) u0 t7)) (THead (Bind Abst) 
u t5))).(\lambda (H30: (eq T (THead (Bind b) u3 (THead (Flat Appl) (lift (S 
O) O v3) t8)) t4)).((let H31 \def (eq_ind T (THead (Flat Appl) v0 (THead 
(Bind b) u0 t7)) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k0 _ 
_) \Rightarrow (match k0 in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind Abst) u t5) 
H29) in (False_ind ((eq T (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O 
v3) t8)) t4) \to ((not (eq B b Abst)) \to ((pr0 v0 v3) \to ((pr0 u0 u3) \to 
((pr0 t7 t8) \to (ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t4) t9)) 
(\lambda (t9: T).(pr0 (THead (Bind Abbr) v2 t6) t9)))))))) H31)) H30 H25 H26 
H27 H28))) | (pr0_delta u0 u3 H25 t7 t8 H26 w H27) \Rightarrow (\lambda (H28: 
(eq T (THead (Bind Abbr) u0 t7) (THead (Bind Abst) u t5))).(\lambda (H29: (eq 
T (THead (Bind Abbr) u3 w) t4)).((let H30 \def (eq_ind T (THead (Bind Abbr) 
u0 t7) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k0 _ _) 
\Rightarrow (match k0 in K return (\lambda (_: K).Prop) with [(Bind b) 
\Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow 
True | Abst \Rightarrow False | Void \Rightarrow False]) | (Flat _) 
\Rightarrow False])])) I (THead (Bind Abst) u t5) H28) in (False_ind ((eq T 
(THead (Bind Abbr) u3 w) t4) \to ((pr0 u0 u3) \to ((pr0 t7 t8) \to ((subst0 O 
u3 t8 w) \to (ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t4) t9)) 
(\lambda (t9: T).(pr0 (THead (Bind Abbr) v2 t6) t9))))))) H30)) H29 H25 H26 
H27))) | (pr0_zeta b H25 t7 t8 H26 u0) \Rightarrow (\lambda (H27: (eq T 
(THead (Bind b) u0 (lift (S O) O t7)) (THead (Bind Abst) u t5))).(\lambda 
(H28: (eq T t8 t4)).((let H29 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map (f: 
((nat \to nat))) (d: nat) (t9: T) on t9: T \def (match t9 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k0 u3 t10) 
\Rightarrow (THead k0 (lref_map f d u3) (lref_map f (s k0 d) t10))]) in 
lref_map) (\lambda (x: nat).(plus x (S O))) O t7) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t9: T) on t9: T \def (match 
t9 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k0 u3 t10) \Rightarrow (THead k0 (lref_map f d u3) (lref_map f (s k0 
d) t10))]) in lref_map) (\lambda (x: nat).(plus x (S O))) O t7) | (THead _ _ 
t9) \Rightarrow t9])) (THead (Bind b) u0 (lift (S O) O t7)) (THead (Bind 
Abst) u t5) H27) in ((let H30 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow u0 | (TLRef _) 
\Rightarrow u0 | (THead _ t9 _) \Rightarrow t9])) (THead (Bind b) u0 (lift (S 
O) O t7)) (THead (Bind Abst) u t5) H27) in ((let H31 \def (f_equal T B 
(\lambda (e: T).(match e in T return (\lambda (_: T).B) with [(TSort _) 
\Rightarrow b | (TLRef _) \Rightarrow b | (THead k0 _ _) \Rightarrow (match 
k0 in K return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) 
\Rightarrow b])])) (THead (Bind b) u0 (lift (S O) O t7)) (THead (Bind Abst) u 
t5) H27) in (eq_ind B Abst (\lambda (b0: B).((eq T u0 u) \to ((eq T (lift (S 
O) O t7) t5) \to ((eq T t8 t4) \to ((not (eq B b0 Abst)) \to ((pr0 t7 t8) \to 
(ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t4) t9)) (\lambda (t9: 
T).(pr0 (THead (Bind Abbr) v2 t6) t9))))))))) (\lambda (H32: (eq T u0 
u)).(eq_ind T u (\lambda (_: T).((eq T (lift (S O) O t7) t5) \to ((eq T t8 
t4) \to ((not (eq B Abst Abst)) \to ((pr0 t7 t8) \to (ex2 T (\lambda (t10: 
T).(pr0 (THead (Flat Appl) u2 t4) t10)) (\lambda (t10: T).(pr0 (THead (Bind 
Abbr) v2 t6) t10)))))))) (\lambda (H33: (eq T (lift (S O) O t7) t5)).(eq_ind 
T (lift (S O) O t7) (\lambda (_: T).((eq T t8 t4) \to ((not (eq B Abst Abst)) 
\to ((pr0 t7 t8) \to (ex2 T (\lambda (t10: T).(pr0 (THead (Flat Appl) u2 t4) 
t10)) (\lambda (t10: T).(pr0 (THead (Bind Abbr) v2 t6) t10))))))) (\lambda 
(H34: (eq T t8 t4)).(eq_ind T t4 (\lambda (t9: T).((not (eq B Abst Abst)) \to 
((pr0 t7 t9) \to (ex2 T (\lambda (t10: T).(pr0 (THead (Flat Appl) u2 t4) 
t10)) (\lambda (t10: T).(pr0 (THead (Bind Abbr) v2 t6) t10)))))) (\lambda 
(H35: (not (eq B Abst Abst))).(\lambda (_: (pr0 t7 t4)).(let H37 \def (match 
(H35 (refl_equal B Abst)) in False return (\lambda (_: False).(ex2 T (\lambda 
(t9: T).(pr0 (THead (Flat Appl) u2 t4) t9)) (\lambda (t9: T).(pr0 (THead 
(Bind Abbr) v2 t6) t9)))) with []) in H37))) t8 (sym_eq T t8 t4 H34))) t5 
H33)) u0 (sym_eq T u0 u H32))) b (sym_eq B b Abst H31))) H30)) H29)) H28 H25 
H26))) | (pr0_tau t7 t8 H25 u0) \Rightarrow (\lambda (H26: (eq T (THead (Flat 
Cast) u0 t7) (THead (Bind Abst) u t5))).(\lambda (H27: (eq T t8 t4)).((let 
H28 \def (eq_ind T (THead (Flat Cast) u0 t7) (\lambda (e: T).(match e in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind Abst) u t5) H26) in (False_ind ((eq T t8 t4) \to 
((pr0 t7 t8) \to (ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t4) t9)) 
(\lambda (t9: T).(pr0 (THead (Bind Abbr) v2 t6) t9))))) H28)) H27 H25)))]) in 
(H25 (refl_equal T (THead (Bind Abst) u t5)) (refl_equal T t4))))) k H21))))) 
H18)) H17))))) t2 H13)) t H11 H12 H9 H10))) | (pr0_upsilon b H9 v1 v2 H10 u0 
u3 H11 t5 t6 H12) \Rightarrow (\lambda (H13: (eq T (THead (Flat Appl) v1 
(THead (Bind b) u0 t5)) t)).(\lambda (H14: (eq T (THead (Bind b) u3 (THead 
(Flat Appl) (lift (S O) O v2) t6)) t2)).(eq_ind T (THead (Flat Appl) v1 
(THead (Bind b) u0 t5)) (\lambda (_: T).((eq T (THead (Bind b) u3 (THead 
(Flat Appl) (lift (S O) O v2) t6)) t2) \to ((not (eq B b Abst)) \to ((pr0 v1 
v2) \to ((pr0 u0 u3) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead 
k u2 t4) t8)) (\lambda (t8: T).(pr0 t2 t8))))))))) (\lambda (H15: (eq T 
(THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) t6)) t2)).(eq_ind T 
(THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) t6)) (\lambda (t7: 
T).((not (eq B b Abst)) \to ((pr0 v1 v2) \to ((pr0 u0 u3) \to ((pr0 t5 t6) 
\to (ex2 T (\lambda (t8: T).(pr0 (THead k u2 t4) t8)) (\lambda (t8: T).(pr0 
t7 t8)))))))) (\lambda (H16: (not (eq B b Abst))).(\lambda (H17: (pr0 v1 
v2)).(\lambda (H18: (pr0 u0 u3)).(\lambda (H19: (pr0 t5 t6)).(let H20 \def 
(eq_ind_r T t (\lambda (t7: T).(eq T (THead k u1 t3) t7)) H4 (THead (Flat 
Appl) v1 (THead (Bind b) u0 t5)) H13) in (let H21 \def (f_equal T K (\lambda 
(e: T).(match e in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k 
| (TLRef _) \Rightarrow k | (THead k0 _ _) \Rightarrow k0])) (THead k u1 t3) 
(THead (Flat Appl) v1 (THead (Bind b) u0 t5)) H20) in ((let H22 \def (f_equal 
T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u1 | (TLRef _) \Rightarrow u1 | (THead _ t7 _) \Rightarrow t7])) 
(THead k u1 t3) (THead (Flat Appl) v1 (THead (Bind b) u0 t5)) H20) in ((let 
H23 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead _ _ t7) 
\Rightarrow t7])) (THead k u1 t3) (THead (Flat Appl) v1 (THead (Bind b) u0 
t5)) H20) in (\lambda (H24: (eq T u1 v1)).(\lambda (H25: (eq K k (Flat 
Appl))).(let H26 \def (eq_ind_r T t (\lambda (t7: T).(\forall (v: T).((tlt v 
t7) \to (\forall (t8: T).((pr0 v t8) \to (\forall (t9: T).((pr0 v t9) \to 
(ex2 T (\lambda (t10: T).(pr0 t8 t10)) (\lambda (t10: T).(pr0 t9 
t10)))))))))) H (THead (Flat Appl) v1 (THead (Bind b) u0 t5)) H13) in 
(eq_ind_r K (Flat Appl) (\lambda (k0: K).(ex2 T (\lambda (t7: T).(pr0 (THead 
k0 u2 t4) t7)) (\lambda (t7: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) 
(lift (S O) O v2) t6)) t7)))) (let H27 \def (eq_ind T u1 (\lambda (t7: 
T).(pr0 t7 u2)) H7 v1 H24) in (let H28 \def (eq_ind T t3 (\lambda (t7: 
T).(pr0 t7 t4)) H8 (THead (Bind b) u0 t5) H23) in (let H29 \def (match H28 in 
pr0 return (\lambda (t7: T).(\lambda (t8: T).(\lambda (_: (pr0 t7 t8)).((eq T 
t7 (THead (Bind b) u0 t5)) \to ((eq T t8 t4) \to (ex2 T (\lambda (t9: T).(pr0 
(THead (Flat Appl) u2 t4) t9)) (\lambda (t9: T).(pr0 (THead (Bind b) u3 
(THead (Flat Appl) (lift (S O) O v2) t6)) t9)))))))) with [(pr0_refl t7) 
\Rightarrow (\lambda (H29: (eq T t7 (THead (Bind b) u0 t5))).(\lambda (H30: 
(eq T t7 t4)).(eq_ind T (THead (Bind b) u0 t5) (\lambda (t8: T).((eq T t8 t4) 
\to (ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t4) t9)) (\lambda (t9: 
T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) t6)) t9))))) 
(\lambda (H31: (eq T (THead (Bind b) u0 t5) t4)).(eq_ind T (THead (Bind b) u0 
t5) (\lambda (t8: T).(ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t8) 
t9)) (\lambda (t9: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) 
O v2) t6)) t9)))) (ex2_ind T (\lambda (t8: T).(pr0 u2 t8)) (\lambda (t8: 
T).(pr0 v2 t8)) (ex2 T (\lambda (t8: T).(pr0 (THead (Flat Appl) u2 (THead 
(Bind b) u0 t5)) t8)) (\lambda (t8: T).(pr0 (THead (Bind b) u3 (THead (Flat 
Appl) (lift (S O) O v2) t6)) t8))) (\lambda (x: T).(\lambda (H32: (pr0 u2 
x)).(\lambda (H33: (pr0 v2 x)).(pr0_confluence__pr0_cong_upsilon_refl b H16 
u0 u3 H18 t5 t6 H19 u2 v2 x H32 H33)))) (H26 v1 (tlt_head_sx (Flat Appl) v1 
(THead (Bind b) u0 t5)) u2 H27 v2 H17)) t4 H31)) t7 (sym_eq T t7 (THead (Bind 
b) u0 t5) H29) H30))) | (pr0_comp u4 u5 H29 t7 t8 H30 k0) \Rightarrow 
(\lambda (H31: (eq T (THead k0 u4 t7) (THead (Bind b) u0 t5))).(\lambda (H32: 
(eq T (THead k0 u5 t8) t4)).((let H33 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t7 | 
(TLRef _) \Rightarrow t7 | (THead _ _ t9) \Rightarrow t9])) (THead k0 u4 t7) 
(THead (Bind b) u0 t5) H31) in ((let H34 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u4 | 
(TLRef _) \Rightarrow u4 | (THead _ t9 _) \Rightarrow t9])) (THead k0 u4 t7) 
(THead (Bind b) u0 t5) H31) in ((let H35 \def (f_equal T K (\lambda (e: 
T).(match e in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k0 | 
(TLRef _) \Rightarrow k0 | (THead k1 _ _) \Rightarrow k1])) (THead k0 u4 t7) 
(THead (Bind b) u0 t5) H31) in (eq_ind K (Bind b) (\lambda (k1: K).((eq T u4 
u0) \to ((eq T t7 t5) \to ((eq T (THead k1 u5 t8) t4) \to ((pr0 u4 u5) \to 
((pr0 t7 t8) \to (ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t4) t9)) 
(\lambda (t9: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) 
t6)) t9))))))))) (\lambda (H36: (eq T u4 u0)).(eq_ind T u0 (\lambda (t9: 
T).((eq T t7 t5) \to ((eq T (THead (Bind b) u5 t8) t4) \to ((pr0 t9 u5) \to 
((pr0 t7 t8) \to (ex2 T (\lambda (t10: T).(pr0 (THead (Flat Appl) u2 t4) 
t10)) (\lambda (t10: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S 
O) O v2) t6)) t10)))))))) (\lambda (H37: (eq T t7 t5)).(eq_ind T t5 (\lambda 
(t9: T).((eq T (THead (Bind b) u5 t8) t4) \to ((pr0 u0 u5) \to ((pr0 t9 t8) 
\to (ex2 T (\lambda (t10: T).(pr0 (THead (Flat Appl) u2 t4) t10)) (\lambda 
(t10: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) t6)) 
t10))))))) (\lambda (H38: (eq T (THead (Bind b) u5 t8) t4)).(eq_ind T (THead 
(Bind b) u5 t8) (\lambda (t9: T).((pr0 u0 u5) \to ((pr0 t5 t8) \to (ex2 T 
(\lambda (t10: T).(pr0 (THead (Flat Appl) u2 t9) t10)) (\lambda (t10: T).(pr0 
(THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) t6)) t10)))))) 
(\lambda (H39: (pr0 u0 u5)).(\lambda (H40: (pr0 t5 t8)).(ex2_ind T (\lambda 
(t9: T).(pr0 t8 t9)) (\lambda (t9: T).(pr0 t6 t9)) (ex2 T (\lambda (t9: 
T).(pr0 (THead (Flat Appl) u2 (THead (Bind b) u5 t8)) t9)) (\lambda (t9: 
T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) t6)) t9))) 
(\lambda (x: T).(\lambda (H41: (pr0 t8 x)).(\lambda (H42: (pr0 t6 
x)).(ex2_ind T (\lambda (t9: T).(pr0 u5 t9)) (\lambda (t9: T).(pr0 u3 t9)) 
(ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 (THead (Bind b) u5 t8)) 
t9)) (\lambda (t9: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) 
O v2) t6)) t9))) (\lambda (x0: T).(\lambda (H43: (pr0 u5 x0)).(\lambda (H44: 
(pr0 u3 x0)).(ex2_ind T (\lambda (t9: T).(pr0 u2 t9)) (\lambda (t9: T).(pr0 
v2 t9)) (ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 (THead (Bind b) u5 
t8)) t9)) (\lambda (t9: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift 
(S O) O v2) t6)) t9))) (\lambda (x1: T).(\lambda (H45: (pr0 u2 x1)).(\lambda 
(H46: (pr0 v2 x1)).(pr0_confluence__pr0_cong_upsilon_cong b H16 u2 v2 x1 H45 
H46 t8 t6 x H41 H42 u5 u3 x0 H43 H44)))) (H26 v1 (tlt_head_sx (Flat Appl) v1 
(THead (Bind b) u0 t5)) u2 H27 v2 H17))))) (H26 u0 (tlt_trans (THead (Bind b) 
u0 t5) u0 (THead (Flat Appl) v1 (THead (Bind b) u0 t5)) (tlt_head_sx (Bind b) 
u0 t5) (tlt_head_dx (Flat Appl) v1 (THead (Bind b) u0 t5))) u5 H39 u3 
H18))))) (H26 t5 (tlt_trans (THead (Bind b) u0 t5) t5 (THead (Flat Appl) v1 
(THead (Bind b) u0 t5)) (tlt_head_dx (Bind b) u0 t5) (tlt_head_dx (Flat Appl) 
v1 (THead (Bind b) u0 t5))) t8 H40 t6 H19)))) t4 H38)) t7 (sym_eq T t7 t5 
H37))) u4 (sym_eq T u4 u0 H36))) k0 (sym_eq K k0 (Bind b) H35))) H34)) H33)) 
H32 H29 H30))) | (pr0_beta u v0 v3 H29 t7 t8 H30) \Rightarrow (\lambda (H31: 
(eq T (THead (Flat Appl) v0 (THead (Bind Abst) u t7)) (THead (Bind b) u0 
t5))).(\lambda (H32: (eq T (THead (Bind Abbr) v3 t8) t4)).((let H33 \def 
(eq_ind T (THead (Flat Appl) v0 (THead (Bind Abst) u t7)) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 in 
K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) I (THead (Bind b) u0 t5) H31) in (False_ind ((eq T 
(THead (Bind Abbr) v3 t8) t4) \to ((pr0 v0 v3) \to ((pr0 t7 t8) \to (ex2 T 
(\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t4) t9)) (\lambda (t9: T).(pr0 
(THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) t6)) t9)))))) H33)) 
H32 H29 H30))) | (pr0_upsilon b0 H29 v0 v3 H30 u4 u5 H31 t7 t8 H32) 
\Rightarrow (\lambda (H33: (eq T (THead (Flat Appl) v0 (THead (Bind b0) u4 
t7)) (THead (Bind b) u0 t5))).(\lambda (H34: (eq T (THead (Bind b0) u5 (THead 
(Flat Appl) (lift (S O) O v3) t8)) t4)).((let H35 \def (eq_ind T (THead (Flat 
Appl) v0 (THead (Bind b0) u4 t7)) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind b) u0 t5) H33) in (False_ind ((eq T (THead (Bind b0) 
u5 (THead (Flat Appl) (lift (S O) O v3) t8)) t4) \to ((not (eq B b0 Abst)) 
\to ((pr0 v0 v3) \to ((pr0 u4 u5) \to ((pr0 t7 t8) \to (ex2 T (\lambda (t9: 
T).(pr0 (THead (Flat Appl) u2 t4) t9)) (\lambda (t9: T).(pr0 (THead (Bind b) 
u3 (THead (Flat Appl) (lift (S O) O v2) t6)) t9)))))))) H35)) H34 H29 H30 H31 
H32))) | (pr0_delta u4 u5 H29 t7 t8 H30 w H31) \Rightarrow (\lambda (H32: (eq 
T (THead (Bind Abbr) u4 t7) (THead (Bind b) u0 t5))).(\lambda (H33: (eq T 
(THead (Bind Abbr) u5 w) t4)).((let H34 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t7 | 
(TLRef _) \Rightarrow t7 | (THead _ _ t9) \Rightarrow t9])) (THead (Bind 
Abbr) u4 t7) (THead (Bind b) u0 t5) H32) in ((let H35 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u4 | (TLRef _) \Rightarrow u4 | (THead _ t9 _) \Rightarrow t9])) 
(THead (Bind Abbr) u4 t7) (THead (Bind b) u0 t5) H32) in ((let H36 \def 
(f_equal T B (\lambda (e: T).(match e in T return (\lambda (_: T).B) with 
[(TSort _) \Rightarrow Abbr | (TLRef _) \Rightarrow Abbr | (THead k0 _ _) 
\Rightarrow (match k0 in K return (\lambda (_: K).B) with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) (THead (Bind Abbr) u4 t7) 
(THead (Bind b) u0 t5) H32) in (eq_ind B Abbr (\lambda (b0: B).((eq T u4 u0) 
\to ((eq T t7 t5) \to ((eq T (THead (Bind Abbr) u5 w) t4) \to ((pr0 u4 u5) 
\to ((pr0 t7 t8) \to ((subst0 O u5 t8 w) \to (ex2 T (\lambda (t9: T).(pr0 
(THead (Flat Appl) u2 t4) t9)) (\lambda (t9: T).(pr0 (THead (Bind b0) u3 
(THead (Flat Appl) (lift (S O) O v2) t6)) t9)))))))))) (\lambda (H37: (eq T 
u4 u0)).(eq_ind T u0 (\lambda (t9: T).((eq T t7 t5) \to ((eq T (THead (Bind 
Abbr) u5 w) t4) \to ((pr0 t9 u5) \to ((pr0 t7 t8) \to ((subst0 O u5 t8 w) \to 
(ex2 T (\lambda (t10: T).(pr0 (THead (Flat Appl) u2 t4) t10)) (\lambda (t10: 
T).(pr0 (THead (Bind Abbr) u3 (THead (Flat Appl) (lift (S O) O v2) t6)) 
t10))))))))) (\lambda (H38: (eq T t7 t5)).(eq_ind T t5 (\lambda (t9: T).((eq 
T (THead (Bind Abbr) u5 w) t4) \to ((pr0 u0 u5) \to ((pr0 t9 t8) \to ((subst0 
O u5 t8 w) \to (ex2 T (\lambda (t10: T).(pr0 (THead (Flat Appl) u2 t4) t10)) 
(\lambda (t10: T).(pr0 (THead (Bind Abbr) u3 (THead (Flat Appl) (lift (S O) O 
v2) t6)) t10)))))))) (\lambda (H39: (eq T (THead (Bind Abbr) u5 w) 
t4)).(eq_ind T (THead (Bind Abbr) u5 w) (\lambda (t9: T).((pr0 u0 u5) \to 
((pr0 t5 t8) \to ((subst0 O u5 t8 w) \to (ex2 T (\lambda (t10: T).(pr0 (THead 
(Flat Appl) u2 t9) t10)) (\lambda (t10: T).(pr0 (THead (Bind Abbr) u3 (THead 
(Flat Appl) (lift (S O) O v2) t6)) t10))))))) (\lambda (H40: (pr0 u0 
u5)).(\lambda (H41: (pr0 t5 t8)).(\lambda (H42: (subst0 O u5 t8 w)).(let H43 
\def (eq_ind_r B b (\lambda (b0: B).(\forall (v: T).((tlt v (THead (Flat 
Appl) v1 (THead (Bind b0) u0 t5))) \to (\forall (t9: T).((pr0 v t9) \to 
(\forall (t10: T).((pr0 v t10) \to (ex2 T (\lambda (t11: T).(pr0 t9 t11)) 
(\lambda (t11: T).(pr0 t10 t11)))))))))) H26 Abbr H36) in (let H44 \def 
(eq_ind_r B b (\lambda (b0: B).(eq T t3 (THead (Bind b0) u0 t5))) H23 Abbr 
H36) in (let H45 \def (eq_ind_r B b (\lambda (b0: B).(not (eq B b0 Abst))) 
H16 Abbr H36) in (ex2_ind T (\lambda (t9: T).(pr0 t8 t9)) (\lambda (t9: 
T).(pr0 t6 t9)) (ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 (THead 
(Bind Abbr) u5 w)) t9)) (\lambda (t9: T).(pr0 (THead (Bind Abbr) u3 (THead 
(Flat Appl) (lift (S O) O v2) t6)) t9))) (\lambda (x: T).(\lambda (H46: (pr0 
t8 x)).(\lambda (H47: (pr0 t6 x)).(ex2_ind T (\lambda (t9: T).(pr0 u5 t9)) 
(\lambda (t9: T).(pr0 u3 t9)) (ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) 
u2 (THead (Bind Abbr) u5 w)) t9)) (\lambda (t9: T).(pr0 (THead (Bind Abbr) u3 
(THead (Flat Appl) (lift (S O) O v2) t6)) t9))) (\lambda (x0: T).(\lambda 
(H48: (pr0 u5 x0)).(\lambda (H49: (pr0 u3 x0)).(ex2_ind T (\lambda (t9: 
T).(pr0 u2 t9)) (\lambda (t9: T).(pr0 v2 t9)) (ex2 T (\lambda (t9: T).(pr0 
(THead (Flat Appl) u2 (THead (Bind Abbr) u5 w)) t9)) (\lambda (t9: T).(pr0 
(THead (Bind Abbr) u3 (THead (Flat Appl) (lift (S O) O v2) t6)) t9))) 
(\lambda (x1: T).(\lambda (H50: (pr0 u2 x1)).(\lambda (H51: (pr0 v2 
x1)).(pr0_confluence__pr0_cong_upsilon_delta H45 u5 t8 w H42 u2 v2 x1 H50 H51 
t6 x H46 H47 u3 x0 H48 H49)))) (H43 v1 (tlt_head_sx (Flat Appl) v1 (THead 
(Bind Abbr) u0 t5)) u2 H27 v2 H17))))) (H43 u0 (tlt_trans (THead (Bind Abbr) 
u0 t5) u0 (THead (Flat Appl) v1 (THead (Bind Abbr) u0 t5)) (tlt_head_sx (Bind 
Abbr) u0 t5) (tlt_head_dx (Flat Appl) v1 (THead (Bind Abbr) u0 t5))) u5 H40 
u3 H18))))) (H43 t5 (tlt_trans (THead (Bind Abbr) u0 t5) t5 (THead (Flat 
Appl) v1 (THead (Bind Abbr) u0 t5)) (tlt_head_dx (Bind Abbr) u0 t5) 
(tlt_head_dx (Flat Appl) v1 (THead (Bind Abbr) u0 t5))) t8 H41 t6 H19)))))))) 
t4 H39)) t7 (sym_eq T t7 t5 H38))) u4 (sym_eq T u4 u0 H37))) b H36)) H35)) 
H34)) H33 H29 H30 H31))) | (pr0_zeta b0 H29 t7 t8 H30 u) \Rightarrow (\lambda 
(H31: (eq T (THead (Bind b0) u (lift (S O) O t7)) (THead (Bind b) u0 
t5))).(\lambda (H32: (eq T t8 t4)).((let H33 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow ((let 
rec lref_map (f: ((nat \to nat))) (d: nat) (t9: T) on t9: T \def (match t9 
with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match 
(blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | (THead k0 
u4 t10) \Rightarrow (THead k0 (lref_map f d u4) (lref_map f (s k0 d) t10))]) 
in lref_map) (\lambda (x: nat).(plus x (S O))) O t7) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t9: T) on t9: T \def (match 
t9 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k0 u4 t10) \Rightarrow (THead k0 (lref_map f d u4) (lref_map f (s k0 
d) t10))]) in lref_map) (\lambda (x: nat).(plus x (S O))) O t7) | (THead _ _ 
t9) \Rightarrow t9])) (THead (Bind b0) u (lift (S O) O t7)) (THead (Bind b) 
u0 t5) H31) in ((let H34 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow u | (TLRef _) 
\Rightarrow u | (THead _ t9 _) \Rightarrow t9])) (THead (Bind b0) u (lift (S 
O) O t7)) (THead (Bind b) u0 t5) H31) in ((let H35 \def (f_equal T B (\lambda 
(e: T).(match e in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow b0 
| (TLRef _) \Rightarrow b0 | (THead k0 _ _) \Rightarrow (match k0 in K return 
(\lambda (_: K).B) with [(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow 
b0])])) (THead (Bind b0) u (lift (S O) O t7)) (THead (Bind b) u0 t5) H31) in 
(eq_ind B b (\lambda (b1: B).((eq T u u0) \to ((eq T (lift (S O) O t7) t5) 
\to ((eq T t8 t4) \to ((not (eq B b1 Abst)) \to ((pr0 t7 t8) \to (ex2 T 
(\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t4) t9)) (\lambda (t9: T).(pr0 
(THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) t6)) t9))))))))) 
(\lambda (H36: (eq T u u0)).(eq_ind T u0 (\lambda (_: T).((eq T (lift (S O) O 
t7) t5) \to ((eq T t8 t4) \to ((not (eq B b Abst)) \to ((pr0 t7 t8) \to (ex2 
T (\lambda (t10: T).(pr0 (THead (Flat Appl) u2 t4) t10)) (\lambda (t10: 
T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) t6)) 
t10)))))))) (\lambda (H37: (eq T (lift (S O) O t7) t5)).(eq_ind T (lift (S O) 
O t7) (\lambda (_: T).((eq T t8 t4) \to ((not (eq B b Abst)) \to ((pr0 t7 t8) 
\to (ex2 T (\lambda (t10: T).(pr0 (THead (Flat Appl) u2 t4) t10)) (\lambda 
(t10: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) t6)) 
t10))))))) (\lambda (H38: (eq T t8 t4)).(eq_ind T t4 (\lambda (t9: T).((not 
(eq B b Abst)) \to ((pr0 t7 t9) \to (ex2 T (\lambda (t10: T).(pr0 (THead 
(Flat Appl) u2 t4) t10)) (\lambda (t10: T).(pr0 (THead (Bind b) u3 (THead 
(Flat Appl) (lift (S O) O v2) t6)) t10)))))) (\lambda (H39: (not (eq B b 
Abst))).(\lambda (H40: (pr0 t7 t4)).(let H41 \def (eq_ind_r T t5 (\lambda 
(t9: T).(\forall (v: T).((tlt v (THead (Flat Appl) v1 (THead (Bind b) u0 
t9))) \to (\forall (t10: T).((pr0 v t10) \to (\forall (t11: T).((pr0 v t11) 
\to (ex2 T (\lambda (t12: T).(pr0 t10 t12)) (\lambda (t12: T).(pr0 t11 
t12)))))))))) H26 (lift (S O) O t7) H37) in (let H42 \def (eq_ind_r T t5 
(\lambda (t9: T).(eq T t3 (THead (Bind b) u0 t9))) H23 (lift (S O) O t7) H37) 
in (let H43 \def (eq_ind_r T t5 (\lambda (t9: T).(pr0 t9 t6)) H19 (lift (S O) 
O t7) H37) in (ex2_ind T (\lambda (t9: T).(eq T t6 (lift (S O) O t9))) 
(\lambda (t9: T).(pr0 t7 t9)) (ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) 
u2 t4) t9)) (\lambda (t9: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift 
(S O) O v2) t6)) t9))) (\lambda (x: T).(\lambda (H44: (eq T t6 (lift (S O) O 
x))).(\lambda (H45: (pr0 t7 x)).(eq_ind_r T (lift (S O) O x) (\lambda (t9: 
T).(ex2 T (\lambda (t10: T).(pr0 (THead (Flat Appl) u2 t4) t10)) (\lambda 
(t10: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) t9)) 
t10)))) (ex2_ind T (\lambda (t9: T).(pr0 x t9)) (\lambda (t9: T).(pr0 t4 t9)) 
(ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t4) t9)) (\lambda (t9: 
T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) (lift (S O) O 
x))) t9))) (\lambda (x0: T).(\lambda (H46: (pr0 x x0)).(\lambda (H47: (pr0 t4 
x0)).(ex2_ind T (\lambda (t9: T).(pr0 u2 t9)) (\lambda (t9: T).(pr0 v2 t9)) 
(ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t4) t9)) (\lambda (t9: 
T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) (lift (S O) O 
x))) t9))) (\lambda (x1: T).(\lambda (H48: (pr0 u2 x1)).(\lambda (H49: (pr0 
v2 x1)).(pr0_confluence__pr0_cong_upsilon_zeta b H39 u0 u3 H18 u2 v2 x1 H48 
H49 x t4 x0 H46 H47)))) (H41 v1 (tlt_head_sx (Flat Appl) v1 (THead (Bind b) 
u0 (lift (S O) O t7))) u2 H27 v2 H17))))) (H41 t7 (tlt_trans (THead (Bind b) 
u0 (lift (S O) O t7)) t7 (THead (Flat Appl) v1 (THead (Bind b) u0 (lift (S O) 
O t7))) (lift_tlt_dx (Bind b) u0 t7 (S O) O) (tlt_head_dx (Flat Appl) v1 
(THead (Bind b) u0 (lift (S O) O t7)))) x H45 t4 H40)) t6 H44)))) 
(pr0_gen_lift t7 t6 (S O) O H43))))))) t8 (sym_eq T t8 t4 H38))) t5 H37)) u 
(sym_eq T u u0 H36))) b0 (sym_eq B b0 b H35))) H34)) H33)) H32 H29 H30))) | 
(pr0_tau t7 t8 H29 u) \Rightarrow (\lambda (H30: (eq T (THead (Flat Cast) u 
t7) (THead (Bind b) u0 t5))).(\lambda (H31: (eq T t8 t4)).((let H32 \def 
(eq_ind T (THead (Flat Cast) u t7) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind b) u0 t5) H30) in (False_ind ((eq T t8 t4) \to ((pr0 
t7 t8) \to (ex2 T (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t4) t9)) 
(\lambda (t9: T).(pr0 (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v2) 
t6)) t9))))) H32)) H31 H29)))]) in (H29 (refl_equal T (THead (Bind b) u0 t5)) 
(refl_equal T t4))))) k H25))))) H22)) H21))))))) t2 H15)) t H13 H14 H9 H10 
H11 H12))) | (pr0_delta u0 u3 H9 t5 t6 H10 w H11) \Rightarrow (\lambda (H12: 
(eq T (THead (Bind Abbr) u0 t5) t)).(\lambda (H13: (eq T (THead (Bind Abbr) 
u3 w) t2)).(eq_ind T (THead (Bind Abbr) u0 t5) (\lambda (_: T).((eq T (THead 
(Bind Abbr) u3 w) t2) \to ((pr0 u0 u3) \to ((pr0 t5 t6) \to ((subst0 O u3 t6 
w) \to (ex2 T (\lambda (t8: T).(pr0 (THead k u2 t4) t8)) (\lambda (t8: 
T).(pr0 t2 t8)))))))) (\lambda (H14: (eq T (THead (Bind Abbr) u3 w) 
t2)).(eq_ind T (THead (Bind Abbr) u3 w) (\lambda (t7: T).((pr0 u0 u3) \to 
((pr0 t5 t6) \to ((subst0 O u3 t6 w) \to (ex2 T (\lambda (t8: T).(pr0 (THead 
k u2 t4) t8)) (\lambda (t8: T).(pr0 t7 t8))))))) (\lambda (H15: (pr0 u0 
u3)).(\lambda (H16: (pr0 t5 t6)).(\lambda (H17: (subst0 O u3 t6 w)).(let H18 
\def (eq_ind_r T t (\lambda (t7: T).(eq T (THead k u1 t3) t7)) H4 (THead 
(Bind Abbr) u0 t5) H12) in (let H19 \def (f_equal T K (\lambda (e: T).(match 
e in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k0 _ _) \Rightarrow k0])) (THead k u1 t3) (THead (Bind 
Abbr) u0 t5) H18) in ((let H20 \def (f_equal T T (\lambda (e: T).(match e in 
T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u1 | (TLRef _) 
\Rightarrow u1 | (THead _ t7 _) \Rightarrow t7])) (THead k u1 t3) (THead 
(Bind Abbr) u0 t5) H18) in ((let H21 \def (f_equal T T (\lambda (e: T).(match 
e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t3 | (TLRef _) 
\Rightarrow t3 | (THead _ _ t7) \Rightarrow t7])) (THead k u1 t3) (THead 
(Bind Abbr) u0 t5) H18) in (\lambda (H22: (eq T u1 u0)).(\lambda (H23: (eq K 
k (Bind Abbr))).(let H24 \def (eq_ind_r T t (\lambda (t7: T).(\forall (v: 
T).((tlt v t7) \to (\forall (t8: T).((pr0 v t8) \to (\forall (t9: T).((pr0 v 
t9) \to (ex2 T (\lambda (t10: T).(pr0 t8 t10)) (\lambda (t10: T).(pr0 t9 
t10)))))))))) H (THead (Bind Abbr) u0 t5) H12) in (eq_ind_r K (Bind Abbr) 
(\lambda (k0: K).(ex2 T (\lambda (t7: T).(pr0 (THead k0 u2 t4) t7)) (\lambda 
(t7: T).(pr0 (THead (Bind Abbr) u3 w) t7)))) (let H25 \def (eq_ind T u1 
(\lambda (t7: T).(pr0 t7 u2)) H7 u0 H22) in (let H26 \def (eq_ind T t3 
(\lambda (t7: T).(pr0 t7 t4)) H8 t5 H21) in (ex2_ind T (\lambda (t7: T).(pr0 
t4 t7)) (\lambda (t7: T).(pr0 t6 t7)) (ex2 T (\lambda (t7: T).(pr0 (THead 
(Bind Abbr) u2 t4) t7)) (\lambda (t7: T).(pr0 (THead (Bind Abbr) u3 w) t7))) 
(\lambda (x: T).(\lambda (H27: (pr0 t4 x)).(\lambda (H28: (pr0 t6 
x)).(ex2_ind T (\lambda (t7: T).(pr0 u2 t7)) (\lambda (t7: T).(pr0 u3 t7)) 
(ex2 T (\lambda (t7: T).(pr0 (THead (Bind Abbr) u2 t4) t7)) (\lambda (t7: 
T).(pr0 (THead (Bind Abbr) u3 w) t7))) (\lambda (x0: T).(\lambda (H29: (pr0 
u2 x0)).(\lambda (H30: (pr0 u3 x0)).(pr0_confluence__pr0_cong_delta u3 t6 w 
H17 u2 x0 H29 H30 t4 x H27 H28)))) (H24 u0 (tlt_head_sx (Bind Abbr) u0 t5) u2 
H25 u3 H15))))) (H24 t5 (tlt_head_dx (Bind Abbr) u0 t5) t4 H26 t6 H16)))) k 
H23))))) H20)) H19)))))) t2 H14)) t H12 H13 H9 H10 H11))) | (pr0_zeta b H9 t5 
t6 H10 u) \Rightarrow (\lambda (H11: (eq T (THead (Bind b) u (lift (S O) O 
t5)) t)).(\lambda (H12: (eq T t6 t2)).(eq_ind T (THead (Bind b) u (lift (S O) 
O t5)) (\lambda (_: T).((eq T t6 t2) \to ((not (eq B b Abst)) \to ((pr0 t5 
t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead k u2 t4) t8)) (\lambda (t8: 
T).(pr0 t2 t8))))))) (\lambda (H13: (eq T t6 t2)).(eq_ind T t2 (\lambda (t7: 
T).((not (eq B b Abst)) \to ((pr0 t5 t7) \to (ex2 T (\lambda (t8: T).(pr0 
(THead k u2 t4) t8)) (\lambda (t8: T).(pr0 t2 t8)))))) (\lambda (H14: (not 
(eq B b Abst))).(\lambda (H15: (pr0 t5 t2)).(let H16 \def (eq_ind_r T t 
(\lambda (t7: T).(eq T (THead k u1 t3) t7)) H4 (THead (Bind b) u (lift (S O) 
O t5)) H11) in (let H17 \def (f_equal T K (\lambda (e: T).(match e in T 
return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k0 _ _) \Rightarrow k0])) (THead k u1 t3) (THead (Bind 
b) u (lift (S O) O t5)) H16) in ((let H18 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u1 | 
(TLRef _) \Rightarrow u1 | (THead _ t7 _) \Rightarrow t7])) (THead k u1 t3) 
(THead (Bind b) u (lift (S O) O t5)) H16) in ((let H19 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead _ _ t7) \Rightarrow t7])) 
(THead k u1 t3) (THead (Bind b) u (lift (S O) O t5)) H16) in (\lambda (H20: 
(eq T u1 u)).(\lambda (H21: (eq K k (Bind b))).(let H22 \def (eq_ind_r T t 
(\lambda (t7: T).(\forall (v: T).((tlt v t7) \to (\forall (t8: T).((pr0 v t8) 
\to (\forall (t9: T).((pr0 v t9) \to (ex2 T (\lambda (t10: T).(pr0 t8 t10)) 
(\lambda (t10: T).(pr0 t9 t10)))))))))) H (THead (Bind b) u (lift (S O) O 
t5)) H11) in (eq_ind_r K (Bind b) (\lambda (k0: K).(ex2 T (\lambda (t7: 
T).(pr0 (THead k0 u2 t4) t7)) (\lambda (t7: T).(pr0 t2 t7)))) (let H23 \def 
(eq_ind T u1 (\lambda (t7: T).(pr0 t7 u2)) H7 u H20) in (let H24 \def (eq_ind 
T t3 (\lambda (t7: T).(pr0 t7 t4)) H8 (lift (S O) O t5) H19) in (ex2_ind T 
(\lambda (t7: T).(eq T t4 (lift (S O) O t7))) (\lambda (t7: T).(pr0 t5 t7)) 
(ex2 T (\lambda (t7: T).(pr0 (THead (Bind b) u2 t4) t7)) (\lambda (t7: 
T).(pr0 t2 t7))) (\lambda (x: T).(\lambda (H25: (eq T t4 (lift (S O) O 
x))).(\lambda (H26: (pr0 t5 x)).(eq_ind_r T (lift (S O) O x) (\lambda (t7: 
T).(ex2 T (\lambda (t8: T).(pr0 (THead (Bind b) u2 t7) t8)) (\lambda (t8: 
T).(pr0 t2 t8)))) (ex2_ind T (\lambda (t7: T).(pr0 x t7)) (\lambda (t7: 
T).(pr0 t2 t7)) (ex2 T (\lambda (t7: T).(pr0 (THead (Bind b) u2 (lift (S O) O 
x)) t7)) (\lambda (t7: T).(pr0 t2 t7))) (\lambda (x0: T).(\lambda (H27: (pr0 
x x0)).(\lambda (H28: (pr0 t2 x0)).(ex_intro2 T (\lambda (t7: T).(pr0 (THead 
(Bind b) u2 (lift (S O) O x)) t7)) (\lambda (t7: T).(pr0 t2 t7)) x0 (pr0_zeta 
b H14 x x0 H27 u2) H28)))) (H22 t5 (lift_tlt_dx (Bind b) u t5 (S O) O) x H26 
t2 H15)) t4 H25)))) (pr0_gen_lift t5 t4 (S O) O H24)))) k H21))))) H18)) 
H17))))) t6 (sym_eq T t6 t2 H13))) t H11 H12 H9 H10))) | (pr0_tau t5 t6 H9 u) 
\Rightarrow (\lambda (H10: (eq T (THead (Flat Cast) u t5) t)).(\lambda (H11: 
(eq T t6 t2)).(eq_ind T (THead (Flat Cast) u t5) (\lambda (_: T).((eq T t6 
t2) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead k u2 t4) t8)) 
(\lambda (t8: T).(pr0 t2 t8)))))) (\lambda (H12: (eq T t6 t2)).(eq_ind T t2 
(\lambda (t7: T).((pr0 t5 t7) \to (ex2 T (\lambda (t8: T).(pr0 (THead k u2 
t4) t8)) (\lambda (t8: T).(pr0 t2 t8))))) (\lambda (H13: (pr0 t5 t2)).(let 
H14 \def (eq_ind_r T t (\lambda (t7: T).(eq T (THead k u1 t3) t7)) H4 (THead 
(Flat Cast) u t5) H10) in (let H15 \def (f_equal T K (\lambda (e: T).(match e 
in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k0 _ _) \Rightarrow k0])) (THead k u1 t3) (THead (Flat 
Cast) u t5) H14) in ((let H16 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow u1 | (TLRef _) 
\Rightarrow u1 | (THead _ t7 _) \Rightarrow t7])) (THead k u1 t3) (THead 
(Flat Cast) u t5) H14) in ((let H17 \def (f_equal T T (\lambda (e: T).(match 
e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t3 | (TLRef _) 
\Rightarrow t3 | (THead _ _ t7) \Rightarrow t7])) (THead k u1 t3) (THead 
(Flat Cast) u t5) H14) in (\lambda (H18: (eq T u1 u)).(\lambda (H19: (eq K k 
(Flat Cast))).(let H20 \def (eq_ind_r T t (\lambda (t7: T).(\forall (v: 
T).((tlt v t7) \to (\forall (t8: T).((pr0 v t8) \to (\forall (t9: T).((pr0 v 
t9) \to (ex2 T (\lambda (t10: T).(pr0 t8 t10)) (\lambda (t10: T).(pr0 t9 
t10)))))))))) H (THead (Flat Cast) u t5) H10) in (eq_ind_r K (Flat Cast) 
(\lambda (k0: K).(ex2 T (\lambda (t7: T).(pr0 (THead k0 u2 t4) t7)) (\lambda 
(t7: T).(pr0 t2 t7)))) (let H21 \def (eq_ind T u1 (\lambda (t7: T).(pr0 t7 
u2)) H7 u H18) in (let H22 \def (eq_ind T t3 (\lambda (t7: T).(pr0 t7 t4)) H8 
t5 H17) in (ex2_ind T (\lambda (t7: T).(pr0 t4 t7)) (\lambda (t7: T).(pr0 t2 
t7)) (ex2 T (\lambda (t7: T).(pr0 (THead (Flat Cast) u2 t4) t7)) (\lambda 
(t7: T).(pr0 t2 t7))) (\lambda (x: T).(\lambda (H23: (pr0 t4 x)).(\lambda 
(H24: (pr0 t2 x)).(ex_intro2 T (\lambda (t7: T).(pr0 (THead (Flat Cast) u2 
t4) t7)) (\lambda (t7: T).(pr0 t2 t7)) x (pr0_tau t4 x H23 u2) H24)))) (H20 
t5 (tlt_head_dx (Flat Cast) u t5) t4 H22 t2 H13)))) k H19))))) H16)) H15)))) 
t6 (sym_eq T t6 t2 H12))) t H10 H11 H9)))]) in (H9 (refl_equal T t) 
(refl_equal T t2))))) t1 H6)) t H4 H5 H2 H3))) | (pr0_beta u v1 v2 H2 t3 t4 
H3) \Rightarrow (\lambda (H4: (eq T (THead (Flat Appl) v1 (THead (Bind Abst) 
u t3)) t)).(\lambda (H5: (eq T (THead (Bind Abbr) v2 t4) t1)).(eq_ind T 
(THead (Flat Appl) v1 (THead (Bind Abst) u t3)) (\lambda (_: T).((eq T (THead 
(Bind Abbr) v2 t4) t1) \to ((pr0 v1 v2) \to ((pr0 t3 t4) \to (ex2 T (\lambda 
(t6: T).(pr0 t1 t6)) (\lambda (t6: T).(pr0 t2 t6))))))) (\lambda (H6: (eq T 
(THead (Bind Abbr) v2 t4) t1)).(eq_ind T (THead (Bind Abbr) v2 t4) (\lambda 
(t5: T).((pr0 v1 v2) \to ((pr0 t3 t4) \to (ex2 T (\lambda (t6: T).(pr0 t5 
t6)) (\lambda (t6: T).(pr0 t2 t6)))))) (\lambda (H7: (pr0 v1 v2)).(\lambda 
(H8: (pr0 t3 t4)).(let H9 \def (match H1 in pr0 return (\lambda (t5: 
T).(\lambda (t6: T).(\lambda (_: (pr0 t5 t6)).((eq T t5 t) \to ((eq T t6 t2) 
\to (ex2 T (\lambda (t7: T).(pr0 (THead (Bind Abbr) v2 t4) t7)) (\lambda (t7: 
T).(pr0 t2 t7)))))))) with [(pr0_refl t5) \Rightarrow (\lambda (H9: (eq T t5 
t)).(\lambda (H10: (eq T t5 t2)).(eq_ind T t (\lambda (t6: T).((eq T t6 t2) 
\to (ex2 T (\lambda (t7: T).(pr0 (THead (Bind Abbr) v2 t4) t7)) (\lambda (t7: 
T).(pr0 t2 t7))))) (\lambda (H11: (eq T t t2)).(eq_ind T t2 (\lambda (_: 
T).(ex2 T (\lambda (t7: T).(pr0 (THead (Bind Abbr) v2 t4) t7)) (\lambda (t7: 
T).(pr0 t2 t7)))) (let H12 \def (eq_ind_r T t (\lambda (t6: T).(eq T t6 t2)) 
H11 (THead (Flat Appl) v1 (THead (Bind Abst) u t3)) H4) in (eq_ind T (THead 
(Flat Appl) v1 (THead (Bind Abst) u t3)) (\lambda (t6: T).(ex2 T (\lambda 
(t7: T).(pr0 (THead (Bind Abbr) v2 t4) t7)) (\lambda (t7: T).(pr0 t6 t7)))) 
(let H13 \def (eq_ind_r T t (\lambda (t6: T).(eq T t5 t6)) H9 (THead (Flat 
Appl) v1 (THead (Bind Abst) u t3)) H4) in (let H14 \def (eq_ind_r T t 
(\lambda (t6: T).(\forall (v: T).((tlt v t6) \to (\forall (t7: T).((pr0 v t7) 
\to (\forall (t8: T).((pr0 v t8) \to (ex2 T (\lambda (t9: T).(pr0 t7 t9)) 
(\lambda (t9: T).(pr0 t8 t9)))))))))) H (THead (Flat Appl) v1 (THead (Bind 
Abst) u t3)) H4) in (ex_intro2 T (\lambda (t6: T).(pr0 (THead (Bind Abbr) v2 
t4) t6)) (\lambda (t6: T).(pr0 (THead (Flat Appl) v1 (THead (Bind Abst) u 
t3)) t6)) (THead (Bind Abbr) v2 t4) (pr0_refl (THead (Bind Abbr) v2 t4)) 
(pr0_beta u v1 v2 H7 t3 t4 H8)))) t2 H12)) t (sym_eq T t t2 H11))) t5 (sym_eq 
T t5 t H9) H10))) | (pr0_comp u1 u2 H9 t5 t6 H10 k) \Rightarrow (\lambda 
(H11: (eq T (THead k u1 t5) t)).(\lambda (H12: (eq T (THead k u2 t6) 
t2)).(eq_ind T (THead k u1 t5) (\lambda (_: T).((eq T (THead k u2 t6) t2) \to 
((pr0 u1 u2) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead (Bind 
Abbr) v2 t4) t8)) (\lambda (t8: T).(pr0 t2 t8))))))) (\lambda (H13: (eq T 
(THead k u2 t6) t2)).(eq_ind T (THead k u2 t6) (\lambda (t7: T).((pr0 u1 u2) 
\to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead (Bind Abbr) v2 t4) 
t8)) (\lambda (t8: T).(pr0 t7 t8)))))) (\lambda (H14: (pr0 u1 u2)).(\lambda 
(H15: (pr0 t5 t6)).(let H16 \def (eq_ind_r T t (\lambda (t7: T).(eq T (THead 
(Flat Appl) v1 (THead (Bind Abst) u t3)) t7)) H4 (THead k u1 t5) H11) in (let 
H17 \def (f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) 
with [(TSort _) \Rightarrow (Flat Appl) | (TLRef _) \Rightarrow (Flat Appl) | 
(THead k0 _ _) \Rightarrow k0])) (THead (Flat Appl) v1 (THead (Bind Abst) u 
t3)) (THead k u1 t5) H16) in ((let H18 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow v1 | 
(TLRef _) \Rightarrow v1 | (THead _ t7 _) \Rightarrow t7])) (THead (Flat 
Appl) v1 (THead (Bind Abst) u t3)) (THead k u1 t5) H16) in ((let H19 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow (THead (Bind Abst) u t3) | (TLRef _) \Rightarrow 
(THead (Bind Abst) u t3) | (THead _ _ t7) \Rightarrow t7])) (THead (Flat 
Appl) v1 (THead (Bind Abst) u t3)) (THead k u1 t5) H16) in (\lambda (H20: (eq 
T v1 u1)).(\lambda (H21: (eq K (Flat Appl) k)).(eq_ind K (Flat Appl) (\lambda 
(k0: K).(ex2 T (\lambda (t7: T).(pr0 (THead (Bind Abbr) v2 t4) t7)) (\lambda 
(t7: T).(pr0 (THead k0 u2 t6) t7)))) (let H22 \def (eq_ind_r K k (\lambda 
(k0: K).(eq T (THead k0 u1 t5) t)) H11 (Flat Appl) H21) in (let H23 \def 
(eq_ind_r T t5 (\lambda (t7: T).(pr0 t7 t6)) H15 (THead (Bind Abst) u t3) 
H19) in (let H24 \def (match H23 in pr0 return (\lambda (t7: T).(\lambda (t8: 
T).(\lambda (_: (pr0 t7 t8)).((eq T t7 (THead (Bind Abst) u t3)) \to ((eq T 
t8 t6) \to (ex2 T (\lambda (t9: T).(pr0 (THead (Bind Abbr) v2 t4) t9)) 
(\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t6) t9)))))))) with [(pr0_refl 
t7) \Rightarrow (\lambda (H24: (eq T t7 (THead (Bind Abst) u t3))).(\lambda 
(H25: (eq T t7 t6)).(eq_ind T (THead (Bind Abst) u t3) (\lambda (t8: T).((eq 
T t8 t6) \to (ex2 T (\lambda (t9: T).(pr0 (THead (Bind Abbr) v2 t4) t9)) 
(\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t6) t9))))) (\lambda (H26: (eq T 
(THead (Bind Abst) u t3) t6)).(eq_ind T (THead (Bind Abst) u t3) (\lambda 
(t8: T).(ex2 T (\lambda (t9: T).(pr0 (THead (Bind Abbr) v2 t4) t9)) (\lambda 
(t9: T).(pr0 (THead (Flat Appl) u2 t8) t9)))) (let H27 \def (eq_ind_r T t5 
(\lambda (t8: T).(eq T (THead (Flat Appl) u1 t8) t)) H22 (THead (Bind Abst) u 
t3) H19) in (let H28 \def (eq_ind_r T t (\lambda (t8: T).(\forall (v: 
T).((tlt v t8) \to (\forall (t9: T).((pr0 v t9) \to (\forall (t10: T).((pr0 v 
t10) \to (ex2 T (\lambda (t11: T).(pr0 t9 t11)) (\lambda (t11: T).(pr0 t10 
t11)))))))))) H (THead (Flat Appl) u1 (THead (Bind Abst) u t3)) H27) in (let 
H29 \def (eq_ind T v1 (\lambda (t8: T).(pr0 t8 v2)) H7 u1 H20) in (ex2_ind T 
(\lambda (t8: T).(pr0 v2 t8)) (\lambda (t8: T).(pr0 u2 t8)) (ex2 T (\lambda 
(t8: T).(pr0 (THead (Bind Abbr) v2 t4) t8)) (\lambda (t8: T).(pr0 (THead 
(Flat Appl) u2 (THead (Bind Abst) u t3)) t8))) (\lambda (x: T).(\lambda (H30: 
(pr0 v2 x)).(\lambda (H31: (pr0 u2 x)).(ex_intro2 T (\lambda (t8: T).(pr0 
(THead (Bind Abbr) v2 t4) t8)) (\lambda (t8: T).(pr0 (THead (Flat Appl) u2 
(THead (Bind Abst) u t3)) t8)) (THead (Bind Abbr) x t4) (pr0_comp v2 x H30 t4 
t4 (pr0_refl t4) (Bind Abbr)) (pr0_beta u u2 x H31 t3 t4 H8))))) (H28 u1 
(tlt_head_sx (Flat Appl) u1 (THead (Bind Abst) u t3)) v2 H29 u2 H14))))) t6 
H26)) t7 (sym_eq T t7 (THead (Bind Abst) u t3) H24) H25))) | (pr0_comp u0 u3 
H24 t7 t8 H25 k0) \Rightarrow (\lambda (H26: (eq T (THead k0 u0 t7) (THead 
(Bind Abst) u t3))).(\lambda (H27: (eq T (THead k0 u3 t8) t6)).((let H28 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow t7 | (TLRef _) \Rightarrow t7 | (THead _ _ t9) 
\Rightarrow t9])) (THead k0 u0 t7) (THead (Bind Abst) u t3) H26) in ((let H29 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead _ t9 _) 
\Rightarrow t9])) (THead k0 u0 t7) (THead (Bind Abst) u t3) H26) in ((let H30 
\def (f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) 
with [(TSort _) \Rightarrow k0 | (TLRef _) \Rightarrow k0 | (THead k1 _ _) 
\Rightarrow k1])) (THead k0 u0 t7) (THead (Bind Abst) u t3) H26) in (eq_ind K 
(Bind Abst) (\lambda (k1: K).((eq T u0 u) \to ((eq T t7 t3) \to ((eq T (THead 
k1 u3 t8) t6) \to ((pr0 u0 u3) \to ((pr0 t7 t8) \to (ex2 T (\lambda (t9: 
T).(pr0 (THead (Bind Abbr) v2 t4) t9)) (\lambda (t9: T).(pr0 (THead (Flat 
Appl) u2 t6) t9))))))))) (\lambda (H31: (eq T u0 u)).(eq_ind T u (\lambda 
(t9: T).((eq T t7 t3) \to ((eq T (THead (Bind Abst) u3 t8) t6) \to ((pr0 t9 
u3) \to ((pr0 t7 t8) \to (ex2 T (\lambda (t10: T).(pr0 (THead (Bind Abbr) v2 
t4) t10)) (\lambda (t10: T).(pr0 (THead (Flat Appl) u2 t6) t10)))))))) 
(\lambda (H32: (eq T t7 t3)).(eq_ind T t3 (\lambda (t9: T).((eq T (THead 
(Bind Abst) u3 t8) t6) \to ((pr0 u u3) \to ((pr0 t9 t8) \to (ex2 T (\lambda 
(t10: T).(pr0 (THead (Bind Abbr) v2 t4) t10)) (\lambda (t10: T).(pr0 (THead 
(Flat Appl) u2 t6) t10))))))) (\lambda (H33: (eq T (THead (Bind Abst) u3 t8) 
t6)).(eq_ind T (THead (Bind Abst) u3 t8) (\lambda (t9: T).((pr0 u u3) \to 
((pr0 t3 t8) \to (ex2 T (\lambda (t10: T).(pr0 (THead (Bind Abbr) v2 t4) 
t10)) (\lambda (t10: T).(pr0 (THead (Flat Appl) u2 t9) t10)))))) (\lambda (_: 
(pr0 u u3)).(\lambda (H35: (pr0 t3 t8)).(let H36 \def (eq_ind_r T t5 (\lambda 
(t9: T).(eq T (THead (Flat Appl) u1 t9) t)) H22 (THead (Bind Abst) u t3) H19) 
in (let H37 \def (eq_ind_r T t (\lambda (t9: T).(\forall (v: T).((tlt v t9) 
\to (\forall (t10: T).((pr0 v t10) \to (\forall (t11: T).((pr0 v t11) \to 
(ex2 T (\lambda (t12: T).(pr0 t10 t12)) (\lambda (t12: T).(pr0 t11 
t12)))))))))) H (THead (Flat Appl) u1 (THead (Bind Abst) u t3)) H36) in (let 
H38 \def (eq_ind T v1 (\lambda (t9: T).(pr0 t9 v2)) H7 u1 H20) in (ex2_ind T 
(\lambda (t9: T).(pr0 v2 t9)) (\lambda (t9: T).(pr0 u2 t9)) (ex2 T (\lambda 
(t9: T).(pr0 (THead (Bind Abbr) v2 t4) t9)) (\lambda (t9: T).(pr0 (THead 
(Flat Appl) u2 (THead (Bind Abst) u3 t8)) t9))) (\lambda (x: T).(\lambda 
(H39: (pr0 v2 x)).(\lambda (H40: (pr0 u2 x)).(ex2_ind T (\lambda (t9: T).(pr0 
t8 t9)) (\lambda (t9: T).(pr0 t4 t9)) (ex2 T (\lambda (t9: T).(pr0 (THead 
(Bind Abbr) v2 t4) t9)) (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 (THead 
(Bind Abst) u3 t8)) t9))) (\lambda (x0: T).(\lambda (H41: (pr0 t8 
x0)).(\lambda (H42: (pr0 t4 x0)).(ex_intro2 T (\lambda (t9: T).(pr0 (THead 
(Bind Abbr) v2 t4) t9)) (\lambda (t9: T).(pr0 (THead (Flat Appl) u2 (THead 
(Bind Abst) u3 t8)) t9)) (THead (Bind Abbr) x x0) (pr0_comp v2 x H39 t4 x0 
H42 (Bind Abbr)) (pr0_beta u3 u2 x H40 t8 x0 H41))))) (H37 t3 (tlt_trans 
(THead (Bind Abst) u t3) t3 (THead (Flat Appl) u1 (THead (Bind Abst) u t3)) 
(tlt_head_dx (Bind Abst) u t3) (tlt_head_dx (Flat Appl) u1 (THead (Bind Abst) 
u t3))) t8 H35 t4 H8))))) (H37 u1 (tlt_head_sx (Flat Appl) u1 (THead (Bind 
Abst) u t3)) v2 H38 u2 H14))))))) t6 H33)) t7 (sym_eq T t7 t3 H32))) u0 
(sym_eq T u0 u H31))) k0 (sym_eq K k0 (Bind Abst) H30))) H29)) H28)) H27 H24 
H25))) | (pr0_beta u0 v0 v3 H24 t7 t8 H25) \Rightarrow (\lambda (H26: (eq T 
(THead (Flat Appl) v0 (THead (Bind Abst) u0 t7)) (THead (Bind Abst) u 
t3))).(\lambda (H27: (eq T (THead (Bind Abbr) v3 t8) t6)).((let H28 \def 
(eq_ind T (THead (Flat Appl) v0 (THead (Bind Abst) u0 t7)) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 in 
K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) I (THead (Bind Abst) u t3) H26) in (False_ind ((eq T 
(THead (Bind Abbr) v3 t8) t6) \to ((pr0 v0 v3) \to ((pr0 t7 t8) \to (ex2 T 
(\lambda (t9: T).(pr0 (THead (Bind Abbr) v2 t4) t9)) (\lambda (t9: T).(pr0 
(THead (Flat Appl) u2 t6) t9)))))) H28)) H27 H24 H25))) | (pr0_upsilon b H24 
v0 v3 H25 u0 u3 H26 t7 t8 H27) \Rightarrow (\lambda (H28: (eq T (THead (Flat 
Appl) v0 (THead (Bind b) u0 t7)) (THead (Bind Abst) u t3))).(\lambda (H29: 
(eq T (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v3) t8)) t6)).((let 
H30 \def (eq_ind T (THead (Flat Appl) v0 (THead (Bind b) u0 t7)) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 in 
K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) I (THead (Bind Abst) u t3) H28) in (False_ind ((eq T 
(THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O v3) t8)) t6) \to ((not 
(eq B b Abst)) \to ((pr0 v0 v3) \to ((pr0 u0 u3) \to ((pr0 t7 t8) \to (ex2 T 
(\lambda (t9: T).(pr0 (THead (Bind Abbr) v2 t4) t9)) (\lambda (t9: T).(pr0 
(THead (Flat Appl) u2 t6) t9)))))))) H30)) H29 H24 H25 H26 H27))) | 
(pr0_delta u0 u3 H24 t7 t8 H25 w H26) \Rightarrow (\lambda (H27: (eq T (THead 
(Bind Abbr) u0 t7) (THead (Bind Abst) u t3))).(\lambda (H28: (eq T (THead 
(Bind Abbr) u3 w) t6)).((let H29 \def (eq_ind T (THead (Bind Abbr) u0 t7) 
(\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k0 _ _) \Rightarrow 
(match k0 in K return (\lambda (_: K).Prop) with [(Bind b) \Rightarrow (match 
b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow True | Abst 
\Rightarrow False | Void \Rightarrow False]) | (Flat _) \Rightarrow 
False])])) I (THead (Bind Abst) u t3) H27) in (False_ind ((eq T (THead (Bind 
Abbr) u3 w) t6) \to ((pr0 u0 u3) \to ((pr0 t7 t8) \to ((subst0 O u3 t8 w) \to 
(ex2 T (\lambda (t9: T).(pr0 (THead (Bind Abbr) v2 t4) t9)) (\lambda (t9: 
T).(pr0 (THead (Flat Appl) u2 t6) t9))))))) H29)) H28 H24 H25 H26))) | 
(pr0_zeta b H24 t7 t8 H25 u0) \Rightarrow (\lambda (H26: (eq T (THead (Bind 
b) u0 (lift (S O) O t7)) (THead (Bind Abst) u t3))).(\lambda (H27: (eq T t8 
t6)).((let H28 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map (f: ((nat 
\to nat))) (d: nat) (t9: T) on t9: T \def (match t9 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k0 u3 t10) 
\Rightarrow (THead k0 (lref_map f d u3) (lref_map f (s k0 d) t10))]) in 
lref_map) (\lambda (x: nat).(plus x (S O))) O t7) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t9: T) on t9: T \def (match 
t9 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k0 u3 t10) \Rightarrow (THead k0 (lref_map f d u3) (lref_map f (s k0 
d) t10))]) in lref_map) (\lambda (x: nat).(plus x (S O))) O t7) | (THead _ _ 
t9) \Rightarrow t9])) (THead (Bind b) u0 (lift (S O) O t7)) (THead (Bind 
Abst) u t3) H26) in ((let H29 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow u0 | (TLRef _) 
\Rightarrow u0 | (THead _ t9 _) \Rightarrow t9])) (THead (Bind b) u0 (lift (S 
O) O t7)) (THead (Bind Abst) u t3) H26) in ((let H30 \def (f_equal T B 
(\lambda (e: T).(match e in T return (\lambda (_: T).B) with [(TSort _) 
\Rightarrow b | (TLRef _) \Rightarrow b | (THead k0 _ _) \Rightarrow (match 
k0 in K return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) 
\Rightarrow b])])) (THead (Bind b) u0 (lift (S O) O t7)) (THead (Bind Abst) u 
t3) H26) in (eq_ind B Abst (\lambda (b0: B).((eq T u0 u) \to ((eq T (lift (S 
O) O t7) t3) \to ((eq T t8 t6) \to ((not (eq B b0 Abst)) \to ((pr0 t7 t8) \to 
(ex2 T (\lambda (t9: T).(pr0 (THead (Bind Abbr) v2 t4) t9)) (\lambda (t9: 
T).(pr0 (THead (Flat Appl) u2 t6) t9))))))))) (\lambda (H31: (eq T u0 
u)).(eq_ind T u (\lambda (_: T).((eq T (lift (S O) O t7) t3) \to ((eq T t8 
t6) \to ((not (eq B Abst Abst)) \to ((pr0 t7 t8) \to (ex2 T (\lambda (t10: 
T).(pr0 (THead (Bind Abbr) v2 t4) t10)) (\lambda (t10: T).(pr0 (THead (Flat 
Appl) u2 t6) t10)))))))) (\lambda (H32: (eq T (lift (S O) O t7) t3)).(eq_ind 
T (lift (S O) O t7) (\lambda (_: T).((eq T t8 t6) \to ((not (eq B Abst Abst)) 
\to ((pr0 t7 t8) \to (ex2 T (\lambda (t10: T).(pr0 (THead (Bind Abbr) v2 t4) 
t10)) (\lambda (t10: T).(pr0 (THead (Flat Appl) u2 t6) t10))))))) (\lambda 
(H33: (eq T t8 t6)).(eq_ind T t6 (\lambda (t9: T).((not (eq B Abst Abst)) \to 
((pr0 t7 t9) \to (ex2 T (\lambda (t10: T).(pr0 (THead (Bind Abbr) v2 t4) 
t10)) (\lambda (t10: T).(pr0 (THead (Flat Appl) u2 t6) t10)))))) (\lambda 
(H34: (not (eq B Abst Abst))).(\lambda (_: (pr0 t7 t6)).(let H36 \def (match 
(H34 (refl_equal B Abst)) in False return (\lambda (_: False).(ex2 T (\lambda 
(t9: T).(pr0 (THead (Bind Abbr) v2 t4) t9)) (\lambda (t9: T).(pr0 (THead 
(Flat Appl) u2 t6) t9)))) with []) in H36))) t8 (sym_eq T t8 t6 H33))) t3 
H32)) u0 (sym_eq T u0 u H31))) b (sym_eq B b Abst H30))) H29)) H28)) H27 H24 
H25))) | (pr0_tau t7 t8 H24 u0) \Rightarrow (\lambda (H25: (eq T (THead (Flat 
Cast) u0 t7) (THead (Bind Abst) u t3))).(\lambda (H26: (eq T t8 t6)).((let 
H27 \def (eq_ind T (THead (Flat Cast) u0 t7) (\lambda (e: T).(match e in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind Abst) u t3) H25) in (False_ind ((eq T t8 t6) \to 
((pr0 t7 t8) \to (ex2 T (\lambda (t9: T).(pr0 (THead (Bind Abbr) v2 t4) t9)) 
(\lambda (t9: T).(pr0 (THead (Flat Appl) u2 t6) t9))))) H27)) H26 H24)))]) in 
(H24 (refl_equal T (THead (Bind Abst) u t3)) (refl_equal T t6))))) k H21)))) 
H18)) H17))))) t2 H13)) t H11 H12 H9 H10))) | (pr0_beta u0 v0 v3 H9 t5 t6 
H10) \Rightarrow (\lambda (H11: (eq T (THead (Flat Appl) v0 (THead (Bind 
Abst) u0 t5)) t)).(\lambda (H12: (eq T (THead (Bind Abbr) v3 t6) t2)).(eq_ind 
T (THead (Flat Appl) v0 (THead (Bind Abst) u0 t5)) (\lambda (_: T).((eq T 
(THead (Bind Abbr) v3 t6) t2) \to ((pr0 v0 v3) \to ((pr0 t5 t6) \to (ex2 T 
(\lambda (t8: T).(pr0 (THead (Bind Abbr) v2 t4) t8)) (\lambda (t8: T).(pr0 t2 
t8))))))) (\lambda (H13: (eq T (THead (Bind Abbr) v3 t6) t2)).(eq_ind T 
(THead (Bind Abbr) v3 t6) (\lambda (t7: T).((pr0 v0 v3) \to ((pr0 t5 t6) \to 
(ex2 T (\lambda (t8: T).(pr0 (THead (Bind Abbr) v2 t4) t8)) (\lambda (t8: 
T).(pr0 t7 t8)))))) (\lambda (H14: (pr0 v0 v3)).(\lambda (H15: (pr0 t5 
t6)).(let H16 \def (eq_ind_r T t (\lambda (t7: T).(eq T (THead (Flat Appl) v1 
(THead (Bind Abst) u t3)) t7)) H4 (THead (Flat Appl) v0 (THead (Bind Abst) u0 
t5)) H11) in (let H17 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow v1 | (TLRef _) \Rightarrow v1 
| (THead _ t7 _) \Rightarrow t7])) (THead (Flat Appl) v1 (THead (Bind Abst) u 
t3)) (THead (Flat Appl) v0 (THead (Bind Abst) u0 t5)) H16) in ((let H18 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow u | (TLRef _) \Rightarrow u | (THead _ _ t7) 
\Rightarrow (match t7 in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u | (TLRef _) \Rightarrow u | (THead _ t8 _) \Rightarrow t8])])) 
(THead (Flat Appl) v1 (THead (Bind Abst) u t3)) (THead (Flat Appl) v0 (THead 
(Bind Abst) u0 t5)) H16) in ((let H19 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t3 | 
(TLRef _) \Rightarrow t3 | (THead _ _ t7) \Rightarrow (match t7 in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow t3 | (TLRef _) \Rightarrow t3 
| (THead _ _ t8) \Rightarrow t8])])) (THead (Flat Appl) v1 (THead (Bind Abst) 
u t3)) (THead (Flat Appl) v0 (THead (Bind Abst) u0 t5)) H16) in (\lambda (_: 
(eq T u u0)).(\lambda (H21: (eq T v1 v0)).(let H22 \def (eq_ind_r T t 
(\lambda (t7: T).(\forall (v: T).((tlt v t7) \to (\forall (t8: T).((pr0 v t8) 
\to (\forall (t9: T).((pr0 v t9) \to (ex2 T (\lambda (t10: T).(pr0 t8 t10)) 
(\lambda (t10: T).(pr0 t9 t10)))))))))) H (THead (Flat Appl) v0 (THead (Bind 
Abst) u0 t5)) H11) in (let H23 \def (eq_ind T v1 (\lambda (t7: T).(pr0 t7 
v2)) H7 v0 H21) in (let H24 \def (eq_ind T t3 (\lambda (t7: T).(pr0 t7 t4)) 
H8 t5 H19) in (ex2_ind T (\lambda (t7: T).(pr0 t4 t7)) (\lambda (t7: T).(pr0 
t6 t7)) (ex2 T (\lambda (t7: T).(pr0 (THead (Bind Abbr) v2 t4) t7)) (\lambda 
(t7: T).(pr0 (THead (Bind Abbr) v3 t6) t7))) (\lambda (x: T).(\lambda (H25: 
(pr0 t4 x)).(\lambda (H26: (pr0 t6 x)).(ex2_ind T (\lambda (t7: T).(pr0 v2 
t7)) (\lambda (t7: T).(pr0 v3 t7)) (ex2 T (\lambda (t7: T).(pr0 (THead (Bind 
Abbr) v2 t4) t7)) (\lambda (t7: T).(pr0 (THead (Bind Abbr) v3 t6) t7))) 
(\lambda (x0: T).(\lambda (H27: (pr0 v2 x0)).(\lambda (H28: (pr0 v3 
x0)).(ex_intro2 T (\lambda (t7: T).(pr0 (THead (Bind Abbr) v2 t4) t7)) 
(\lambda (t7: T).(pr0 (THead (Bind Abbr) v3 t6) t7)) (THead (Bind Abbr) x0 x) 
(pr0_comp v2 x0 H27 t4 x H25 (Bind Abbr)) (pr0_comp v3 x0 H28 t6 x H26 (Bind 
Abbr)))))) (H22 v0 (tlt_head_sx (Flat Appl) v0 (THead (Bind Abst) u0 t5)) v2 
H23 v3 H14))))) (H22 t5 (tlt_trans (THead (Bind Abst) u0 t5) t5 (THead (Flat 
Appl) v0 (THead (Bind Abst) u0 t5)) (tlt_head_dx (Bind Abst) u0 t5) 
(tlt_head_dx (Flat Appl) v0 (THead (Bind Abst) u0 t5))) t4 H24 t6 H15)))))))) 
H18)) H17))))) t2 H13)) t H11 H12 H9 H10))) | (pr0_upsilon b H9 v0 v3 H10 u1 
u2 H11 t5 t6 H12) \Rightarrow (\lambda (H13: (eq T (THead (Flat Appl) v0 
(THead (Bind b) u1 t5)) t)).(\lambda (H14: (eq T (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v3) t6)) t2)).(eq_ind T (THead (Flat Appl) v0 
(THead (Bind b) u1 t5)) (\lambda (_: T).((eq T (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v3) t6)) t2) \to ((not (eq B b Abst)) \to ((pr0 v0 
v3) \to ((pr0 u1 u2) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead 
(Bind Abbr) v2 t4) t8)) (\lambda (t8: T).(pr0 t2 t8))))))))) (\lambda (H15: 
(eq T (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v3) t6)) 
t2)).(eq_ind T (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v3) t6)) 
(\lambda (t7: T).((not (eq B b Abst)) \to ((pr0 v0 v3) \to ((pr0 u1 u2) \to 
((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead (Bind Abbr) v2 t4) t8)) 
(\lambda (t8: T).(pr0 t7 t8)))))))) (\lambda (H16: (not (eq B b 
Abst))).(\lambda (_: (pr0 v0 v3)).(\lambda (_: (pr0 u1 u2)).(\lambda (_: (pr0 
t5 t6)).(let H20 \def (eq_ind_r T t (\lambda (t7: T).(eq T (THead (Flat Appl) 
v1 (THead (Bind Abst) u t3)) t7)) H4 (THead (Flat Appl) v0 (THead (Bind b) u1 
t5)) H13) in (let H21 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow v1 | (TLRef _) \Rightarrow v1 
| (THead _ t7 _) \Rightarrow t7])) (THead (Flat Appl) v1 (THead (Bind Abst) u 
t3)) (THead (Flat Appl) v0 (THead (Bind b) u1 t5)) H20) in ((let H22 \def 
(f_equal T B (\lambda (e: T).(match e in T return (\lambda (_: T).B) with 
[(TSort _) \Rightarrow Abst | (TLRef _) \Rightarrow Abst | (THead _ _ t7) 
\Rightarrow (match t7 in T return (\lambda (_: T).B) with [(TSort _) 
\Rightarrow Abst | (TLRef _) \Rightarrow Abst | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | 
(Flat _) \Rightarrow Abst])])])) (THead (Flat Appl) v1 (THead (Bind Abst) u 
t3)) (THead (Flat Appl) v0 (THead (Bind b) u1 t5)) H20) in ((let H23 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow u | (TLRef _) \Rightarrow u | (THead _ _ t7) 
\Rightarrow (match t7 in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u | (TLRef _) \Rightarrow u | (THead _ t8 _) \Rightarrow t8])])) 
(THead (Flat Appl) v1 (THead (Bind Abst) u t3)) (THead (Flat Appl) v0 (THead 
(Bind b) u1 t5)) H20) in ((let H24 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t3 | (TLRef _) 
\Rightarrow t3 | (THead _ _ t7) \Rightarrow (match t7 in T return (\lambda 
(_: T).T) with [(TSort _) \Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead 
_ _ t8) \Rightarrow t8])])) (THead (Flat Appl) v1 (THead (Bind Abst) u t3)) 
(THead (Flat Appl) v0 (THead (Bind b) u1 t5)) H20) in (\lambda (_: (eq T u 
u1)).(\lambda (H26: (eq B Abst b)).(\lambda (_: (eq T v1 v0)).(eq_ind B Abst 
(\lambda (b0: B).(ex2 T (\lambda (t7: T).(pr0 (THead (Bind Abbr) v2 t4) t7)) 
(\lambda (t7: T).(pr0 (THead (Bind b0) u2 (THead (Flat Appl) (lift (S O) O 
v3) t6)) t7)))) (let H28 \def (eq_ind_r B b (\lambda (b0: B).(not (eq B b0 
Abst))) H16 Abst H26) in (let H29 \def (match (H28 (refl_equal B Abst)) in 
False return (\lambda (_: False).(ex2 T (\lambda (t7: T).(pr0 (THead (Bind 
Abbr) v2 t4) t7)) (\lambda (t7: T).(pr0 (THead (Bind Abst) u2 (THead (Flat 
Appl) (lift (S O) O v3) t6)) t7)))) with []) in H29)) b H26))))) H23)) H22)) 
H21))))))) t2 H15)) t H13 H14 H9 H10 H11 H12))) | (pr0_delta u1 u2 H9 t5 t6 
H10 w H11) \Rightarrow (\lambda (H12: (eq T (THead (Bind Abbr) u1 t5) 
t)).(\lambda (H13: (eq T (THead (Bind Abbr) u2 w) t2)).(eq_ind T (THead (Bind 
Abbr) u1 t5) (\lambda (_: T).((eq T (THead (Bind Abbr) u2 w) t2) \to ((pr0 u1 
u2) \to ((pr0 t5 t6) \to ((subst0 O u2 t6 w) \to (ex2 T (\lambda (t8: T).(pr0 
(THead (Bind Abbr) v2 t4) t8)) (\lambda (t8: T).(pr0 t2 t8)))))))) (\lambda 
(H14: (eq T (THead (Bind Abbr) u2 w) t2)).(eq_ind T (THead (Bind Abbr) u2 w) 
(\lambda (t7: T).((pr0 u1 u2) \to ((pr0 t5 t6) \to ((subst0 O u2 t6 w) \to 
(ex2 T (\lambda (t8: T).(pr0 (THead (Bind Abbr) v2 t4) t8)) (\lambda (t8: 
T).(pr0 t7 t8))))))) (\lambda (_: (pr0 u1 u2)).(\lambda (_: (pr0 t5 
t6)).(\lambda (_: (subst0 O u2 t6 w)).(let H18 \def (eq_ind_r T t (\lambda 
(t7: T).(eq T (THead (Flat Appl) v1 (THead (Bind Abst) u t3)) t7)) H4 (THead 
(Bind Abbr) u1 t5) H12) in (let H19 \def (eq_ind T (THead (Flat Appl) v1 
(THead (Bind Abst) u t3)) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind 
Abbr) u1 t5) H18) in (False_ind (ex2 T (\lambda (t7: T).(pr0 (THead (Bind 
Abbr) v2 t4) t7)) (\lambda (t7: T).(pr0 (THead (Bind Abbr) u2 w) t7))) 
H19)))))) t2 H14)) t H12 H13 H9 H10 H11))) | (pr0_zeta b H9 t5 t6 H10 u0) 
\Rightarrow (\lambda (H11: (eq T (THead (Bind b) u0 (lift (S O) O t5)) 
t)).(\lambda (H12: (eq T t6 t2)).(eq_ind T (THead (Bind b) u0 (lift (S O) O 
t5)) (\lambda (_: T).((eq T t6 t2) \to ((not (eq B b Abst)) \to ((pr0 t5 t6) 
\to (ex2 T (\lambda (t8: T).(pr0 (THead (Bind Abbr) v2 t4) t8)) (\lambda (t8: 
T).(pr0 t2 t8))))))) (\lambda (H13: (eq T t6 t2)).(eq_ind T t2 (\lambda (t7: 
T).((not (eq B b Abst)) \to ((pr0 t5 t7) \to (ex2 T (\lambda (t8: T).(pr0 
(THead (Bind Abbr) v2 t4) t8)) (\lambda (t8: T).(pr0 t2 t8)))))) (\lambda (_: 
(not (eq B b Abst))).(\lambda (_: (pr0 t5 t2)).(let H16 \def (eq_ind_r T t 
(\lambda (t7: T).(eq T (THead (Flat Appl) v1 (THead (Bind Abst) u t3)) t7)) 
H4 (THead (Bind b) u0 (lift (S O) O t5)) H11) in (let H17 \def (eq_ind T 
(THead (Flat Appl) v1 (THead (Bind Abst) u t3)) (\lambda (ee: T).(match ee in 
T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind b) u0 (lift (S O) O t5)) H16) in (False_ind (ex2 T 
(\lambda (t7: T).(pr0 (THead (Bind Abbr) v2 t4) t7)) (\lambda (t7: T).(pr0 t2 
t7))) H17))))) t6 (sym_eq T t6 t2 H13))) t H11 H12 H9 H10))) | (pr0_tau t5 t6 
H9 u0) \Rightarrow (\lambda (H10: (eq T (THead (Flat Cast) u0 t5) 
t)).(\lambda (H11: (eq T t6 t2)).(eq_ind T (THead (Flat Cast) u0 t5) (\lambda 
(_: T).((eq T t6 t2) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead 
(Bind Abbr) v2 t4) t8)) (\lambda (t8: T).(pr0 t2 t8)))))) (\lambda (H12: (eq 
T t6 t2)).(eq_ind T t2 (\lambda (t7: T).((pr0 t5 t7) \to (ex2 T (\lambda (t8: 
T).(pr0 (THead (Bind Abbr) v2 t4) t8)) (\lambda (t8: T).(pr0 t2 t8))))) 
(\lambda (_: (pr0 t5 t2)).(let H14 \def (eq_ind_r T t (\lambda (t7: T).(eq T 
(THead (Flat Appl) v1 (THead (Bind Abst) u t3)) t7)) H4 (THead (Flat Cast) u0 
t5) H10) in (let H15 \def (eq_ind T (THead (Flat Appl) v1 (THead (Bind Abst) 
u t3)) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat f) \Rightarrow (match f in F return (\lambda (_: 
F).Prop) with [Appl \Rightarrow True | Cast \Rightarrow False])])])) I (THead 
(Flat Cast) u0 t5) H14) in (False_ind (ex2 T (\lambda (t7: T).(pr0 (THead 
(Bind Abbr) v2 t4) t7)) (\lambda (t7: T).(pr0 t2 t7))) H15)))) t6 (sym_eq T 
t6 t2 H12))) t H10 H11 H9)))]) in (H9 (refl_equal T t) (refl_equal T t2))))) 
t1 H6)) t H4 H5 H2 H3))) | (pr0_upsilon b H2 v1 v2 H3 u1 u2 H4 t3 t4 H5) 
\Rightarrow (\lambda (H6: (eq T (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) 
t)).(\lambda (H7: (eq T (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O 
v2) t4)) t1)).(eq_ind T (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) 
(\lambda (_: T).((eq T (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O 
v2) t4)) t1) \to ((not (eq B b Abst)) \to ((pr0 v1 v2) \to ((pr0 u1 u2) \to 
((pr0 t3 t4) \to (ex2 T (\lambda (t6: T).(pr0 t1 t6)) (\lambda (t6: T).(pr0 
t2 t6))))))))) (\lambda (H8: (eq T (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4)) t1)).(eq_ind T (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4)) (\lambda (t5: T).((not (eq B b Abst)) \to ((pr0 v1 v2) 
\to ((pr0 u1 u2) \to ((pr0 t3 t4) \to (ex2 T (\lambda (t6: T).(pr0 t5 t6)) 
(\lambda (t6: T).(pr0 t2 t6)))))))) (\lambda (H9: (not (eq B b 
Abst))).(\lambda (H10: (pr0 v1 v2)).(\lambda (H11: (pr0 u1 u2)).(\lambda 
(H12: (pr0 t3 t4)).(let H13 \def (match H1 in pr0 return (\lambda (t5: 
T).(\lambda (t6: T).(\lambda (_: (pr0 t5 t6)).((eq T t5 t) \to ((eq T t6 t2) 
\to (ex2 T (\lambda (t7: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift 
(S O) O v2) t4)) t7)) (\lambda (t7: T).(pr0 t2 t7)))))))) with [(pr0_refl t5) 
\Rightarrow (\lambda (H13: (eq T t5 t)).(\lambda (H14: (eq T t5 t2)).(eq_ind 
T t (\lambda (t6: T).((eq T t6 t2) \to (ex2 T (\lambda (t7: T).(pr0 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t7)) (\lambda (t7: 
T).(pr0 t2 t7))))) (\lambda (H15: (eq T t t2)).(eq_ind T t2 (\lambda (_: 
T).(ex2 T (\lambda (t7: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift 
(S O) O v2) t4)) t7)) (\lambda (t7: T).(pr0 t2 t7)))) (let H16 \def (eq_ind_r 
T t (\lambda (t6: T).(eq T t6 t2)) H15 (THead (Flat Appl) v1 (THead (Bind b) 
u1 t3)) H6) in (eq_ind T (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) 
(\lambda (t6: T).(ex2 T (\lambda (t7: T).(pr0 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) t7)) (\lambda (t7: T).(pr0 t6 t7)))) (let H17 
\def (eq_ind_r T t (\lambda (t6: T).(eq T t5 t6)) H13 (THead (Flat Appl) v1 
(THead (Bind b) u1 t3)) H6) in (let H18 \def (eq_ind_r T t (\lambda (t6: 
T).(\forall (v: T).((tlt v t6) \to (\forall (t7: T).((pr0 v t7) \to (\forall 
(t8: T).((pr0 v t8) \to (ex2 T (\lambda (t9: T).(pr0 t7 t9)) (\lambda (t9: 
T).(pr0 t8 t9)))))))))) H (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) H6) 
in (ex2_sym T (pr0 (THead (Flat Appl) v1 (THead (Bind b) u1 t3))) (pr0 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4))) 
(pr0_confluence__pr0_cong_upsilon_refl b H9 u1 u2 H11 t3 t4 H12 v1 v2 v2 H10 
(pr0_refl v2))))) t2 H16)) t (sym_eq T t t2 H15))) t5 (sym_eq T t5 t H13) 
H14))) | (pr0_comp u0 u3 H13 t5 t6 H14 k) \Rightarrow (\lambda (H15: (eq T 
(THead k u0 t5) t)).(\lambda (H16: (eq T (THead k u3 t6) t2)).(eq_ind T 
(THead k u0 t5) (\lambda (_: T).((eq T (THead k u3 t6) t2) \to ((pr0 u0 u3) 
\to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4)) t8)) (\lambda (t8: T).(pr0 t2 t8))))))) 
(\lambda (H17: (eq T (THead k u3 t6) t2)).(eq_ind T (THead k u3 t6) (\lambda 
(t7: T).((pr0 u0 u3) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t8)) (\lambda (t8: 
T).(pr0 t7 t8)))))) (\lambda (H18: (pr0 u0 u3)).(\lambda (H19: (pr0 t5 
t6)).(let H20 \def (eq_ind_r T t (\lambda (t7: T).(eq T (THead (Flat Appl) v1 
(THead (Bind b) u1 t3)) t7)) H6 (THead k u0 t5) H15) in (let H21 \def 
(f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) with 
[(TSort _) \Rightarrow (Flat Appl) | (TLRef _) \Rightarrow (Flat Appl) | 
(THead k0 _ _) \Rightarrow k0])) (THead (Flat Appl) v1 (THead (Bind b) u1 
t3)) (THead k u0 t5) H20) in ((let H22 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow v1 | 
(TLRef _) \Rightarrow v1 | (THead _ t7 _) \Rightarrow t7])) (THead (Flat 
Appl) v1 (THead (Bind b) u1 t3)) (THead k u0 t5) H20) in ((let H23 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow (THead (Bind b) u1 t3) | (TLRef _) \Rightarrow (THead 
(Bind b) u1 t3) | (THead _ _ t7) \Rightarrow t7])) (THead (Flat Appl) v1 
(THead (Bind b) u1 t3)) (THead k u0 t5) H20) in (\lambda (H24: (eq T v1 
u0)).(\lambda (H25: (eq K (Flat Appl) k)).(eq_ind K (Flat Appl) (\lambda (k0: 
K).(ex2 T (\lambda (t7: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift 
(S O) O v2) t4)) t7)) (\lambda (t7: T).(pr0 (THead k0 u3 t6) t7)))) (let H26 
\def (eq_ind_r K k (\lambda (k0: K).(eq T (THead k0 u0 t5) t)) H15 (Flat 
Appl) H25) in (let H27 \def (eq_ind_r T t5 (\lambda (t7: T).(pr0 t7 t6)) H19 
(THead (Bind b) u1 t3) H23) in (let H28 \def (match H27 in pr0 return 
(\lambda (t7: T).(\lambda (t8: T).(\lambda (_: (pr0 t7 t8)).((eq T t7 (THead 
(Bind b) u1 t3)) \to ((eq T t8 t6) \to (ex2 T (\lambda (t9: T).(pr0 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t9)) (\lambda (t9: 
T).(pr0 (THead (Flat Appl) u3 t6) t9)))))))) with [(pr0_refl t7) \Rightarrow 
(\lambda (H28: (eq T t7 (THead (Bind b) u1 t3))).(\lambda (H29: (eq T t7 
t6)).(eq_ind T (THead (Bind b) u1 t3) (\lambda (t8: T).((eq T t8 t6) \to (ex2 
T (\lambda (t9: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O 
v2) t4)) t9)) (\lambda (t9: T).(pr0 (THead (Flat Appl) u3 t6) t9))))) 
(\lambda (H30: (eq T (THead (Bind b) u1 t3) t6)).(eq_ind T (THead (Bind b) u1 
t3) (\lambda (t8: T).(ex2 T (\lambda (t9: T).(pr0 (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4)) t9)) (\lambda (t9: T).(pr0 (THead (Flat 
Appl) u3 t8) t9)))) (let H31 \def (eq_ind_r T t5 (\lambda (t8: T).(eq T 
(THead (Flat Appl) u0 t8) t)) H26 (THead (Bind b) u1 t3) H23) in (let H32 
\def (eq_ind_r T t (\lambda (t8: T).(\forall (v: T).((tlt v t8) \to (\forall 
(t9: T).((pr0 v t9) \to (\forall (t10: T).((pr0 v t10) \to (ex2 T (\lambda 
(t11: T).(pr0 t9 t11)) (\lambda (t11: T).(pr0 t10 t11)))))))))) H (THead 
(Flat Appl) u0 (THead (Bind b) u1 t3)) H31) in (let H33 \def (eq_ind T v1 
(\lambda (t8: T).(pr0 t8 v2)) H10 u0 H24) in (ex2_ind T (\lambda (t8: T).(pr0 
v2 t8)) (\lambda (t8: T).(pr0 u3 t8)) (ex2 T (\lambda (t8: T).(pr0 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t8)) (\lambda (t8: 
T).(pr0 (THead (Flat Appl) u3 (THead (Bind b) u1 t3)) t8))) (\lambda (x: 
T).(\lambda (H34: (pr0 v2 x)).(\lambda (H35: (pr0 u3 x)).(ex2_sym T (pr0 
(THead (Flat Appl) u3 (THead (Bind b) u1 t3))) (pr0 (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4))) (pr0_confluence__pr0_cong_upsilon_refl b 
H9 u1 u2 H11 t3 t4 H12 u3 v2 x H35 H34))))) (H32 u0 (tlt_head_sx (Flat Appl) 
u0 (THead (Bind b) u1 t3)) v2 H33 u3 H18))))) t6 H30)) t7 (sym_eq T t7 (THead 
(Bind b) u1 t3) H28) H29))) | (pr0_comp u4 u5 H28 t7 t8 H29 k0) \Rightarrow 
(\lambda (H30: (eq T (THead k0 u4 t7) (THead (Bind b) u1 t3))).(\lambda (H31: 
(eq T (THead k0 u5 t8) t6)).((let H32 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t7 | 
(TLRef _) \Rightarrow t7 | (THead _ _ t9) \Rightarrow t9])) (THead k0 u4 t7) 
(THead (Bind b) u1 t3) H30) in ((let H33 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u4 | 
(TLRef _) \Rightarrow u4 | (THead _ t9 _) \Rightarrow t9])) (THead k0 u4 t7) 
(THead (Bind b) u1 t3) H30) in ((let H34 \def (f_equal T K (\lambda (e: 
T).(match e in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k0 | 
(TLRef _) \Rightarrow k0 | (THead k1 _ _) \Rightarrow k1])) (THead k0 u4 t7) 
(THead (Bind b) u1 t3) H30) in (eq_ind K (Bind b) (\lambda (k1: K).((eq T u4 
u1) \to ((eq T t7 t3) \to ((eq T (THead k1 u5 t8) t6) \to ((pr0 u4 u5) \to 
((pr0 t7 t8) \to (ex2 T (\lambda (t9: T).(pr0 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) t9)) (\lambda (t9: T).(pr0 (THead (Flat Appl) u3 
t6) t9))))))))) (\lambda (H35: (eq T u4 u1)).(eq_ind T u1 (\lambda (t9: 
T).((eq T t7 t3) \to ((eq T (THead (Bind b) u5 t8) t6) \to ((pr0 t9 u5) \to 
((pr0 t7 t8) \to (ex2 T (\lambda (t10: T).(pr0 (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4)) t10)) (\lambda (t10: T).(pr0 (THead (Flat 
Appl) u3 t6) t10)))))))) (\lambda (H36: (eq T t7 t3)).(eq_ind T t3 (\lambda 
(t9: T).((eq T (THead (Bind b) u5 t8) t6) \to ((pr0 u1 u5) \to ((pr0 t9 t8) 
\to (ex2 T (\lambda (t10: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift 
(S O) O v2) t4)) t10)) (\lambda (t10: T).(pr0 (THead (Flat Appl) u3 t6) 
t10))))))) (\lambda (H37: (eq T (THead (Bind b) u5 t8) t6)).(eq_ind T (THead 
(Bind b) u5 t8) (\lambda (t9: T).((pr0 u1 u5) \to ((pr0 t3 t8) \to (ex2 T 
(\lambda (t10: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O 
v2) t4)) t10)) (\lambda (t10: T).(pr0 (THead (Flat Appl) u3 t9) t10)))))) 
(\lambda (H38: (pr0 u1 u5)).(\lambda (H39: (pr0 t3 t8)).(let H40 \def 
(eq_ind_r T t5 (\lambda (t9: T).(eq T (THead (Flat Appl) u0 t9) t)) H26 
(THead (Bind b) u1 t3) H23) in (let H41 \def (eq_ind_r T t (\lambda (t9: 
T).(\forall (v: T).((tlt v t9) \to (\forall (t10: T).((pr0 v t10) \to 
(\forall (t11: T).((pr0 v t11) \to (ex2 T (\lambda (t12: T).(pr0 t10 t12)) 
(\lambda (t12: T).(pr0 t11 t12)))))))))) H (THead (Flat Appl) u0 (THead (Bind 
b) u1 t3)) H40) in (let H42 \def (eq_ind T v1 (\lambda (t9: T).(pr0 t9 v2)) 
H10 u0 H24) in (ex2_ind T (\lambda (t9: T).(pr0 v2 t9)) (\lambda (t9: T).(pr0 
u3 t9)) (ex2 T (\lambda (t9: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4)) t9)) (\lambda (t9: T).(pr0 (THead (Flat Appl) u3 
(THead (Bind b) u5 t8)) t9))) (\lambda (x: T).(\lambda (H43: (pr0 v2 
x)).(\lambda (H44: (pr0 u3 x)).(ex2_ind T (\lambda (t9: T).(pr0 t8 t9)) 
(\lambda (t9: T).(pr0 t4 t9)) (ex2 T (\lambda (t9: T).(pr0 (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t4)) t9)) (\lambda (t9: T).(pr0 (THead 
(Flat Appl) u3 (THead (Bind b) u5 t8)) t9))) (\lambda (x0: T).(\lambda (H45: 
(pr0 t8 x0)).(\lambda (H46: (pr0 t4 x0)).(ex2_ind T (\lambda (t9: T).(pr0 u5 
t9)) (\lambda (t9: T).(pr0 u2 t9)) (ex2 T (\lambda (t9: T).(pr0 (THead (Bind 
b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t9)) (\lambda (t9: T).(pr0 
(THead (Flat Appl) u3 (THead (Bind b) u5 t8)) t9))) (\lambda (x1: T).(\lambda 
(H47: (pr0 u5 x1)).(\lambda (H48: (pr0 u2 x1)).(ex2_sym T (pr0 (THead (Flat 
Appl) u3 (THead (Bind b) u5 t8))) (pr0 (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4))) (pr0_confluence__pr0_cong_upsilon_cong b H9 u3 v2 x 
H44 H43 t8 t4 x0 H45 H46 u5 u2 x1 H47 H48))))) (H41 u1 (tlt_trans (THead 
(Bind b) u1 t3) u1 (THead (Flat Appl) u0 (THead (Bind b) u1 t3)) (tlt_head_sx 
(Bind b) u1 t3) (tlt_head_dx (Flat Appl) u0 (THead (Bind b) u1 t3))) u5 H38 
u2 H11))))) (H41 t3 (tlt_trans (THead (Bind b) u1 t3) t3 (THead (Flat Appl) 
u0 (THead (Bind b) u1 t3)) (tlt_head_dx (Bind b) u1 t3) (tlt_head_dx (Flat 
Appl) u0 (THead (Bind b) u1 t3))) t8 H39 t4 H12))))) (H41 u0 (tlt_head_sx 
(Flat Appl) u0 (THead (Bind b) u1 t3)) v2 H42 u3 H18))))))) t6 H37)) t7 
(sym_eq T t7 t3 H36))) u4 (sym_eq T u4 u1 H35))) k0 (sym_eq K k0 (Bind b) 
H34))) H33)) H32)) H31 H28 H29))) | (pr0_beta u v0 v3 H28 t7 t8 H29) 
\Rightarrow (\lambda (H30: (eq T (THead (Flat Appl) v0 (THead (Bind Abst) u 
t7)) (THead (Bind b) u1 t3))).(\lambda (H31: (eq T (THead (Bind Abbr) v3 t8) 
t6)).((let H32 \def (eq_ind T (THead (Flat Appl) v0 (THead (Bind Abst) u t7)) 
(\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k0 _ _) \Rightarrow 
(match k0 in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False 
| (Flat _) \Rightarrow True])])) I (THead (Bind b) u1 t3) H30) in (False_ind 
((eq T (THead (Bind Abbr) v3 t8) t6) \to ((pr0 v0 v3) \to ((pr0 t7 t8) \to 
(ex2 T (\lambda (t9: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) t9)) (\lambda (t9: T).(pr0 (THead (Flat Appl) u3 t6) t9)))))) 
H32)) H31 H28 H29))) | (pr0_upsilon b0 H28 v0 v3 H29 u4 u5 H30 t7 t8 H31) 
\Rightarrow (\lambda (H32: (eq T (THead (Flat Appl) v0 (THead (Bind b0) u4 
t7)) (THead (Bind b) u1 t3))).(\lambda (H33: (eq T (THead (Bind b0) u5 (THead 
(Flat Appl) (lift (S O) O v3) t8)) t6)).((let H34 \def (eq_ind T (THead (Flat 
Appl) v0 (THead (Bind b0) u4 t7)) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind b) u1 t3) H32) in (False_ind ((eq T (THead (Bind b0) 
u5 (THead (Flat Appl) (lift (S O) O v3) t8)) t6) \to ((not (eq B b0 Abst)) 
\to ((pr0 v0 v3) \to ((pr0 u4 u5) \to ((pr0 t7 t8) \to (ex2 T (\lambda (t9: 
T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t9)) 
(\lambda (t9: T).(pr0 (THead (Flat Appl) u3 t6) t9)))))))) H34)) H33 H28 H29 
H30 H31))) | (pr0_delta u4 u5 H28 t7 t8 H29 w H30) \Rightarrow (\lambda (H31: 
(eq T (THead (Bind Abbr) u4 t7) (THead (Bind b) u1 t3))).(\lambda (H32: (eq T 
(THead (Bind Abbr) u5 w) t6)).((let H33 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t7 | 
(TLRef _) \Rightarrow t7 | (THead _ _ t9) \Rightarrow t9])) (THead (Bind 
Abbr) u4 t7) (THead (Bind b) u1 t3) H31) in ((let H34 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u4 | (TLRef _) \Rightarrow u4 | (THead _ t9 _) \Rightarrow t9])) 
(THead (Bind Abbr) u4 t7) (THead (Bind b) u1 t3) H31) in ((let H35 \def 
(f_equal T B (\lambda (e: T).(match e in T return (\lambda (_: T).B) with 
[(TSort _) \Rightarrow Abbr | (TLRef _) \Rightarrow Abbr | (THead k0 _ _) 
\Rightarrow (match k0 in K return (\lambda (_: K).B) with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) (THead (Bind Abbr) u4 t7) 
(THead (Bind b) u1 t3) H31) in (eq_ind B Abbr (\lambda (b0: B).((eq T u4 u1) 
\to ((eq T t7 t3) \to ((eq T (THead (Bind Abbr) u5 w) t6) \to ((pr0 u4 u5) 
\to ((pr0 t7 t8) \to ((subst0 O u5 t8 w) \to (ex2 T (\lambda (t9: T).(pr0 
(THead (Bind b0) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t9)) (\lambda 
(t9: T).(pr0 (THead (Flat Appl) u3 t6) t9)))))))))) (\lambda (H36: (eq T u4 
u1)).(eq_ind T u1 (\lambda (t9: T).((eq T t7 t3) \to ((eq T (THead (Bind 
Abbr) u5 w) t6) \to ((pr0 t9 u5) \to ((pr0 t7 t8) \to ((subst0 O u5 t8 w) \to 
(ex2 T (\lambda (t10: T).(pr0 (THead (Bind Abbr) u2 (THead (Flat Appl) (lift 
(S O) O v2) t4)) t10)) (\lambda (t10: T).(pr0 (THead (Flat Appl) u3 t6) 
t10))))))))) (\lambda (H37: (eq T t7 t3)).(eq_ind T t3 (\lambda (t9: T).((eq 
T (THead (Bind Abbr) u5 w) t6) \to ((pr0 u1 u5) \to ((pr0 t9 t8) \to ((subst0 
O u5 t8 w) \to (ex2 T (\lambda (t10: T).(pr0 (THead (Bind Abbr) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4)) t10)) (\lambda (t10: T).(pr0 (THead (Flat 
Appl) u3 t6) t10)))))))) (\lambda (H38: (eq T (THead (Bind Abbr) u5 w) 
t6)).(eq_ind T (THead (Bind Abbr) u5 w) (\lambda (t9: T).((pr0 u1 u5) \to 
((pr0 t3 t8) \to ((subst0 O u5 t8 w) \to (ex2 T (\lambda (t10: T).(pr0 (THead 
(Bind Abbr) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t10)) (\lambda (t10: 
T).(pr0 (THead (Flat Appl) u3 t9) t10))))))) (\lambda (H39: (pr0 u1 
u5)).(\lambda (H40: (pr0 t3 t8)).(\lambda (H41: (subst0 O u5 t8 w)).(let H42 
\def (eq_ind_r B b (\lambda (b0: B).(eq T (THead (Bind b0) u1 t3) t5)) H23 
Abbr H35) in (let H43 \def (eq_ind_r B b (\lambda (b0: B).(not (eq B b0 
Abst))) H9 Abbr H35) in (let H44 \def (eq_ind_r B b (\lambda (b0: B).(eq T 
(THead (Bind b0) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t1)) H8 Abbr 
H35) in (let H45 \def (eq_ind_r T t5 (\lambda (t9: T).(eq T (THead (Flat 
Appl) u0 t9) t)) H26 (THead (Bind Abbr) u1 t3) H42) in (let H46 \def 
(eq_ind_r T t (\lambda (t9: T).(\forall (v: T).((tlt v t9) \to (\forall (t10: 
T).((pr0 v t10) \to (\forall (t11: T).((pr0 v t11) \to (ex2 T (\lambda (t12: 
T).(pr0 t10 t12)) (\lambda (t12: T).(pr0 t11 t12)))))))))) H (THead (Flat 
Appl) u0 (THead (Bind Abbr) u1 t3)) H45) in (let H47 \def (eq_ind T v1 
(\lambda (t9: T).(pr0 t9 v2)) H10 u0 H24) in (ex2_ind T (\lambda (t9: T).(pr0 
v2 t9)) (\lambda (t9: T).(pr0 u3 t9)) (ex2 T (\lambda (t9: T).(pr0 (THead 
(Bind Abbr) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t9)) (\lambda (t9: 
T).(pr0 (THead (Flat Appl) u3 (THead (Bind Abbr) u5 w)) t9))) (\lambda (x: 
T).(\lambda (H48: (pr0 v2 x)).(\lambda (H49: (pr0 u3 x)).(ex2_ind T (\lambda 
(t9: T).(pr0 t8 t9)) (\lambda (t9: T).(pr0 t4 t9)) (ex2 T (\lambda (t9: 
T).(pr0 (THead (Bind Abbr) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t9)) 
(\lambda (t9: T).(pr0 (THead (Flat Appl) u3 (THead (Bind Abbr) u5 w)) t9))) 
(\lambda (x0: T).(\lambda (H50: (pr0 t8 x0)).(\lambda (H51: (pr0 t4 
x0)).(ex2_ind T (\lambda (t9: T).(pr0 u5 t9)) (\lambda (t9: T).(pr0 u2 t9)) 
(ex2 T (\lambda (t9: T).(pr0 (THead (Bind Abbr) u2 (THead (Flat Appl) (lift 
(S O) O v2) t4)) t9)) (\lambda (t9: T).(pr0 (THead (Flat Appl) u3 (THead 
(Bind Abbr) u5 w)) t9))) (\lambda (x1: T).(\lambda (H52: (pr0 u5 
x1)).(\lambda (H53: (pr0 u2 x1)).(ex2_sym T (pr0 (THead (Flat Appl) u3 (THead 
(Bind Abbr) u5 w))) (pr0 (THead (Bind Abbr) u2 (THead (Flat Appl) (lift (S O) 
O v2) t4))) (pr0_confluence__pr0_cong_upsilon_delta H43 u5 t8 w H41 u3 v2 x 
H49 H48 t4 x0 H50 H51 u2 x1 H52 H53))))) (H46 u1 (tlt_trans (THead (Bind 
Abbr) u1 t3) u1 (THead (Flat Appl) u0 (THead (Bind Abbr) u1 t3)) (tlt_head_sx 
(Bind Abbr) u1 t3) (tlt_head_dx (Flat Appl) u0 (THead (Bind Abbr) u1 t3))) u5 
H39 u2 H11))))) (H46 t3 (tlt_trans (THead (Bind Abbr) u1 t3) t3 (THead (Flat 
Appl) u0 (THead (Bind Abbr) u1 t3)) (tlt_head_dx (Bind Abbr) u1 t3) 
(tlt_head_dx (Flat Appl) u0 (THead (Bind Abbr) u1 t3))) t8 H40 t4 H12))))) 
(H46 u0 (tlt_head_sx (Flat Appl) u0 (THead (Bind Abbr) u1 t3)) v2 H47 u3 
H18))))))))))) t6 H38)) t7 (sym_eq T t7 t3 H37))) u4 (sym_eq T u4 u1 H36))) b 
H35)) H34)) H33)) H32 H28 H29 H30))) | (pr0_zeta b0 H28 t7 t8 H29 u) 
\Rightarrow (\lambda (H30: (eq T (THead (Bind b0) u (lift (S O) O t7)) (THead 
(Bind b) u1 t3))).(\lambda (H31: (eq T t8 t6)).((let H32 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow ((let rec lref_map (f: ((nat \to nat))) (d: nat) (t9: T) on t9: T 
\def (match t9 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow 
(TLRef (match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) 
| (THead k0 u4 t10) \Rightarrow (THead k0 (lref_map f d u4) (lref_map f (s k0 
d) t10))]) in lref_map) (\lambda (x: nat).(plus x (S O))) O t7) | (TLRef _) 
\Rightarrow ((let rec lref_map (f: ((nat \to nat))) (d: nat) (t9: T) on t9: T 
\def (match t9 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow 
(TLRef (match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) 
| (THead k0 u4 t10) \Rightarrow (THead k0 (lref_map f d u4) (lref_map f (s k0 
d) t10))]) in lref_map) (\lambda (x: nat).(plus x (S O))) O t7) | (THead _ _ 
t9) \Rightarrow t9])) (THead (Bind b0) u (lift (S O) O t7)) (THead (Bind b) 
u1 t3) H30) in ((let H33 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow u | (TLRef _) 
\Rightarrow u | (THead _ t9 _) \Rightarrow t9])) (THead (Bind b0) u (lift (S 
O) O t7)) (THead (Bind b) u1 t3) H30) in ((let H34 \def (f_equal T B (\lambda 
(e: T).(match e in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow b0 
| (TLRef _) \Rightarrow b0 | (THead k0 _ _) \Rightarrow (match k0 in K return 
(\lambda (_: K).B) with [(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow 
b0])])) (THead (Bind b0) u (lift (S O) O t7)) (THead (Bind b) u1 t3) H30) in 
(eq_ind B b (\lambda (b1: B).((eq T u u1) \to ((eq T (lift (S O) O t7) t3) 
\to ((eq T t8 t6) \to ((not (eq B b1 Abst)) \to ((pr0 t7 t8) \to (ex2 T 
(\lambda (t9: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) 
t4)) t9)) (\lambda (t9: T).(pr0 (THead (Flat Appl) u3 t6) t9))))))))) 
(\lambda (H35: (eq T u u1)).(eq_ind T u1 (\lambda (_: T).((eq T (lift (S O) O 
t7) t3) \to ((eq T t8 t6) \to ((not (eq B b Abst)) \to ((pr0 t7 t8) \to (ex2 
T (\lambda (t10: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O 
v2) t4)) t10)) (\lambda (t10: T).(pr0 (THead (Flat Appl) u3 t6) t10)))))))) 
(\lambda (H36: (eq T (lift (S O) O t7) t3)).(eq_ind T (lift (S O) O t7) 
(\lambda (_: T).((eq T t8 t6) \to ((not (eq B b Abst)) \to ((pr0 t7 t8) \to 
(ex2 T (\lambda (t10: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) t10)) (\lambda (t10: T).(pr0 (THead (Flat Appl) u3 t6) 
t10))))))) (\lambda (H37: (eq T t8 t6)).(eq_ind T t6 (\lambda (t9: T).((not 
(eq B b Abst)) \to ((pr0 t7 t9) \to (ex2 T (\lambda (t10: T).(pr0 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t10)) (\lambda (t10: 
T).(pr0 (THead (Flat Appl) u3 t6) t10)))))) (\lambda (H38: (not (eq B b 
Abst))).(\lambda (H39: (pr0 t7 t6)).(let H40 \def (eq_ind_r T t3 (\lambda 
(t9: T).(eq T (THead (Bind b) u1 t9) t5)) H23 (lift (S O) O t7) H36) in (let 
H41 \def (eq_ind_r T t5 (\lambda (t9: T).(eq T (THead (Flat Appl) u0 t9) t)) 
H26 (THead (Bind b) u1 (lift (S O) O t7)) H40) in (let H42 \def (eq_ind_r T t 
(\lambda (t9: T).(\forall (v: T).((tlt v t9) \to (\forall (t10: T).((pr0 v 
t10) \to (\forall (t11: T).((pr0 v t11) \to (ex2 T (\lambda (t12: T).(pr0 t10 
t12)) (\lambda (t12: T).(pr0 t11 t12)))))))))) H (THead (Flat Appl) u0 (THead 
(Bind b) u1 (lift (S O) O t7))) H41) in (let H43 \def (eq_ind_r T t3 (\lambda 
(t9: T).(pr0 t9 t4)) H12 (lift (S O) O t7) H36) in (ex2_ind T (\lambda (t9: 
T).(eq T t4 (lift (S O) O t9))) (\lambda (t9: T).(pr0 t7 t9)) (ex2 T (\lambda 
(t9: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
t9)) (\lambda (t9: T).(pr0 (THead (Flat Appl) u3 t6) t9))) (\lambda (x: 
T).(\lambda (H44: (eq T t4 (lift (S O) O x))).(\lambda (H45: (pr0 t7 
x)).(eq_ind_r T (lift (S O) O x) (\lambda (t9: T).(ex2 T (\lambda (t10: 
T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t9)) t10)) 
(\lambda (t10: T).(pr0 (THead (Flat Appl) u3 t6) t10)))) (let H46 \def 
(eq_ind T v1 (\lambda (t9: T).(pr0 t9 v2)) H10 u0 H24) in (ex2_ind T (\lambda 
(t9: T).(pr0 v2 t9)) (\lambda (t9: T).(pr0 u3 t9)) (ex2 T (\lambda (t9: 
T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) (lift (S O) O 
x))) t9)) (\lambda (t9: T).(pr0 (THead (Flat Appl) u3 t6) t9))) (\lambda (x0: 
T).(\lambda (H47: (pr0 v2 x0)).(\lambda (H48: (pr0 u3 x0)).(ex2_ind T 
(\lambda (t9: T).(pr0 x t9)) (\lambda (t9: T).(pr0 t6 t9)) (ex2 T (\lambda 
(t9: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) (lift (S 
O) O x))) t9)) (\lambda (t9: T).(pr0 (THead (Flat Appl) u3 t6) t9))) (\lambda 
(x1: T).(\lambda (H49: (pr0 x x1)).(\lambda (H50: (pr0 t6 x1)).(ex2_sym T 
(pr0 (THead (Flat Appl) u3 t6)) (pr0 (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) (lift (S O) O x)))) (pr0_confluence__pr0_cong_upsilon_zeta 
b H38 u1 u2 H11 u3 v2 x0 H48 H47 x t6 x1 H49 H50))))) (H42 t7 (tlt_trans 
(THead (Bind b) u1 (lift (S O) O t7)) t7 (THead (Flat Appl) u0 (THead (Bind 
b) u1 (lift (S O) O t7))) (lift_tlt_dx (Bind b) u1 t7 (S O) O) (tlt_head_dx 
(Flat Appl) u0 (THead (Bind b) u1 (lift (S O) O t7)))) x H45 t6 H39))))) (H42 
u0 (tlt_head_sx (Flat Appl) u0 (THead (Bind b) u1 (lift (S O) O t7))) v2 H46 
u3 H18))) t4 H44)))) (pr0_gen_lift t7 t4 (S O) O H43)))))))) t8 (sym_eq T t8 
t6 H37))) t3 H36)) u (sym_eq T u u1 H35))) b0 (sym_eq B b0 b H34))) H33)) 
H32)) H31 H28 H29))) | (pr0_tau t7 t8 H28 u) \Rightarrow (\lambda (H29: (eq T 
(THead (Flat Cast) u t7) (THead (Bind b) u1 t3))).(\lambda (H30: (eq T t8 
t6)).((let H31 \def (eq_ind T (THead (Flat Cast) u t7) (\lambda (e: T).(match 
e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 in K 
return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) I (THead (Bind b) u1 t3) H29) in (False_ind ((eq T t8 
t6) \to ((pr0 t7 t8) \to (ex2 T (\lambda (t9: T).(pr0 (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t4)) t9)) (\lambda (t9: T).(pr0 (THead 
(Flat Appl) u3 t6) t9))))) H31)) H30 H28)))]) in (H28 (refl_equal T (THead 
(Bind b) u1 t3)) (refl_equal T t6))))) k H25)))) H22)) H21))))) t2 H17)) t 
H15 H16 H13 H14))) | (pr0_beta u v0 v3 H13 t5 t6 H14) \Rightarrow (\lambda 
(H15: (eq T (THead (Flat Appl) v0 (THead (Bind Abst) u t5)) t)).(\lambda 
(H16: (eq T (THead (Bind Abbr) v3 t6) t2)).(eq_ind T (THead (Flat Appl) v0 
(THead (Bind Abst) u t5)) (\lambda (_: T).((eq T (THead (Bind Abbr) v3 t6) 
t2) \to ((pr0 v0 v3) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t8)) (\lambda (t8: 
T).(pr0 t2 t8))))))) (\lambda (H17: (eq T (THead (Bind Abbr) v3 t6) 
t2)).(eq_ind T (THead (Bind Abbr) v3 t6) (\lambda (t7: T).((pr0 v0 v3) \to 
((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) t8)) (\lambda (t8: T).(pr0 t7 t8)))))) (\lambda 
(_: (pr0 v0 v3)).(\lambda (_: (pr0 t5 t6)).(let H20 \def (eq_ind_r T t 
(\lambda (t7: T).(eq T (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) t7)) H6 
(THead (Flat Appl) v0 (THead (Bind Abst) u t5)) H15) in (let H21 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow v1 | (TLRef _) \Rightarrow v1 | (THead _ t7 _) 
\Rightarrow t7])) (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) (THead (Flat 
Appl) v0 (THead (Bind Abst) u t5)) H20) in ((let H22 \def (f_equal T B 
(\lambda (e: T).(match e in T return (\lambda (_: T).B) with [(TSort _) 
\Rightarrow b | (TLRef _) \Rightarrow b | (THead _ _ t7) \Rightarrow (match 
t7 in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow b | (TLRef _) 
\Rightarrow b | (THead k _ _) \Rightarrow (match k in K return (\lambda (_: 
K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow b])])])) (THead 
(Flat Appl) v1 (THead (Bind b) u1 t3)) (THead (Flat Appl) v0 (THead (Bind 
Abst) u t5)) H20) in ((let H23 \def (f_equal T T (\lambda (e: T).(match e in 
T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u1 | (TLRef _) 
\Rightarrow u1 | (THead _ _ t7) \Rightarrow (match t7 in T return (\lambda 
(_: T).T) with [(TSort _) \Rightarrow u1 | (TLRef _) \Rightarrow u1 | (THead 
_ t8 _) \Rightarrow t8])])) (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) 
(THead (Flat Appl) v0 (THead (Bind Abst) u t5)) H20) in ((let H24 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead _ _ t7) 
\Rightarrow (match t7 in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead _ _ t8) \Rightarrow 
t8])])) (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) (THead (Flat Appl) v0 
(THead (Bind Abst) u t5)) H20) in (\lambda (_: (eq T u1 u)).(\lambda (H26: 
(eq B b Abst)).(\lambda (H27: (eq T v1 v0)).(let H28 \def (eq_ind_r T t 
(\lambda (t7: T).(\forall (v: T).((tlt v t7) \to (\forall (t8: T).((pr0 v t8) 
\to (\forall (t9: T).((pr0 v t9) \to (ex2 T (\lambda (t10: T).(pr0 t8 t10)) 
(\lambda (t10: T).(pr0 t9 t10)))))))))) H (THead (Flat Appl) v0 (THead (Bind 
Abst) u t5)) H15) in (let H29 \def (eq_ind T v1 (\lambda (t7: T).(pr0 t7 v2)) 
H10 v0 H27) in (eq_ind_r B Abst (\lambda (b0: B).(ex2 T (\lambda (t7: T).(pr0 
(THead (Bind b0) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t7)) (\lambda 
(t7: T).(pr0 (THead (Bind Abbr) v3 t6) t7)))) (let H30 \def (eq_ind B b 
(\lambda (b0: B).(not (eq B b0 Abst))) H9 Abst H26) in (let H31 \def (match 
(H30 (refl_equal B Abst)) in False return (\lambda (_: False).(ex2 T (\lambda 
(t7: T).(pr0 (THead (Bind Abst) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
t7)) (\lambda (t7: T).(pr0 (THead (Bind Abbr) v3 t6) t7)))) with []) in H31)) 
b H26))))))) H23)) H22)) H21))))) t2 H17)) t H15 H16 H13 H14))) | 
(pr0_upsilon b0 H13 v0 v3 H14 u0 u3 H15 t5 t6 H16) \Rightarrow (\lambda (H17: 
(eq T (THead (Flat Appl) v0 (THead (Bind b0) u0 t5)) t)).(\lambda (H18: (eq T 
(THead (Bind b0) u3 (THead (Flat Appl) (lift (S O) O v3) t6)) t2)).(eq_ind T 
(THead (Flat Appl) v0 (THead (Bind b0) u0 t5)) (\lambda (_: T).((eq T (THead 
(Bind b0) u3 (THead (Flat Appl) (lift (S O) O v3) t6)) t2) \to ((not (eq B b0 
Abst)) \to ((pr0 v0 v3) \to ((pr0 u0 u3) \to ((pr0 t5 t6) \to (ex2 T (\lambda 
(t8: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
t8)) (\lambda (t8: T).(pr0 t2 t8))))))))) (\lambda (H19: (eq T (THead (Bind 
b0) u3 (THead (Flat Appl) (lift (S O) O v3) t6)) t2)).(eq_ind T (THead (Bind 
b0) u3 (THead (Flat Appl) (lift (S O) O v3) t6)) (\lambda (t7: T).((not (eq B 
b0 Abst)) \to ((pr0 v0 v3) \to ((pr0 u0 u3) \to ((pr0 t5 t6) \to (ex2 T 
(\lambda (t8: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) 
t4)) t8)) (\lambda (t8: T).(pr0 t7 t8)))))))) (\lambda (_: (not (eq B b0 
Abst))).(\lambda (H21: (pr0 v0 v3)).(\lambda (H22: (pr0 u0 u3)).(\lambda 
(H23: (pr0 t5 t6)).(let H24 \def (eq_ind_r T t (\lambda (t7: T).(eq T (THead 
(Flat Appl) v1 (THead (Bind b) u1 t3)) t7)) H6 (THead (Flat Appl) v0 (THead 
(Bind b0) u0 t5)) H17) in (let H25 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow v1 | (TLRef _) 
\Rightarrow v1 | (THead _ t7 _) \Rightarrow t7])) (THead (Flat Appl) v1 
(THead (Bind b) u1 t3)) (THead (Flat Appl) v0 (THead (Bind b0) u0 t5)) H24) 
in ((let H26 \def (f_equal T B (\lambda (e: T).(match e in T return (\lambda 
(_: T).B) with [(TSort _) \Rightarrow b | (TLRef _) \Rightarrow b | (THead _ 
_ t7) \Rightarrow (match t7 in T return (\lambda (_: T).B) with [(TSort _) 
\Rightarrow b | (TLRef _) \Rightarrow b | (THead k _ _) \Rightarrow (match k 
in K return (\lambda (_: K).B) with [(Bind b1) \Rightarrow b1 | (Flat _) 
\Rightarrow b])])])) (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) (THead 
(Flat Appl) v0 (THead (Bind b0) u0 t5)) H24) in ((let H27 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u1 | (TLRef _) \Rightarrow u1 | (THead _ _ t7) \Rightarrow (match 
t7 in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u1 | (TLRef _) 
\Rightarrow u1 | (THead _ t8 _) \Rightarrow t8])])) (THead (Flat Appl) v1 
(THead (Bind b) u1 t3)) (THead (Flat Appl) v0 (THead (Bind b0) u0 t5)) H24) 
in ((let H28 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda 
(_: T).T) with [(TSort _) \Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead 
_ _ t7) \Rightarrow (match t7 in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead _ _ t8) \Rightarrow 
t8])])) (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) (THead (Flat Appl) v0 
(THead (Bind b0) u0 t5)) H24) in (\lambda (H29: (eq T u1 u0)).(\lambda (H30: 
(eq B b b0)).(\lambda (H31: (eq T v1 v0)).(let H32 \def (eq_ind_r T t 
(\lambda (t7: T).(\forall (v: T).((tlt v t7) \to (\forall (t8: T).((pr0 v t8) 
\to (\forall (t9: T).((pr0 v t9) \to (ex2 T (\lambda (t10: T).(pr0 t8 t10)) 
(\lambda (t10: T).(pr0 t9 t10)))))))))) H (THead (Flat Appl) v0 (THead (Bind 
b0) u0 t5)) H17) in (let H33 \def (eq_ind T v1 (\lambda (t7: T).(pr0 t7 v2)) 
H10 v0 H31) in (eq_ind_r B b0 (\lambda (b1: B).(ex2 T (\lambda (t7: T).(pr0 
(THead (Bind b1) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t7)) (\lambda 
(t7: T).(pr0 (THead (Bind b0) u3 (THead (Flat Appl) (lift (S O) O v3) t6)) 
t7)))) (let H34 \def (eq_ind B b (\lambda (b1: B).(not (eq B b1 Abst))) H9 b0 
H30) in (let H35 \def (eq_ind T u1 (\lambda (t7: T).(pr0 t7 u2)) H11 u0 H29) 
in (let H36 \def (eq_ind T t3 (\lambda (t7: T).(pr0 t7 t4)) H12 t5 H28) in 
(ex2_ind T (\lambda (t7: T).(pr0 t4 t7)) (\lambda (t7: T).(pr0 t6 t7)) (ex2 T 
(\lambda (t7: T).(pr0 (THead (Bind b0) u2 (THead (Flat Appl) (lift (S O) O 
v2) t4)) t7)) (\lambda (t7: T).(pr0 (THead (Bind b0) u3 (THead (Flat Appl) 
(lift (S O) O v3) t6)) t7))) (\lambda (x: T).(\lambda (H37: (pr0 t4 
x)).(\lambda (H38: (pr0 t6 x)).(ex2_ind T (\lambda (t7: T).(pr0 u2 t7)) 
(\lambda (t7: T).(pr0 u3 t7)) (ex2 T (\lambda (t7: T).(pr0 (THead (Bind b0) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t7)) (\lambda (t7: T).(pr0 
(THead (Bind b0) u3 (THead (Flat Appl) (lift (S O) O v3) t6)) t7))) (\lambda 
(x0: T).(\lambda (H39: (pr0 u2 x0)).(\lambda (H40: (pr0 u3 x0)).(ex2_ind T 
(\lambda (t7: T).(pr0 v2 t7)) (\lambda (t7: T).(pr0 v3 t7)) (ex2 T (\lambda 
(t7: T).(pr0 (THead (Bind b0) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) 
t7)) (\lambda (t7: T).(pr0 (THead (Bind b0) u3 (THead (Flat Appl) (lift (S O) 
O v3) t6)) t7))) (\lambda (x1: T).(\lambda (H41: (pr0 v2 x1)).(\lambda (H42: 
(pr0 v3 x1)).(pr0_confluence__pr0_upsilon_upsilon b0 H34 v2 v3 x1 H41 H42 u2 
u3 x0 H39 H40 t4 t6 x H37 H38)))) (H32 v0 (tlt_head_sx (Flat Appl) v0 (THead 
(Bind b0) u0 t5)) v2 H33 v3 H21))))) (H32 u0 (tlt_trans (THead (Bind b0) u0 
t5) u0 (THead (Flat Appl) v0 (THead (Bind b0) u0 t5)) (tlt_head_sx (Bind b0) 
u0 t5) (tlt_head_dx (Flat Appl) v0 (THead (Bind b0) u0 t5))) u2 H35 u3 
H22))))) (H32 t5 (tlt_trans (THead (Bind b0) u0 t5) t5 (THead (Flat Appl) v0 
(THead (Bind b0) u0 t5)) (tlt_head_dx (Bind b0) u0 t5) (tlt_head_dx (Flat 
Appl) v0 (THead (Bind b0) u0 t5))) t4 H36 t6 H23))))) b H30))))))) H27)) 
H26)) H25))))))) t2 H19)) t H17 H18 H13 H14 H15 H16))) | (pr0_delta u0 u3 H13 
t5 t6 H14 w H15) \Rightarrow (\lambda (H16: (eq T (THead (Bind Abbr) u0 t5) 
t)).(\lambda (H17: (eq T (THead (Bind Abbr) u3 w) t2)).(eq_ind T (THead (Bind 
Abbr) u0 t5) (\lambda (_: T).((eq T (THead (Bind Abbr) u3 w) t2) \to ((pr0 u0 
u3) \to ((pr0 t5 t6) \to ((subst0 O u3 t6 w) \to (ex2 T (\lambda (t8: T).(pr0 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t8)) (\lambda 
(t8: T).(pr0 t2 t8)))))))) (\lambda (H18: (eq T (THead (Bind Abbr) u3 w) 
t2)).(eq_ind T (THead (Bind Abbr) u3 w) (\lambda (t7: T).((pr0 u0 u3) \to 
((pr0 t5 t6) \to ((subst0 O u3 t6 w) \to (ex2 T (\lambda (t8: T).(pr0 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t8)) (\lambda (t8: 
T).(pr0 t7 t8))))))) (\lambda (_: (pr0 u0 u3)).(\lambda (_: (pr0 t5 
t6)).(\lambda (_: (subst0 O u3 t6 w)).(let H22 \def (eq_ind_r T t (\lambda 
(t7: T).(eq T (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) t7)) H6 (THead 
(Bind Abbr) u0 t5) H16) in (let H23 \def (eq_ind T (THead (Flat Appl) v1 
(THead (Bind b) u1 t3)) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind 
Abbr) u0 t5) H22) in (False_ind (ex2 T (\lambda (t7: T).(pr0 (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t7)) (\lambda (t7: T).(pr0 
(THead (Bind Abbr) u3 w) t7))) H23)))))) t2 H18)) t H16 H17 H13 H14 H15))) | 
(pr0_zeta b0 H13 t5 t6 H14 u) \Rightarrow (\lambda (H15: (eq T (THead (Bind 
b0) u (lift (S O) O t5)) t)).(\lambda (H16: (eq T t6 t2)).(eq_ind T (THead 
(Bind b0) u (lift (S O) O t5)) (\lambda (_: T).((eq T t6 t2) \to ((not (eq B 
b0 Abst)) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t8)) (\lambda (t8: T).(pr0 t2 
t8))))))) (\lambda (H17: (eq T t6 t2)).(eq_ind T t2 (\lambda (t7: T).((not 
(eq B b0 Abst)) \to ((pr0 t5 t7) \to (ex2 T (\lambda (t8: T).(pr0 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t8)) (\lambda (t8: 
T).(pr0 t2 t8)))))) (\lambda (_: (not (eq B b0 Abst))).(\lambda (_: (pr0 t5 
t2)).(let H20 \def (eq_ind_r T t (\lambda (t7: T).(eq T (THead (Flat Appl) v1 
(THead (Bind b) u1 t3)) t7)) H6 (THead (Bind b0) u (lift (S O) O t5)) H15) in 
(let H21 \def (eq_ind T (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | 
(Flat _) \Rightarrow True])])) I (THead (Bind b0) u (lift (S O) O t5)) H20) 
in (False_ind (ex2 T (\lambda (t7: T).(pr0 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) t7)) (\lambda (t7: T).(pr0 t2 t7))) H21))))) t6 
(sym_eq T t6 t2 H17))) t H15 H16 H13 H14))) | (pr0_tau t5 t6 H13 u) 
\Rightarrow (\lambda (H14: (eq T (THead (Flat Cast) u t5) t)).(\lambda (H15: 
(eq T t6 t2)).(eq_ind T (THead (Flat Cast) u t5) (\lambda (_: T).((eq T t6 
t2) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t4)) t8)) (\lambda (t8: T).(pr0 t2 
t8)))))) (\lambda (H16: (eq T t6 t2)).(eq_ind T t2 (\lambda (t7: T).((pr0 t5 
t7) \to (ex2 T (\lambda (t8: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4)) t8)) (\lambda (t8: T).(pr0 t2 t8))))) (\lambda (_: 
(pr0 t5 t2)).(let H18 \def (eq_ind_r T t (\lambda (t7: T).(eq T (THead (Flat 
Appl) v1 (THead (Bind b) u1 t3)) t7)) H6 (THead (Flat Cast) u t5) H14) in 
(let H19 \def (eq_ind T (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | 
(Flat f) \Rightarrow (match f in F return (\lambda (_: F).Prop) with [Appl 
\Rightarrow True | Cast \Rightarrow False])])])) I (THead (Flat Cast) u t5) 
H18) in (False_ind (ex2 T (\lambda (t7: T).(pr0 (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4)) t7)) (\lambda (t7: T).(pr0 t2 t7))) 
H19)))) t6 (sym_eq T t6 t2 H16))) t H14 H15 H13)))]) in (H13 (refl_equal T t) 
(refl_equal T t2))))))) t1 H8)) t H6 H7 H2 H3 H4 H5))) | (pr0_delta u1 u2 H2 
t3 t4 H3 w H4) \Rightarrow (\lambda (H5: (eq T (THead (Bind Abbr) u1 t3) 
t)).(\lambda (H6: (eq T (THead (Bind Abbr) u2 w) t1)).(eq_ind T (THead (Bind 
Abbr) u1 t3) (\lambda (_: T).((eq T (THead (Bind Abbr) u2 w) t1) \to ((pr0 u1 
u2) \to ((pr0 t3 t4) \to ((subst0 O u2 t4 w) \to (ex2 T (\lambda (t6: T).(pr0 
t1 t6)) (\lambda (t6: T).(pr0 t2 t6)))))))) (\lambda (H7: (eq T (THead (Bind 
Abbr) u2 w) t1)).(eq_ind T (THead (Bind Abbr) u2 w) (\lambda (t5: T).((pr0 u1 
u2) \to ((pr0 t3 t4) \to ((subst0 O u2 t4 w) \to (ex2 T (\lambda (t6: T).(pr0 
t5 t6)) (\lambda (t6: T).(pr0 t2 t6))))))) (\lambda (H8: (pr0 u1 
u2)).(\lambda (H9: (pr0 t3 t4)).(\lambda (H10: (subst0 O u2 t4 w)).(let H11 
\def (match H1 in pr0 return (\lambda (t5: T).(\lambda (t6: T).(\lambda (_: 
(pr0 t5 t6)).((eq T t5 t) \to ((eq T t6 t2) \to (ex2 T (\lambda (t7: T).(pr0 
(THead (Bind Abbr) u2 w) t7)) (\lambda (t7: T).(pr0 t2 t7)))))))) with 
[(pr0_refl t5) \Rightarrow (\lambda (H11: (eq T t5 t)).(\lambda (H12: (eq T 
t5 t2)).(eq_ind T t (\lambda (t6: T).((eq T t6 t2) \to (ex2 T (\lambda (t7: 
T).(pr0 (THead (Bind Abbr) u2 w) t7)) (\lambda (t7: T).(pr0 t2 t7))))) 
(\lambda (H13: (eq T t t2)).(eq_ind T t2 (\lambda (_: T).(ex2 T (\lambda (t7: 
T).(pr0 (THead (Bind Abbr) u2 w) t7)) (\lambda (t7: T).(pr0 t2 t7)))) (let 
H14 \def (eq_ind_r T t (\lambda (t6: T).(eq T t6 t2)) H13 (THead (Bind Abbr) 
u1 t3) H5) in (eq_ind T (THead (Bind Abbr) u1 t3) (\lambda (t6: T).(ex2 T 
(\lambda (t7: T).(pr0 (THead (Bind Abbr) u2 w) t7)) (\lambda (t7: T).(pr0 t6 
t7)))) (let H15 \def (eq_ind_r T t (\lambda (t6: T).(eq T t5 t6)) H11 (THead 
(Bind Abbr) u1 t3) H5) in (let H16 \def (eq_ind_r T t (\lambda (t6: 
T).(\forall (v: T).((tlt v t6) \to (\forall (t7: T).((pr0 v t7) \to (\forall 
(t8: T).((pr0 v t8) \to (ex2 T (\lambda (t9: T).(pr0 t7 t9)) (\lambda (t9: 
T).(pr0 t8 t9)))))))))) H (THead (Bind Abbr) u1 t3) H5) in (ex_intro2 T 
(\lambda (t6: T).(pr0 (THead (Bind Abbr) u2 w) t6)) (\lambda (t6: T).(pr0 
(THead (Bind Abbr) u1 t3) t6)) (THead (Bind Abbr) u2 w) (pr0_refl (THead 
(Bind Abbr) u2 w)) (pr0_delta u1 u2 H8 t3 t4 H9 w H10)))) t2 H14)) t (sym_eq 
T t t2 H13))) t5 (sym_eq T t5 t H11) H12))) | (pr0_comp u0 u3 H11 t5 t6 H12 
k) \Rightarrow (\lambda (H13: (eq T (THead k u0 t5) t)).(\lambda (H14: (eq T 
(THead k u3 t6) t2)).(eq_ind T (THead k u0 t5) (\lambda (_: T).((eq T (THead 
k u3 t6) t2) \to ((pr0 u0 u3) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: 
T).(pr0 (THead (Bind Abbr) u2 w) t8)) (\lambda (t8: T).(pr0 t2 t8))))))) 
(\lambda (H15: (eq T (THead k u3 t6) t2)).(eq_ind T (THead k u3 t6) (\lambda 
(t7: T).((pr0 u0 u3) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead 
(Bind Abbr) u2 w) t8)) (\lambda (t8: T).(pr0 t7 t8)))))) (\lambda (H16: (pr0 
u0 u3)).(\lambda (H17: (pr0 t5 t6)).(let H18 \def (eq_ind_r T t (\lambda (t7: 
T).(eq T (THead (Bind Abbr) u1 t3) t7)) H5 (THead k u0 t5) H13) in (let H19 
\def (f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) 
with [(TSort _) \Rightarrow (Bind Abbr) | (TLRef _) \Rightarrow (Bind Abbr) | 
(THead k0 _ _) \Rightarrow k0])) (THead (Bind Abbr) u1 t3) (THead k u0 t5) 
H18) in ((let H20 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow u1 | (TLRef _) \Rightarrow u1 
| (THead _ t7 _) \Rightarrow t7])) (THead (Bind Abbr) u1 t3) (THead k u0 t5) 
H18) in ((let H21 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow t3 | (TLRef _) \Rightarrow t3 
| (THead _ _ t7) \Rightarrow t7])) (THead (Bind Abbr) u1 t3) (THead k u0 t5) 
H18) in (\lambda (H22: (eq T u1 u0)).(\lambda (H23: (eq K (Bind Abbr) 
k)).(eq_ind K (Bind Abbr) (\lambda (k0: K).(ex2 T (\lambda (t7: T).(pr0 
(THead (Bind Abbr) u2 w) t7)) (\lambda (t7: T).(pr0 (THead k0 u3 t6) t7)))) 
(let H24 \def (eq_ind_r K k (\lambda (k0: K).(eq T (THead k0 u0 t5) t)) H13 
(Bind Abbr) H23) in (let H25 \def (eq_ind_r T t (\lambda (t7: T).(\forall (v: 
T).((tlt v t7) \to (\forall (t8: T).((pr0 v t8) \to (\forall (t9: T).((pr0 v 
t9) \to (ex2 T (\lambda (t10: T).(pr0 t8 t10)) (\lambda (t10: T).(pr0 t9 
t10)))))))))) H (THead (Bind Abbr) u0 t5) H24) in (let H26 \def (eq_ind T u1 
(\lambda (t7: T).(pr0 t7 u2)) H8 u0 H22) in (let H27 \def (eq_ind T t3 
(\lambda (t7: T).(pr0 t7 t4)) H9 t5 H21) in (ex2_ind T (\lambda (t7: T).(pr0 
t4 t7)) (\lambda (t7: T).(pr0 t6 t7)) (ex2 T (\lambda (t7: T).(pr0 (THead 
(Bind Abbr) u2 w) t7)) (\lambda (t7: T).(pr0 (THead (Bind Abbr) u3 t6) t7))) 
(\lambda (x: T).(\lambda (H28: (pr0 t4 x)).(\lambda (H29: (pr0 t6 
x)).(ex2_ind T (\lambda (t7: T).(pr0 u2 t7)) (\lambda (t7: T).(pr0 u3 t7)) 
(ex2 T (\lambda (t7: T).(pr0 (THead (Bind Abbr) u2 w) t7)) (\lambda (t7: 
T).(pr0 (THead (Bind Abbr) u3 t6) t7))) (\lambda (x0: T).(\lambda (H30: (pr0 
u2 x0)).(\lambda (H31: (pr0 u3 x0)).(ex2_sym T (pr0 (THead (Bind Abbr) u3 
t6)) (pr0 (THead (Bind Abbr) u2 w)) (pr0_confluence__pr0_cong_delta u2 t4 w 
H10 u3 x0 H31 H30 t6 x H29 H28))))) (H25 u0 (tlt_head_sx (Bind Abbr) u0 t5) 
u2 H26 u3 H16))))) (H25 t5 (tlt_head_dx (Bind Abbr) u0 t5) t4 H27 t6 
H17)))))) k H23)))) H20)) H19))))) t2 H15)) t H13 H14 H11 H12))) | (pr0_beta 
u v1 v2 H11 t5 t6 H12) \Rightarrow (\lambda (H13: (eq T (THead (Flat Appl) v1 
(THead (Bind Abst) u t5)) t)).(\lambda (H14: (eq T (THead (Bind Abbr) v2 t6) 
t2)).(eq_ind T (THead (Flat Appl) v1 (THead (Bind Abst) u t5)) (\lambda (_: 
T).((eq T (THead (Bind Abbr) v2 t6) t2) \to ((pr0 v1 v2) \to ((pr0 t5 t6) \to 
(ex2 T (\lambda (t8: T).(pr0 (THead (Bind Abbr) u2 w) t8)) (\lambda (t8: 
T).(pr0 t2 t8))))))) (\lambda (H15: (eq T (THead (Bind Abbr) v2 t6) 
t2)).(eq_ind T (THead (Bind Abbr) v2 t6) (\lambda (t7: T).((pr0 v1 v2) \to 
((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead (Bind Abbr) u2 w) t8)) 
(\lambda (t8: T).(pr0 t7 t8)))))) (\lambda (_: (pr0 v1 v2)).(\lambda (_: (pr0 
t5 t6)).(let H18 \def (eq_ind_r T t (\lambda (t7: T).(eq T (THead (Bind Abbr) 
u1 t3) t7)) H5 (THead (Flat Appl) v1 (THead (Bind Abst) u t5)) H13) in (let 
H19 \def (eq_ind T (THead (Bind Abbr) u1 t3) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow 
False])])) I (THead (Flat Appl) v1 (THead (Bind Abst) u t5)) H18) in 
(False_ind (ex2 T (\lambda (t7: T).(pr0 (THead (Bind Abbr) u2 w) t7)) 
(\lambda (t7: T).(pr0 (THead (Bind Abbr) v2 t6) t7))) H19))))) t2 H15)) t H13 
H14 H11 H12))) | (pr0_upsilon b H11 v1 v2 H12 u0 u3 H13 t5 t6 H14) 
\Rightarrow (\lambda (H15: (eq T (THead (Flat Appl) v1 (THead (Bind b) u0 
t5)) t)).(\lambda (H16: (eq T (THead (Bind b) u3 (THead (Flat Appl) (lift (S 
O) O v2) t6)) t2)).(eq_ind T (THead (Flat Appl) v1 (THead (Bind b) u0 t5)) 
(\lambda (_: T).((eq T (THead (Bind b) u3 (THead (Flat Appl) (lift (S O) O 
v2) t6)) t2) \to ((not (eq B b Abst)) \to ((pr0 v1 v2) \to ((pr0 u0 u3) \to 
((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead (Bind Abbr) u2 w) t8)) 
(\lambda (t8: T).(pr0 t2 t8))))))))) (\lambda (H17: (eq T (THead (Bind b) u3 
(THead (Flat Appl) (lift (S O) O v2) t6)) t2)).(eq_ind T (THead (Bind b) u3 
(THead (Flat Appl) (lift (S O) O v2) t6)) (\lambda (t7: T).((not (eq B b 
Abst)) \to ((pr0 v1 v2) \to ((pr0 u0 u3) \to ((pr0 t5 t6) \to (ex2 T (\lambda 
(t8: T).(pr0 (THead (Bind Abbr) u2 w) t8)) (\lambda (t8: T).(pr0 t7 
t8)))))))) (\lambda (_: (not (eq B b Abst))).(\lambda (_: (pr0 v1 
v2)).(\lambda (_: (pr0 u0 u3)).(\lambda (_: (pr0 t5 t6)).(let H22 \def 
(eq_ind_r T t (\lambda (t7: T).(eq T (THead (Bind Abbr) u1 t3) t7)) H5 (THead 
(Flat Appl) v1 (THead (Bind b) u0 t5)) H15) in (let H23 \def (eq_ind T (THead 
(Bind Abbr) u1 t3) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat 
Appl) v1 (THead (Bind b) u0 t5)) H22) in (False_ind (ex2 T (\lambda (t7: 
T).(pr0 (THead (Bind Abbr) u2 w) t7)) (\lambda (t7: T).(pr0 (THead (Bind b) 
u3 (THead (Flat Appl) (lift (S O) O v2) t6)) t7))) H23))))))) t2 H17)) t H15 
H16 H11 H12 H13 H14))) | (pr0_delta u0 u3 H11 t5 t6 H12 w0 H13) \Rightarrow 
(\lambda (H14: (eq T (THead (Bind Abbr) u0 t5) t)).(\lambda (H15: (eq T 
(THead (Bind Abbr) u3 w0) t2)).(eq_ind T (THead (Bind Abbr) u0 t5) (\lambda 
(_: T).((eq T (THead (Bind Abbr) u3 w0) t2) \to ((pr0 u0 u3) \to ((pr0 t5 t6) 
\to ((subst0 O u3 t6 w0) \to (ex2 T (\lambda (t8: T).(pr0 (THead (Bind Abbr) 
u2 w) t8)) (\lambda (t8: T).(pr0 t2 t8)))))))) (\lambda (H16: (eq T (THead 
(Bind Abbr) u3 w0) t2)).(eq_ind T (THead (Bind Abbr) u3 w0) (\lambda (t7: 
T).((pr0 u0 u3) \to ((pr0 t5 t6) \to ((subst0 O u3 t6 w0) \to (ex2 T (\lambda 
(t8: T).(pr0 (THead (Bind Abbr) u2 w) t8)) (\lambda (t8: T).(pr0 t7 t8))))))) 
(\lambda (H17: (pr0 u0 u3)).(\lambda (H18: (pr0 t5 t6)).(\lambda (H19: 
(subst0 O u3 t6 w0)).(let H20 \def (eq_ind_r T t (\lambda (t7: T).(eq T 
(THead (Bind Abbr) u1 t3) t7)) H5 (THead (Bind Abbr) u0 t5) H14) in (let H21 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow u1 | (TLRef _) \Rightarrow u1 | (THead _ t7 _) 
\Rightarrow t7])) (THead (Bind Abbr) u1 t3) (THead (Bind Abbr) u0 t5) H20) in 
((let H22 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead _ _ 
t7) \Rightarrow t7])) (THead (Bind Abbr) u1 t3) (THead (Bind Abbr) u0 t5) 
H20) in (\lambda (H23: (eq T u1 u0)).(let H24 \def (eq_ind_r T t (\lambda 
(t7: T).(\forall (v: T).((tlt v t7) \to (\forall (t8: T).((pr0 v t8) \to 
(\forall (t9: T).((pr0 v t9) \to (ex2 T (\lambda (t10: T).(pr0 t8 t10)) 
(\lambda (t10: T).(pr0 t9 t10)))))))))) H (THead (Bind Abbr) u0 t5) H14) in 
(let H25 \def (eq_ind T u1 (\lambda (t7: T).(pr0 t7 u2)) H8 u0 H23) in (let 
H26 \def (eq_ind T t3 (\lambda (t7: T).(pr0 t7 t4)) H9 t5 H22) in (ex2_ind T 
(\lambda (t7: T).(pr0 t4 t7)) (\lambda (t7: T).(pr0 t6 t7)) (ex2 T (\lambda 
(t7: T).(pr0 (THead (Bind Abbr) u2 w) t7)) (\lambda (t7: T).(pr0 (THead (Bind 
Abbr) u3 w0) t7))) (\lambda (x: T).(\lambda (H27: (pr0 t4 x)).(\lambda (H28: 
(pr0 t6 x)).(ex2_ind T (\lambda (t7: T).(pr0 u2 t7)) (\lambda (t7: T).(pr0 u3 
t7)) (ex2 T (\lambda (t7: T).(pr0 (THead (Bind Abbr) u2 w) t7)) (\lambda (t7: 
T).(pr0 (THead (Bind Abbr) u3 w0) t7))) (\lambda (x0: T).(\lambda (H29: (pr0 
u2 x0)).(\lambda (H30: (pr0 u3 x0)).(pr0_confluence__pr0_delta_delta u2 t4 w 
H10 u3 t6 w0 H19 x0 H29 H30 x H27 H28)))) (H24 u0 (tlt_head_sx (Bind Abbr) u0 
t5) u2 H25 u3 H17))))) (H24 t5 (tlt_head_dx (Bind Abbr) u0 t5) t4 H26 t6 
H18))))))) H21)))))) t2 H16)) t H14 H15 H11 H12 H13))) | (pr0_zeta b H11 t5 
t6 H12 u) \Rightarrow (\lambda (H13: (eq T (THead (Bind b) u (lift (S O) O 
t5)) t)).(\lambda (H14: (eq T t6 t2)).(eq_ind T (THead (Bind b) u (lift (S O) 
O t5)) (\lambda (_: T).((eq T t6 t2) \to ((not (eq B b Abst)) \to ((pr0 t5 
t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead (Bind Abbr) u2 w) t8)) (\lambda 
(t8: T).(pr0 t2 t8))))))) (\lambda (H15: (eq T t6 t2)).(eq_ind T t2 (\lambda 
(t7: T).((not (eq B b Abst)) \to ((pr0 t5 t7) \to (ex2 T (\lambda (t8: 
T).(pr0 (THead (Bind Abbr) u2 w) t8)) (\lambda (t8: T).(pr0 t2 t8)))))) 
(\lambda (H16: (not (eq B b Abst))).(\lambda (H17: (pr0 t5 t2)).(let H18 \def 
(eq_ind_r T t (\lambda (t7: T).(eq T (THead (Bind Abbr) u1 t3) t7)) H5 (THead 
(Bind b) u (lift (S O) O t5)) H13) in (let H19 \def (f_equal T B (\lambda (e: 
T).(match e in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow Abbr | 
(TLRef _) \Rightarrow Abbr | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow 
Abbr])])) (THead (Bind Abbr) u1 t3) (THead (Bind b) u (lift (S O) O t5)) H18) 
in ((let H20 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda 
(_: T).T) with [(TSort _) \Rightarrow u1 | (TLRef _) \Rightarrow u1 | (THead 
_ t7 _) \Rightarrow t7])) (THead (Bind Abbr) u1 t3) (THead (Bind b) u (lift 
(S O) O t5)) H18) in ((let H21 \def (f_equal T T (\lambda (e: T).(match e in 
T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t3 | (TLRef _) 
\Rightarrow t3 | (THead _ _ t7) \Rightarrow t7])) (THead (Bind Abbr) u1 t3) 
(THead (Bind b) u (lift (S O) O t5)) H18) in (\lambda (H22: (eq T u1 
u)).(\lambda (H23: (eq B Abbr b)).(let H24 \def (eq_ind_r B b (\lambda (b0: 
B).(not (eq B b0 Abst))) H16 Abbr H23) in (let H25 \def (eq_ind_r B b 
(\lambda (b0: B).(eq T (THead (Bind b0) u (lift (S O) O t5)) t)) H13 Abbr 
H23) in (let H26 \def (eq_ind_r T t (\lambda (t7: T).(\forall (v: T).((tlt v 
t7) \to (\forall (t8: T).((pr0 v t8) \to (\forall (t9: T).((pr0 v t9) \to 
(ex2 T (\lambda (t10: T).(pr0 t8 t10)) (\lambda (t10: T).(pr0 t9 
t10)))))))))) H (THead (Bind Abbr) u (lift (S O) O t5)) H25) in (let H27 \def 
(eq_ind T u1 (\lambda (t7: T).(pr0 t7 u2)) H8 u H22) in (let H28 \def (eq_ind 
T t3 (\lambda (t7: T).(pr0 t7 t4)) H9 (lift (S O) O t5) H21) in (ex2_ind T 
(\lambda (t7: T).(eq T t4 (lift (S O) O t7))) (\lambda (t7: T).(pr0 t5 t7)) 
(ex2 T (\lambda (t7: T).(pr0 (THead (Bind Abbr) u2 w) t7)) (\lambda (t7: 
T).(pr0 t2 t7))) (\lambda (x: T).(\lambda (H29: (eq T t4 (lift (S O) O 
x))).(\lambda (H30: (pr0 t5 x)).(let H31 \def (eq_ind T t4 (\lambda (t7: 
T).(subst0 O u2 t7 w)) H10 (lift (S O) O x) H29) in (ex2_ind T (\lambda (t7: 
T).(pr0 x t7)) (\lambda (t7: T).(pr0 t2 t7)) (ex2 T (\lambda (t7: T).(pr0 
(THead (Bind Abbr) u2 w) t7)) (\lambda (t7: T).(pr0 t2 t7))) (\lambda (x0: 
T).(\lambda (_: (pr0 x x0)).(\lambda (_: (pr0 t2 
x0)).(pr0_confluence__pr0_delta_tau u2 (lift (S O) O x) w H31 x (pr0_refl 
(lift (S O) O x)) t2)))) (H26 t5 (lift_tlt_dx (Bind Abbr) u t5 (S O) O) x H30 
t2 H17)))))) (pr0_gen_lift t5 t4 (S O) O H28)))))))))) H20)) H19))))) t6 
(sym_eq T t6 t2 H15))) t H13 H14 H11 H12))) | (pr0_tau t5 t6 H11 u) 
\Rightarrow (\lambda (H12: (eq T (THead (Flat Cast) u t5) t)).(\lambda (H13: 
(eq T t6 t2)).(eq_ind T (THead (Flat Cast) u t5) (\lambda (_: T).((eq T t6 
t2) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 (THead (Bind Abbr) u2 
w) t8)) (\lambda (t8: T).(pr0 t2 t8)))))) (\lambda (H14: (eq T t6 
t2)).(eq_ind T t2 (\lambda (t7: T).((pr0 t5 t7) \to (ex2 T (\lambda (t8: 
T).(pr0 (THead (Bind Abbr) u2 w) t8)) (\lambda (t8: T).(pr0 t2 t8))))) 
(\lambda (_: (pr0 t5 t2)).(let H16 \def (eq_ind_r T t (\lambda (t7: T).(eq T 
(THead (Bind Abbr) u1 t3) t7)) H5 (THead (Flat Cast) u t5) H12) in (let H17 
\def (eq_ind T (THead (Bind Abbr) u1 t3) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow 
False])])) I (THead (Flat Cast) u t5) H16) in (False_ind (ex2 T (\lambda (t7: 
T).(pr0 (THead (Bind Abbr) u2 w) t7)) (\lambda (t7: T).(pr0 t2 t7))) H17)))) 
t6 (sym_eq T t6 t2 H14))) t H12 H13 H11)))]) in (H11 (refl_equal T t) 
(refl_equal T t2)))))) t1 H7)) t H5 H6 H2 H3 H4))) | (pr0_zeta b H2 t3 t4 H3 
u) \Rightarrow (\lambda (H4: (eq T (THead (Bind b) u (lift (S O) O t3)) 
t)).(\lambda (H5: (eq T t4 t1)).(eq_ind T (THead (Bind b) u (lift (S O) O 
t3)) (\lambda (_: T).((eq T t4 t1) \to ((not (eq B b Abst)) \to ((pr0 t3 t4) 
\to (ex2 T (\lambda (t6: T).(pr0 t1 t6)) (\lambda (t6: T).(pr0 t2 t6))))))) 
(\lambda (H6: (eq T t4 t1)).(eq_ind T t1 (\lambda (t5: T).((not (eq B b 
Abst)) \to ((pr0 t3 t5) \to (ex2 T (\lambda (t6: T).(pr0 t1 t6)) (\lambda 
(t6: T).(pr0 t2 t6)))))) (\lambda (H7: (not (eq B b Abst))).(\lambda (H8: 
(pr0 t3 t1)).(let H9 \def (match H1 in pr0 return (\lambda (t5: T).(\lambda 
(t6: T).(\lambda (_: (pr0 t5 t6)).((eq T t5 t) \to ((eq T t6 t2) \to (ex2 T 
(\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t2 t7)))))))) with 
[(pr0_refl t5) \Rightarrow (\lambda (H9: (eq T t5 t)).(\lambda (H10: (eq T t5 
t2)).(eq_ind T t (\lambda (t6: T).((eq T t6 t2) \to (ex2 T (\lambda (t7: 
T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t2 t7))))) (\lambda (H11: (eq T t 
t2)).(eq_ind T t2 (\lambda (_: T).(ex2 T (\lambda (t7: T).(pr0 t1 t7)) 
(\lambda (t7: T).(pr0 t2 t7)))) (let H12 \def (eq_ind_r T t (\lambda (t6: 
T).(eq T t6 t2)) H11 (THead (Bind b) u (lift (S O) O t3)) H4) in (eq_ind T 
(THead (Bind b) u (lift (S O) O t3)) (\lambda (t6: T).(ex2 T (\lambda (t7: 
T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t6 t7)))) (let H13 \def (eq_ind_r T t 
(\lambda (t6: T).(eq T t5 t6)) H9 (THead (Bind b) u (lift (S O) O t3)) H4) in 
(let H14 \def (eq_ind_r T t (\lambda (t6: T).(\forall (v: T).((tlt v t6) \to 
(\forall (t7: T).((pr0 v t7) \to (\forall (t8: T).((pr0 v t8) \to (ex2 T 
(\lambda (t9: T).(pr0 t7 t9)) (\lambda (t9: T).(pr0 t8 t9)))))))))) H (THead 
(Bind b) u (lift (S O) O t3)) H4) in (ex_intro2 T (\lambda (t6: T).(pr0 t1 
t6)) (\lambda (t6: T).(pr0 (THead (Bind b) u (lift (S O) O t3)) t6)) t1 
(pr0_refl t1) (pr0_zeta b H7 t3 t1 H8 u)))) t2 H12)) t (sym_eq T t t2 H11))) 
t5 (sym_eq T t5 t H9) H10))) | (pr0_comp u1 u2 H9 t5 t6 H10 k) \Rightarrow 
(\lambda (H11: (eq T (THead k u1 t5) t)).(\lambda (H12: (eq T (THead k u2 t6) 
t2)).(eq_ind T (THead k u1 t5) (\lambda (_: T).((eq T (THead k u2 t6) t2) \to 
((pr0 u1 u2) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 t1 t8)) 
(\lambda (t8: T).(pr0 t2 t8))))))) (\lambda (H13: (eq T (THead k u2 t6) 
t2)).(eq_ind T (THead k u2 t6) (\lambda (t7: T).((pr0 u1 u2) \to ((pr0 t5 t6) 
\to (ex2 T (\lambda (t8: T).(pr0 t1 t8)) (\lambda (t8: T).(pr0 t7 t8)))))) 
(\lambda (_: (pr0 u1 u2)).(\lambda (H15: (pr0 t5 t6)).(let H16 \def (eq_ind_r 
T t (\lambda (t7: T).(eq T (THead (Bind b) u (lift (S O) O t3)) t7)) H4 
(THead k u1 t5) H11) in (let H17 \def (f_equal T K (\lambda (e: T).(match e 
in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow (Bind b) | (TLRef 
_) \Rightarrow (Bind b) | (THead k0 _ _) \Rightarrow k0])) (THead (Bind b) u 
(lift (S O) O t3)) (THead k u1 t5) H16) in ((let H18 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u | (TLRef _) \Rightarrow u | (THead _ t7 _) \Rightarrow t7])) 
(THead (Bind b) u (lift (S O) O t3)) (THead k u1 t5) H16) in ((let H19 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow ((let rec lref_map (f: ((nat \to nat))) (d: nat) (t7: 
T) on t7: T \def (match t7 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) 
\Rightarrow (TLRef (match (blt i d) with [true \Rightarrow i | false 
\Rightarrow (f i)])) | (THead k0 u0 t8) \Rightarrow (THead k0 (lref_map f d 
u0) (lref_map f (s k0 d) t8))]) in lref_map) (\lambda (x: nat).(plus x (S 
O))) O t3) | (TLRef _) \Rightarrow ((let rec lref_map (f: ((nat \to nat))) 
(d: nat) (t7: T) on t7: T \def (match t7 with [(TSort n) \Rightarrow (TSort 
n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with [true \Rightarrow i | 
false \Rightarrow (f i)])) | (THead k0 u0 t8) \Rightarrow (THead k0 (lref_map 
f d u0) (lref_map f (s k0 d) t8))]) in lref_map) (\lambda (x: nat).(plus x (S 
O))) O t3) | (THead _ _ t7) \Rightarrow t7])) (THead (Bind b) u (lift (S O) O 
t3)) (THead k u1 t5) H16) in (\lambda (_: (eq T u u1)).(\lambda (H21: (eq K 
(Bind b) k)).(eq_ind K (Bind b) (\lambda (k0: K).(ex2 T (\lambda (t7: T).(pr0 
t1 t7)) (\lambda (t7: T).(pr0 (THead k0 u2 t6) t7)))) (let H22 \def (eq_ind_r 
K k (\lambda (k0: K).(eq T (THead k0 u1 t5) t)) H11 (Bind b) H21) in (let H23 
\def (eq_ind_r T t5 (\lambda (t7: T).(pr0 t7 t6)) H15 (lift (S O) O t3) H19) 
in (ex2_ind T (\lambda (t7: T).(eq T t6 (lift (S O) O t7))) (\lambda (t7: 
T).(pr0 t3 t7)) (ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 
(THead (Bind b) u2 t6) t7))) (\lambda (x: T).(\lambda (H24: (eq T t6 (lift (S 
O) O x))).(\lambda (H25: (pr0 t3 x)).(let H26 \def (eq_ind_r T t5 (\lambda 
(t7: T).(eq T (THead (Bind b) u1 t7) t)) H22 (lift (S O) O t3) H19) in (let 
H27 \def (eq_ind_r T t (\lambda (t7: T).(\forall (v: T).((tlt v t7) \to 
(\forall (t8: T).((pr0 v t8) \to (\forall (t9: T).((pr0 v t9) \to (ex2 T 
(\lambda (t10: T).(pr0 t8 t10)) (\lambda (t10: T).(pr0 t9 t10)))))))))) H 
(THead (Bind b) u1 (lift (S O) O t3)) H26) in (eq_ind_r T (lift (S O) O x) 
(\lambda (t7: T).(ex2 T (\lambda (t8: T).(pr0 t1 t8)) (\lambda (t8: T).(pr0 
(THead (Bind b) u2 t7) t8)))) (ex2_ind T (\lambda (t7: T).(pr0 x t7)) 
(\lambda (t7: T).(pr0 t1 t7)) (ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda 
(t7: T).(pr0 (THead (Bind b) u2 (lift (S O) O x)) t7))) (\lambda (x0: 
T).(\lambda (H28: (pr0 x x0)).(\lambda (H29: (pr0 t1 x0)).(ex_intro2 T 
(\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 (THead (Bind b) u2 (lift 
(S O) O x)) t7)) x0 H29 (pr0_zeta b H7 x x0 H28 u2))))) (H27 t3 (lift_tlt_dx 
(Bind b) u1 t3 (S O) O) x H25 t1 H8)) t6 H24)))))) (pr0_gen_lift t3 t6 (S O) 
O H23)))) k H21)))) H18)) H17))))) t2 H13)) t H11 H12 H9 H10))) | (pr0_beta 
u0 v1 v2 H9 t5 t6 H10) \Rightarrow (\lambda (H11: (eq T (THead (Flat Appl) v1 
(THead (Bind Abst) u0 t5)) t)).(\lambda (H12: (eq T (THead (Bind Abbr) v2 t6) 
t2)).(eq_ind T (THead (Flat Appl) v1 (THead (Bind Abst) u0 t5)) (\lambda (_: 
T).((eq T (THead (Bind Abbr) v2 t6) t2) \to ((pr0 v1 v2) \to ((pr0 t5 t6) \to 
(ex2 T (\lambda (t8: T).(pr0 t1 t8)) (\lambda (t8: T).(pr0 t2 t8))))))) 
(\lambda (H13: (eq T (THead (Bind Abbr) v2 t6) t2)).(eq_ind T (THead (Bind 
Abbr) v2 t6) (\lambda (t7: T).((pr0 v1 v2) \to ((pr0 t5 t6) \to (ex2 T 
(\lambda (t8: T).(pr0 t1 t8)) (\lambda (t8: T).(pr0 t7 t8)))))) (\lambda (_: 
(pr0 v1 v2)).(\lambda (_: (pr0 t5 t6)).(let H16 \def (eq_ind_r T t (\lambda 
(t7: T).(eq T (THead (Bind b) u (lift (S O) O t3)) t7)) H4 (THead (Flat Appl) 
v1 (THead (Bind Abst) u0 t5)) H11) in (let H17 \def (eq_ind T (THead (Bind b) 
u (lift (S O) O t3)) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat 
Appl) v1 (THead (Bind Abst) u0 t5)) H16) in (False_ind (ex2 T (\lambda (t7: 
T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 (THead (Bind Abbr) v2 t6) t7))) 
H17))))) t2 H13)) t H11 H12 H9 H10))) | (pr0_upsilon b0 H9 v1 v2 H10 u1 u2 
H11 t5 t6 H12) \Rightarrow (\lambda (H13: (eq T (THead (Flat Appl) v1 (THead 
(Bind b0) u1 t5)) t)).(\lambda (H14: (eq T (THead (Bind b0) u2 (THead (Flat 
Appl) (lift (S O) O v2) t6)) t2)).(eq_ind T (THead (Flat Appl) v1 (THead 
(Bind b0) u1 t5)) (\lambda (_: T).((eq T (THead (Bind b0) u2 (THead (Flat 
Appl) (lift (S O) O v2) t6)) t2) \to ((not (eq B b0 Abst)) \to ((pr0 v1 v2) 
\to ((pr0 u1 u2) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 t1 t8)) 
(\lambda (t8: T).(pr0 t2 t8))))))))) (\lambda (H15: (eq T (THead (Bind b0) u2 
(THead (Flat Appl) (lift (S O) O v2) t6)) t2)).(eq_ind T (THead (Bind b0) u2 
(THead (Flat Appl) (lift (S O) O v2) t6)) (\lambda (t7: T).((not (eq B b0 
Abst)) \to ((pr0 v1 v2) \to ((pr0 u1 u2) \to ((pr0 t5 t6) \to (ex2 T (\lambda 
(t8: T).(pr0 t1 t8)) (\lambda (t8: T).(pr0 t7 t8)))))))) (\lambda (_: (not 
(eq B b0 Abst))).(\lambda (_: (pr0 v1 v2)).(\lambda (_: (pr0 u1 u2)).(\lambda 
(_: (pr0 t5 t6)).(let H20 \def (eq_ind_r T t (\lambda (t7: T).(eq T (THead 
(Bind b) u (lift (S O) O t3)) t7)) H4 (THead (Flat Appl) v1 (THead (Bind b0) 
u1 t5)) H13) in (let H21 \def (eq_ind T (THead (Bind b) u (lift (S O) O t3)) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | 
(Flat _) \Rightarrow False])])) I (THead (Flat Appl) v1 (THead (Bind b0) u1 
t5)) H20) in (False_ind (ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: 
T).(pr0 (THead (Bind b0) u2 (THead (Flat Appl) (lift (S O) O v2) t6)) t7))) 
H21))))))) t2 H15)) t H13 H14 H9 H10 H11 H12))) | (pr0_delta u1 u2 H9 t5 t6 
H10 w H11) \Rightarrow (\lambda (H12: (eq T (THead (Bind Abbr) u1 t5) 
t)).(\lambda (H13: (eq T (THead (Bind Abbr) u2 w) t2)).(eq_ind T (THead (Bind 
Abbr) u1 t5) (\lambda (_: T).((eq T (THead (Bind Abbr) u2 w) t2) \to ((pr0 u1 
u2) \to ((pr0 t5 t6) \to ((subst0 O u2 t6 w) \to (ex2 T (\lambda (t8: T).(pr0 
t1 t8)) (\lambda (t8: T).(pr0 t2 t8)))))))) (\lambda (H14: (eq T (THead (Bind 
Abbr) u2 w) t2)).(eq_ind T (THead (Bind Abbr) u2 w) (\lambda (t7: T).((pr0 u1 
u2) \to ((pr0 t5 t6) \to ((subst0 O u2 t6 w) \to (ex2 T (\lambda (t8: T).(pr0 
t1 t8)) (\lambda (t8: T).(pr0 t7 t8))))))) (\lambda (_: (pr0 u1 u2)).(\lambda 
(H16: (pr0 t5 t6)).(\lambda (H17: (subst0 O u2 t6 w)).(let H18 \def (eq_ind_r 
T t (\lambda (t7: T).(eq T (THead (Bind b) u (lift (S O) O t3)) t7)) H4 
(THead (Bind Abbr) u1 t5) H12) in (let H19 \def (f_equal T B (\lambda (e: 
T).(match e in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow b | 
(TLRef _) \Rightarrow b | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow 
b])])) (THead (Bind b) u (lift (S O) O t3)) (THead (Bind Abbr) u1 t5) H18) in 
((let H20 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow u | (TLRef _) \Rightarrow u | (THead _ t7 
_) \Rightarrow t7])) (THead (Bind b) u (lift (S O) O t3)) (THead (Bind Abbr) 
u1 t5) H18) in ((let H21 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map (f: 
((nat \to nat))) (d: nat) (t7: T) on t7: T \def (match t7 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t8) 
\Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t8))]) in 
lref_map) (\lambda (x: nat).(plus x (S O))) O t3) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t7: T) on t7: T \def (match 
t7 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k u0 t8) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t8))]) in lref_map) (\lambda (x: nat).(plus x (S O))) O t3) | (THead _ _ t7) 
\Rightarrow t7])) (THead (Bind b) u (lift (S O) O t3)) (THead (Bind Abbr) u1 
t5) H18) in (\lambda (_: (eq T u u1)).(\lambda (H23: (eq B b Abbr)).(let H24 
\def (eq_ind_r T t5 (\lambda (t7: T).(pr0 t7 t6)) H16 (lift (S O) O t3) H21) 
in (ex2_ind T (\lambda (t7: T).(eq T t6 (lift (S O) O t7))) (\lambda (t7: 
T).(pr0 t3 t7)) (ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 
(THead (Bind Abbr) u2 w) t7))) (\lambda (x: T).(\lambda (H25: (eq T t6 (lift 
(S O) O x))).(\lambda (H26: (pr0 t3 x)).(let H27 \def (eq_ind_r T t5 (\lambda 
(t7: T).(eq T (THead (Bind Abbr) u1 t7) t)) H12 (lift (S O) O t3) H21) in 
(let H28 \def (eq_ind_r T t (\lambda (t7: T).(\forall (v: T).((tlt v t7) \to 
(\forall (t8: T).((pr0 v t8) \to (\forall (t9: T).((pr0 v t9) \to (ex2 T 
(\lambda (t10: T).(pr0 t8 t10)) (\lambda (t10: T).(pr0 t9 t10)))))))))) H 
(THead (Bind Abbr) u1 (lift (S O) O t3)) H27) in (let H29 \def (eq_ind T t6 
(\lambda (t7: T).(subst0 O u2 t7 w)) H17 (lift (S O) O x) H25) in (let H30 
\def (eq_ind B b (\lambda (b0: B).(not (eq B b0 Abst))) H7 Abbr H23) in 
(ex2_ind T (\lambda (t7: T).(pr0 x t7)) (\lambda (t7: T).(pr0 t1 t7)) (ex2 T 
(\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 (THead (Bind Abbr) u2 w) 
t7))) (\lambda (x0: T).(\lambda (_: (pr0 x x0)).(\lambda (_: (pr0 t1 
x0)).(ex2_sym T (pr0 (THead (Bind Abbr) u2 w)) (pr0 t1) 
(pr0_confluence__pr0_delta_tau u2 (lift (S O) O x) w H29 x (pr0_refl (lift (S 
O) O x)) t1))))) (H28 t3 (lift_tlt_dx (Bind Abbr) u1 t3 (S O) O) x H26 t1 
H8))))))))) (pr0_gen_lift t3 t6 (S O) O H24)))))) H20)) H19)))))) t2 H14)) t 
H12 H13 H9 H10 H11))) | (pr0_zeta b0 H9 t5 t6 H10 u0) \Rightarrow (\lambda 
(H11: (eq T (THead (Bind b0) u0 (lift (S O) O t5)) t)).(\lambda (H12: (eq T 
t6 t2)).(eq_ind T (THead (Bind b0) u0 (lift (S O) O t5)) (\lambda (_: T).((eq 
T t6 t2) \to ((not (eq B b0 Abst)) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: 
T).(pr0 t1 t8)) (\lambda (t8: T).(pr0 t2 t8))))))) (\lambda (H13: (eq T t6 
t2)).(eq_ind T t2 (\lambda (t7: T).((not (eq B b0 Abst)) \to ((pr0 t5 t7) \to 
(ex2 T (\lambda (t8: T).(pr0 t1 t8)) (\lambda (t8: T).(pr0 t2 t8)))))) 
(\lambda (_: (not (eq B b0 Abst))).(\lambda (H15: (pr0 t5 t2)).(let H16 \def 
(eq_ind_r T t (\lambda (t7: T).(eq T (THead (Bind b) u (lift (S O) O t3)) 
t7)) H4 (THead (Bind b0) u0 (lift (S O) O t5)) H11) in (let H17 \def (f_equal 
T B (\lambda (e: T).(match e in T return (\lambda (_: T).B) with [(TSort _) 
\Rightarrow b | (TLRef _) \Rightarrow b | (THead k _ _) \Rightarrow (match k 
in K return (\lambda (_: K).B) with [(Bind b1) \Rightarrow b1 | (Flat _) 
\Rightarrow b])])) (THead (Bind b) u (lift (S O) O t3)) (THead (Bind b0) u0 
(lift (S O) O t5)) H16) in ((let H18 \def (f_equal T T (\lambda (e: T).(match 
e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u | (TLRef _) 
\Rightarrow u | (THead _ t7 _) \Rightarrow t7])) (THead (Bind b) u (lift (S 
O) O t3)) (THead (Bind b0) u0 (lift (S O) O t5)) H16) in ((let H19 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow ((let rec lref_map (f: ((nat \to nat))) (d: nat) (t7: 
T) on t7: T \def (match t7 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) 
\Rightarrow (TLRef (match (blt i d) with [true \Rightarrow i | false 
\Rightarrow (f i)])) | (THead k u1 t8) \Rightarrow (THead k (lref_map f d u1) 
(lref_map f (s k d) t8))]) in lref_map) (\lambda (x: nat).(plus x (S O))) O 
t3) | (TLRef _) \Rightarrow ((let rec lref_map (f: ((nat \to nat))) (d: nat) 
(t7: T) on t7: T \def (match t7 with [(TSort n) \Rightarrow (TSort n) | 
(TLRef i) \Rightarrow (TLRef (match (blt i d) with [true \Rightarrow i | 
false \Rightarrow (f i)])) | (THead k u1 t8) \Rightarrow (THead k (lref_map f 
d u1) (lref_map f (s k d) t8))]) in lref_map) (\lambda (x: nat).(plus x (S 
O))) O t3) | (THead _ _ t7) \Rightarrow t7])) (THead (Bind b) u (lift (S O) O 
t3)) (THead (Bind b0) u0 (lift (S O) O t5)) H16) in (\lambda (_: (eq T u 
u0)).(\lambda (H21: (eq B b b0)).(let H22 \def (eq_ind_r T t (\lambda (t7: 
T).(\forall (v: T).((tlt v t7) \to (\forall (t8: T).((pr0 v t8) \to (\forall 
(t9: T).((pr0 v t9) \to (ex2 T (\lambda (t10: T).(pr0 t8 t10)) (\lambda (t10: 
T).(pr0 t9 t10)))))))))) H (THead (Bind b0) u0 (lift (S O) O t5)) H11) in 
(let H23 \def (eq_ind T t3 (\lambda (t7: T).(pr0 t7 t1)) H8 t5 (lift_inj t3 
t5 (S O) O H19)) in (let H24 \def (eq_ind B b (\lambda (b1: B).(not (eq B b1 
Abst))) H7 b0 H21) in (ex2_ind T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: 
T).(pr0 t2 t7)) (ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t2 
t7))) (\lambda (x: T).(\lambda (H25: (pr0 t1 x)).(\lambda (H26: (pr0 t2 
x)).(ex_intro2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t2 t7)) 
x H25 H26)))) (H22 t5 (lift_tlt_dx (Bind b0) u0 t5 (S O) O) t1 H23 t2 
H15)))))))) H18)) H17))))) t6 (sym_eq T t6 t2 H13))) t H11 H12 H9 H10))) | 
(pr0_tau t5 t6 H9 u0) \Rightarrow (\lambda (H10: (eq T (THead (Flat Cast) u0 
t5) t)).(\lambda (H11: (eq T t6 t2)).(eq_ind T (THead (Flat Cast) u0 t5) 
(\lambda (_: T).((eq T t6 t2) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: 
T).(pr0 t1 t8)) (\lambda (t8: T).(pr0 t2 t8)))))) (\lambda (H12: (eq T t6 
t2)).(eq_ind T t2 (\lambda (t7: T).((pr0 t5 t7) \to (ex2 T (\lambda (t8: 
T).(pr0 t1 t8)) (\lambda (t8: T).(pr0 t2 t8))))) (\lambda (_: (pr0 t5 
t2)).(let H14 \def (eq_ind_r T t (\lambda (t7: T).(eq T (THead (Bind b) u 
(lift (S O) O t3)) t7)) H4 (THead (Flat Cast) u0 t5) H10) in (let H15 \def 
(eq_ind T (THead (Bind b) u (lift (S O) O t3)) (\lambda (ee: T).(match ee in 
T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow 
False])])) I (THead (Flat Cast) u0 t5) H14) in (False_ind (ex2 T (\lambda 
(t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t2 t7))) H15)))) t6 (sym_eq T t6 
t2 H12))) t H10 H11 H9)))]) in (H9 (refl_equal T t) (refl_equal T t2))))) t4 
(sym_eq T t4 t1 H6))) t H4 H5 H2 H3))) | (pr0_tau t3 t4 H2 u) \Rightarrow 
(\lambda (H3: (eq T (THead (Flat Cast) u t3) t)).(\lambda (H4: (eq T t4 
t1)).(eq_ind T (THead (Flat Cast) u t3) (\lambda (_: T).((eq T t4 t1) \to 
((pr0 t3 t4) \to (ex2 T (\lambda (t6: T).(pr0 t1 t6)) (\lambda (t6: T).(pr0 
t2 t6)))))) (\lambda (H5: (eq T t4 t1)).(eq_ind T t1 (\lambda (t5: T).((pr0 
t3 t5) \to (ex2 T (\lambda (t6: T).(pr0 t1 t6)) (\lambda (t6: T).(pr0 t2 
t6))))) (\lambda (H6: (pr0 t3 t1)).(let H7 \def (match H1 in pr0 return 
(\lambda (t5: T).(\lambda (t6: T).(\lambda (_: (pr0 t5 t6)).((eq T t5 t) \to 
((eq T t6 t2) \to (ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 
t2 t7)))))))) with [(pr0_refl t5) \Rightarrow (\lambda (H7: (eq T t5 
t)).(\lambda (H8: (eq T t5 t2)).(eq_ind T t (\lambda (t6: T).((eq T t6 t2) 
\to (ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t2 t7))))) 
(\lambda (H9: (eq T t t2)).(eq_ind T t2 (\lambda (_: T).(ex2 T (\lambda (t7: 
T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t2 t7)))) (let H10 \def (eq_ind_r T t 
(\lambda (t6: T).(eq T t6 t2)) H9 (THead (Flat Cast) u t3) H3) in (eq_ind T 
(THead (Flat Cast) u t3) (\lambda (t6: T).(ex2 T (\lambda (t7: T).(pr0 t1 
t7)) (\lambda (t7: T).(pr0 t6 t7)))) (let H11 \def (eq_ind_r T t (\lambda 
(t6: T).(eq T t5 t6)) H7 (THead (Flat Cast) u t3) H3) in (let H12 \def 
(eq_ind_r T t (\lambda (t6: T).(\forall (v: T).((tlt v t6) \to (\forall (t7: 
T).((pr0 v t7) \to (\forall (t8: T).((pr0 v t8) \to (ex2 T (\lambda (t9: 
T).(pr0 t7 t9)) (\lambda (t9: T).(pr0 t8 t9)))))))))) H (THead (Flat Cast) u 
t3) H3) in (ex_intro2 T (\lambda (t6: T).(pr0 t1 t6)) (\lambda (t6: T).(pr0 
(THead (Flat Cast) u t3) t6)) t1 (pr0_refl t1) (pr0_tau t3 t1 H6 u)))) t2 
H10)) t (sym_eq T t t2 H9))) t5 (sym_eq T t5 t H7) H8))) | (pr0_comp u1 u2 H7 
t5 t6 H8 k) \Rightarrow (\lambda (H9: (eq T (THead k u1 t5) t)).(\lambda 
(H10: (eq T (THead k u2 t6) t2)).(eq_ind T (THead k u1 t5) (\lambda (_: 
T).((eq T (THead k u2 t6) t2) \to ((pr0 u1 u2) \to ((pr0 t5 t6) \to (ex2 T 
(\lambda (t8: T).(pr0 t1 t8)) (\lambda (t8: T).(pr0 t2 t8))))))) (\lambda 
(H11: (eq T (THead k u2 t6) t2)).(eq_ind T (THead k u2 t6) (\lambda (t7: 
T).((pr0 u1 u2) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 t1 t8)) 
(\lambda (t8: T).(pr0 t7 t8)))))) (\lambda (_: (pr0 u1 u2)).(\lambda (H13: 
(pr0 t5 t6)).(let H14 \def (eq_ind_r T t (\lambda (t7: T).(eq T (THead (Flat 
Cast) u t3) t7)) H3 (THead k u1 t5) H9) in (let H15 \def (f_equal T K 
(\lambda (e: T).(match e in T return (\lambda (_: T).K) with [(TSort _) 
\Rightarrow (Flat Cast) | (TLRef _) \Rightarrow (Flat Cast) | (THead k0 _ _) 
\Rightarrow k0])) (THead (Flat Cast) u t3) (THead k u1 t5) H14) in ((let H16 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow u | (TLRef _) \Rightarrow u | (THead _ t7 _) 
\Rightarrow t7])) (THead (Flat Cast) u t3) (THead k u1 t5) H14) in ((let H17 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead _ _ t7) 
\Rightarrow t7])) (THead (Flat Cast) u t3) (THead k u1 t5) H14) in (\lambda 
(_: (eq T u u1)).(\lambda (H19: (eq K (Flat Cast) k)).(eq_ind K (Flat Cast) 
(\lambda (k0: K).(ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 
(THead k0 u2 t6) t7)))) (let H20 \def (eq_ind_r K k (\lambda (k0: K).(eq T 
(THead k0 u1 t5) t)) H9 (Flat Cast) H19) in (let H21 \def (eq_ind_r T t 
(\lambda (t7: T).(\forall (v: T).((tlt v t7) \to (\forall (t8: T).((pr0 v t8) 
\to (\forall (t9: T).((pr0 v t9) \to (ex2 T (\lambda (t10: T).(pr0 t8 t10)) 
(\lambda (t10: T).(pr0 t9 t10)))))))))) H (THead (Flat Cast) u1 t5) H20) in 
(let H22 \def (eq_ind T t3 (\lambda (t7: T).(pr0 t7 t1)) H6 t5 H17) in 
(ex2_ind T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t6 t7)) (ex2 T 
(\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 (THead (Flat Cast) u2 t6) 
t7))) (\lambda (x: T).(\lambda (H23: (pr0 t1 x)).(\lambda (H24: (pr0 t6 
x)).(ex_intro2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 (THead 
(Flat Cast) u2 t6) t7)) x H23 (pr0_tau t6 x H24 u2))))) (H21 t5 (tlt_head_dx 
(Flat Cast) u1 t5) t1 H22 t6 H13))))) k H19)))) H16)) H15))))) t2 H11)) t H9 
H10 H7 H8))) | (pr0_beta u0 v1 v2 H7 t5 t6 H8) \Rightarrow (\lambda (H9: (eq 
T (THead (Flat Appl) v1 (THead (Bind Abst) u0 t5)) t)).(\lambda (H10: (eq T 
(THead (Bind Abbr) v2 t6) t2)).(eq_ind T (THead (Flat Appl) v1 (THead (Bind 
Abst) u0 t5)) (\lambda (_: T).((eq T (THead (Bind Abbr) v2 t6) t2) \to ((pr0 
v1 v2) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 t1 t8)) (\lambda 
(t8: T).(pr0 t2 t8))))))) (\lambda (H11: (eq T (THead (Bind Abbr) v2 t6) 
t2)).(eq_ind T (THead (Bind Abbr) v2 t6) (\lambda (t7: T).((pr0 v1 v2) \to 
((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 t1 t8)) (\lambda (t8: T).(pr0 
t7 t8)))))) (\lambda (_: (pr0 v1 v2)).(\lambda (_: (pr0 t5 t6)).(let H14 \def 
(eq_ind_r T t (\lambda (t7: T).(eq T (THead (Flat Cast) u t3) t7)) H3 (THead 
(Flat Appl) v1 (THead (Bind Abst) u0 t5)) H9) in (let H15 \def (eq_ind T 
(THead (Flat Cast) u t3) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow False | (Flat f) \Rightarrow (match f in F return 
(\lambda (_: F).Prop) with [Appl \Rightarrow False | Cast \Rightarrow 
True])])])) I (THead (Flat Appl) v1 (THead (Bind Abst) u0 t5)) H14) in 
(False_ind (ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 (THead 
(Bind Abbr) v2 t6) t7))) H15))))) t2 H11)) t H9 H10 H7 H8))) | (pr0_upsilon b 
H7 v1 v2 H8 u1 u2 H9 t5 t6 H10) \Rightarrow (\lambda (H11: (eq T (THead (Flat 
Appl) v1 (THead (Bind b) u1 t5)) t)).(\lambda (H12: (eq T (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t6)) t2)).(eq_ind T (THead (Flat Appl) 
v1 (THead (Bind b) u1 t5)) (\lambda (_: T).((eq T (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t6)) t2) \to ((not (eq B b Abst)) \to ((pr0 v1 
v2) \to ((pr0 u1 u2) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 t1 
t8)) (\lambda (t8: T).(pr0 t2 t8))))))))) (\lambda (H13: (eq T (THead (Bind 
b) u2 (THead (Flat Appl) (lift (S O) O v2) t6)) t2)).(eq_ind T (THead (Bind 
b) u2 (THead (Flat Appl) (lift (S O) O v2) t6)) (\lambda (t7: T).((not (eq B 
b Abst)) \to ((pr0 v1 v2) \to ((pr0 u1 u2) \to ((pr0 t5 t6) \to (ex2 T 
(\lambda (t8: T).(pr0 t1 t8)) (\lambda (t8: T).(pr0 t7 t8)))))))) (\lambda 
(_: (not (eq B b Abst))).(\lambda (_: (pr0 v1 v2)).(\lambda (_: (pr0 u1 
u2)).(\lambda (_: (pr0 t5 t6)).(let H18 \def (eq_ind_r T t (\lambda (t7: 
T).(eq T (THead (Flat Cast) u t3) t7)) H3 (THead (Flat Appl) v1 (THead (Bind 
b) u1 t5)) H11) in (let H19 \def (eq_ind T (THead (Flat Cast) u t3) (\lambda 
(ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | 
(Flat f) \Rightarrow (match f in F return (\lambda (_: F).Prop) with [Appl 
\Rightarrow False | Cast \Rightarrow True])])])) I (THead (Flat Appl) v1 
(THead (Bind b) u1 t5)) H18) in (False_ind (ex2 T (\lambda (t7: T).(pr0 t1 
t7)) (\lambda (t7: T).(pr0 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) 
O v2) t6)) t7))) H19))))))) t2 H13)) t H11 H12 H7 H8 H9 H10))) | (pr0_delta 
u1 u2 H7 t5 t6 H8 w H9) \Rightarrow (\lambda (H10: (eq T (THead (Bind Abbr) 
u1 t5) t)).(\lambda (H11: (eq T (THead (Bind Abbr) u2 w) t2)).(eq_ind T 
(THead (Bind Abbr) u1 t5) (\lambda (_: T).((eq T (THead (Bind Abbr) u2 w) t2) 
\to ((pr0 u1 u2) \to ((pr0 t5 t6) \to ((subst0 O u2 t6 w) \to (ex2 T (\lambda 
(t8: T).(pr0 t1 t8)) (\lambda (t8: T).(pr0 t2 t8)))))))) (\lambda (H12: (eq T 
(THead (Bind Abbr) u2 w) t2)).(eq_ind T (THead (Bind Abbr) u2 w) (\lambda 
(t7: T).((pr0 u1 u2) \to ((pr0 t5 t6) \to ((subst0 O u2 t6 w) \to (ex2 T 
(\lambda (t8: T).(pr0 t1 t8)) (\lambda (t8: T).(pr0 t7 t8))))))) (\lambda (_: 
(pr0 u1 u2)).(\lambda (_: (pr0 t5 t6)).(\lambda (_: (subst0 O u2 t6 w)).(let 
H16 \def (eq_ind_r T t (\lambda (t7: T).(eq T (THead (Flat Cast) u t3) t7)) 
H3 (THead (Bind Abbr) u1 t5) H10) in (let H17 \def (eq_ind T (THead (Flat 
Cast) u t3) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind Abbr) u1 
t5) H16) in (False_ind (ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: 
T).(pr0 (THead (Bind Abbr) u2 w) t7))) H17)))))) t2 H12)) t H10 H11 H7 H8 
H9))) | (pr0_zeta b H7 t5 t6 H8 u0) \Rightarrow (\lambda (H9: (eq T (THead 
(Bind b) u0 (lift (S O) O t5)) t)).(\lambda (H10: (eq T t6 t2)).(eq_ind T 
(THead (Bind b) u0 (lift (S O) O t5)) (\lambda (_: T).((eq T t6 t2) \to ((not 
(eq B b Abst)) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 t1 t8)) 
(\lambda (t8: T).(pr0 t2 t8))))))) (\lambda (H11: (eq T t6 t2)).(eq_ind T t2 
(\lambda (t7: T).((not (eq B b Abst)) \to ((pr0 t5 t7) \to (ex2 T (\lambda 
(t8: T).(pr0 t1 t8)) (\lambda (t8: T).(pr0 t2 t8)))))) (\lambda (_: (not (eq 
B b Abst))).(\lambda (_: (pr0 t5 t2)).(let H14 \def (eq_ind_r T t (\lambda 
(t7: T).(eq T (THead (Flat Cast) u t3) t7)) H3 (THead (Bind b) u0 (lift (S O) 
O t5)) H9) in (let H15 \def (eq_ind T (THead (Flat Cast) u t3) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K 
return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) I (THead (Bind b) u0 (lift (S O) O t5)) H14) in 
(False_ind (ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t2 
t7))) H15))))) t6 (sym_eq T t6 t2 H11))) t H9 H10 H7 H8))) | (pr0_tau t5 t6 
H7 u0) \Rightarrow (\lambda (H8: (eq T (THead (Flat Cast) u0 t5) t)).(\lambda 
(H9: (eq T t6 t2)).(eq_ind T (THead (Flat Cast) u0 t5) (\lambda (_: T).((eq T 
t6 t2) \to ((pr0 t5 t6) \to (ex2 T (\lambda (t8: T).(pr0 t1 t8)) (\lambda 
(t8: T).(pr0 t2 t8)))))) (\lambda (H10: (eq T t6 t2)).(eq_ind T t2 (\lambda 
(t7: T).((pr0 t5 t7) \to (ex2 T (\lambda (t8: T).(pr0 t1 t8)) (\lambda (t8: 
T).(pr0 t2 t8))))) (\lambda (H11: (pr0 t5 t2)).(let H12 \def (eq_ind_r T t 
(\lambda (t7: T).(eq T (THead (Flat Cast) u t3) t7)) H3 (THead (Flat Cast) u0 
t5) H8) in (let H13 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow u | (TLRef _) \Rightarrow u | 
(THead _ t7 _) \Rightarrow t7])) (THead (Flat Cast) u t3) (THead (Flat Cast) 
u0 t5) H12) in ((let H14 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow t3 | (TLRef _) 
\Rightarrow t3 | (THead _ _ t7) \Rightarrow t7])) (THead (Flat Cast) u t3) 
(THead (Flat Cast) u0 t5) H12) in (\lambda (_: (eq T u u0)).(let H16 \def 
(eq_ind_r T t (\lambda (t7: T).(\forall (v: T).((tlt v t7) \to (\forall (t8: 
T).((pr0 v t8) \to (\forall (t9: T).((pr0 v t9) \to (ex2 T (\lambda (t10: 
T).(pr0 t8 t10)) (\lambda (t10: T).(pr0 t9 t10)))))))))) H (THead (Flat Cast) 
u0 t5) H8) in (let H17 \def (eq_ind T t3 (\lambda (t7: T).(pr0 t7 t1)) H6 t5 
H14) in (ex2_ind T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t2 
t7)) (ex2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t2 t7))) 
(\lambda (x: T).(\lambda (H18: (pr0 t1 x)).(\lambda (H19: (pr0 t2 
x)).(ex_intro2 T (\lambda (t7: T).(pr0 t1 t7)) (\lambda (t7: T).(pr0 t2 t7)) 
x H18 H19)))) (H16 t5 (tlt_head_dx (Flat Cast) u0 t5) t1 H17 t2 H11)))))) 
H13)))) t6 (sym_eq T t6 t2 H10))) t H8 H9 H7)))]) in (H7 (refl_equal T t) 
(refl_equal T t2)))) t4 (sym_eq T t4 t1 H5))) t H3 H4 H2)))]) in (H2 
(refl_equal T t) (refl_equal T t1))))))))) t0).
(* COMMENTS
Initial nodes: 46103
END *)

