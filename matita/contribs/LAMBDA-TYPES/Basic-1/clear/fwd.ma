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

include "Basic-1/clear/defs.ma".

theorem clear_gen_sort:
 \forall (x: C).(\forall (n: nat).((clear (CSort n) x) \to (\forall (P: 
Prop).P)))
\def
 \lambda (x: C).(\lambda (n: nat).(\lambda (H: (clear (CSort n) x)).(\lambda 
(P: Prop).(insert_eq C (CSort n) (\lambda (c: C).(clear c x)) (\lambda (_: 
C).P) (\lambda (y: C).(\lambda (H0: (clear y x)).(clear_ind (\lambda (c: 
C).(\lambda (_: C).((eq C c (CSort n)) \to P))) (\lambda (b: B).(\lambda (e: 
C).(\lambda (u: T).(\lambda (H1: (eq C (CHead e (Bind b) u) (CSort n))).(let 
H2 \def (eq_ind C (CHead e (Bind b) u) (\lambda (ee: C).(match ee in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ _ _) 
\Rightarrow True])) I (CSort n) H1) in (False_ind P H2)))))) (\lambda (e: 
C).(\lambda (c: C).(\lambda (_: (clear e c)).(\lambda (_: (((eq C e (CSort 
n)) \to P))).(\lambda (f: F).(\lambda (u: T).(\lambda (H3: (eq C (CHead e 
(Flat f) u) (CSort n))).(let H4 \def (eq_ind C (CHead e (Flat f) u) (\lambda 
(ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ _ _) \Rightarrow True])) I (CSort n) H3) in 
(False_ind P H4))))))))) y x H0))) H)))).
(* COMMENTS
Initial nodes: 215
END *)

theorem clear_gen_bind:
 \forall (b: B).(\forall (e: C).(\forall (x: C).(\forall (u: T).((clear 
(CHead e (Bind b) u) x) \to (eq C x (CHead e (Bind b) u))))))
\def
 \lambda (b: B).(\lambda (e: C).(\lambda (x: C).(\lambda (u: T).(\lambda (H: 
(clear (CHead e (Bind b) u) x)).(insert_eq C (CHead e (Bind b) u) (\lambda 
(c: C).(clear c x)) (\lambda (c: C).(eq C x c)) (\lambda (y: C).(\lambda (H0: 
(clear y x)).(clear_ind (\lambda (c: C).(\lambda (c0: C).((eq C c (CHead e 
(Bind b) u)) \to (eq C c0 c)))) (\lambda (b0: B).(\lambda (e0: C).(\lambda 
(u0: T).(\lambda (H1: (eq C (CHead e0 (Bind b0) u0) (CHead e (Bind b) 
u))).(let H2 \def (f_equal C C (\lambda (e1: C).(match e1 in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow e0 | (CHead c _ _) \Rightarrow 
c])) (CHead e0 (Bind b0) u0) (CHead e (Bind b) u) H1) in ((let H3 \def 
(f_equal C B (\lambda (e1: C).(match e1 in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow b0 | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow 
b0])])) (CHead e0 (Bind b0) u0) (CHead e (Bind b) u) H1) in ((let H4 \def 
(f_equal C T (\lambda (e1: C).(match e1 in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) (CHead e0 (Bind 
b0) u0) (CHead e (Bind b) u) H1) in (\lambda (H5: (eq B b0 b)).(\lambda (H6: 
(eq C e0 e)).(eq_ind_r T u (\lambda (t: T).(eq C (CHead e0 (Bind b0) t) 
(CHead e0 (Bind b0) t))) (eq_ind_r C e (\lambda (c: C).(eq C (CHead c (Bind 
b0) u) (CHead c (Bind b0) u))) (eq_ind_r B b (\lambda (b1: B).(eq C (CHead e 
(Bind b1) u) (CHead e (Bind b1) u))) (refl_equal C (CHead e (Bind b) u)) b0 
H5) e0 H6) u0 H4)))) H3)) H2)))))) (\lambda (e0: C).(\lambda (c: C).(\lambda 
(_: (clear e0 c)).(\lambda (_: (((eq C e0 (CHead e (Bind b) u)) \to (eq C c 
e0)))).(\lambda (f: F).(\lambda (u0: T).(\lambda (H3: (eq C (CHead e0 (Flat 
f) u0) (CHead e (Bind b) u))).(let H4 \def (eq_ind C (CHead e0 (Flat f) u0) 
(\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (CHead e (Bind b) u) H3) in (False_ind (eq C c (CHead e0 (Flat f) 
u0)) H4))))))))) y x H0))) H))))).
(* COMMENTS
Initial nodes: 525
END *)

theorem clear_gen_flat:
 \forall (f: F).(\forall (e: C).(\forall (x: C).(\forall (u: T).((clear 
(CHead e (Flat f) u) x) \to (clear e x)))))
\def
 \lambda (f: F).(\lambda (e: C).(\lambda (x: C).(\lambda (u: T).(\lambda (H: 
(clear (CHead e (Flat f) u) x)).(insert_eq C (CHead e (Flat f) u) (\lambda 
(c: C).(clear c x)) (\lambda (_: C).(clear e x)) (\lambda (y: C).(\lambda 
(H0: (clear y x)).(clear_ind (\lambda (c: C).(\lambda (c0: C).((eq C c (CHead 
e (Flat f) u)) \to (clear e c0)))) (\lambda (b: B).(\lambda (e0: C).(\lambda 
(u0: T).(\lambda (H1: (eq C (CHead e0 (Bind b) u0) (CHead e (Flat f) 
u))).(let H2 \def (eq_ind C (CHead e0 (Bind b) u0) (\lambda (ee: C).(match ee 
in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead 
_ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow True | (Flat _) \Rightarrow False])])) I (CHead e (Flat f) u) H1) 
in (False_ind (clear e (CHead e0 (Bind b) u0)) H2)))))) (\lambda (e0: 
C).(\lambda (c: C).(\lambda (H1: (clear e0 c)).(\lambda (H2: (((eq C e0 
(CHead e (Flat f) u)) \to (clear e c)))).(\lambda (f0: F).(\lambda (u0: 
T).(\lambda (H3: (eq C (CHead e0 (Flat f0) u0) (CHead e (Flat f) u))).(let H4 
\def (f_equal C C (\lambda (e1: C).(match e1 in C return (\lambda (_: C).C) 
with [(CSort _) \Rightarrow e0 | (CHead c0 _ _) \Rightarrow c0])) (CHead e0 
(Flat f0) u0) (CHead e (Flat f) u) H3) in ((let H5 \def (f_equal C F (\lambda 
(e1: C).(match e1 in C return (\lambda (_: C).F) with [(CSort _) \Rightarrow 
f0 | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).F) with 
[(Bind _) \Rightarrow f0 | (Flat f1) \Rightarrow f1])])) (CHead e0 (Flat f0) 
u0) (CHead e (Flat f) u) H3) in ((let H6 \def (f_equal C T (\lambda (e1: 
C).(match e1 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | 
(CHead _ _ t) \Rightarrow t])) (CHead e0 (Flat f0) u0) (CHead e (Flat f) u) 
H3) in (\lambda (_: (eq F f0 f)).(\lambda (H8: (eq C e0 e)).(let H9 \def 
(eq_ind C e0 (\lambda (c0: C).((eq C c0 (CHead e (Flat f) u)) \to (clear e 
c))) H2 e H8) in (let H10 \def (eq_ind C e0 (\lambda (c0: C).(clear c0 c)) H1 
e H8) in H10))))) H5)) H4))))))))) y x H0))) H))))).
(* COMMENTS
Initial nodes: 453
END *)

theorem clear_gen_flat_r:
 \forall (f: F).(\forall (x: C).(\forall (e: C).(\forall (u: T).((clear x 
(CHead e (Flat f) u)) \to (\forall (P: Prop).P)))))
\def
 \lambda (f: F).(\lambda (x: C).(\lambda (e: C).(\lambda (u: T).(\lambda (H: 
(clear x (CHead e (Flat f) u))).(\lambda (P: Prop).(insert_eq C (CHead e 
(Flat f) u) (\lambda (c: C).(clear x c)) (\lambda (_: C).P) (\lambda (y: 
C).(\lambda (H0: (clear x y)).(clear_ind (\lambda (_: C).(\lambda (c0: 
C).((eq C c0 (CHead e (Flat f) u)) \to P))) (\lambda (b: B).(\lambda (e0: 
C).(\lambda (u0: T).(\lambda (H1: (eq C (CHead e0 (Bind b) u0) (CHead e (Flat 
f) u))).(let H2 \def (eq_ind C (CHead e0 (Bind b) u0) (\lambda (ee: C).(match 
ee in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | 
(CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) I (CHead e (Flat 
f) u) H1) in (False_ind P H2)))))) (\lambda (e0: C).(\lambda (c: C).(\lambda 
(H1: (clear e0 c)).(\lambda (H2: (((eq C c (CHead e (Flat f) u)) \to 
P))).(\lambda (_: F).(\lambda (_: T).(\lambda (H3: (eq C c (CHead e (Flat f) 
u))).(let H4 \def (eq_ind C c (\lambda (c0: C).((eq C c0 (CHead e (Flat f) 
u)) \to P)) H2 (CHead e (Flat f) u) H3) in (let H5 \def (eq_ind C c (\lambda 
(c0: C).(clear e0 c0)) H1 (CHead e (Flat f) u) H3) in (H4 (refl_equal C 
(CHead e (Flat f) u)))))))))))) x y H0))) H)))))).
(* COMMENTS
Initial nodes: 303
END *)

theorem clear_gen_all:
 \forall (c1: C).(\forall (c2: C).((clear c1 c2) \to (ex_3 B C T (\lambda (b: 
B).(\lambda (e: C).(\lambda (u: T).(eq C c2 (CHead e (Bind b) u))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (clear c1 c2)).(clear_ind 
(\lambda (_: C).(\lambda (c0: C).(ex_3 B C T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u: T).(eq C c0 (CHead e (Bind b) u)))))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (u: T).(ex_3_intro B C T (\lambda (b0: 
B).(\lambda (e0: C).(\lambda (u0: T).(eq C (CHead e (Bind b) u) (CHead e0 
(Bind b0) u0))))) b e u (refl_equal C (CHead e (Bind b) u)))))) (\lambda (e: 
C).(\lambda (c: C).(\lambda (H0: (clear e c)).(\lambda (H1: (ex_3 B C T 
(\lambda (b: B).(\lambda (e0: C).(\lambda (u: T).(eq C c (CHead e0 (Bind b) 
u))))))).(\lambda (_: F).(\lambda (_: T).(let H2 \def H1 in (ex_3_ind B C T 
(\lambda (b: B).(\lambda (e0: C).(\lambda (u0: T).(eq C c (CHead e0 (Bind b) 
u0))))) (ex_3 B C T (\lambda (b: B).(\lambda (e0: C).(\lambda (u0: T).(eq C c 
(CHead e0 (Bind b) u0)))))) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: 
T).(\lambda (H3: (eq C c (CHead x1 (Bind x0) x2))).(let H4 \def (eq_ind C c 
(\lambda (c0: C).(clear e c0)) H0 (CHead x1 (Bind x0) x2) H3) in (eq_ind_r C 
(CHead x1 (Bind x0) x2) (\lambda (c0: C).(ex_3 B C T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u0: T).(eq C c0 (CHead e0 (Bind b) u0))))))) (ex_3_intro B 
C T (\lambda (b: B).(\lambda (e0: C).(\lambda (u0: T).(eq C (CHead x1 (Bind 
x0) x2) (CHead e0 (Bind b) u0))))) x0 x1 x2 (refl_equal C (CHead x1 (Bind x0) 
x2))) c H3)))))) H2)))))))) c1 c2 H))).
(* COMMENTS
Initial nodes: 381
END *)

