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

include "Basic-1/pr3/props.ma".

theorem sn3_gen_bind:
 \forall (b: B).(\forall (c: C).(\forall (u: T).(\forall (t: T).((sn3 c 
(THead (Bind b) u t)) \to (land (sn3 c u) (sn3 (CHead c (Bind b) u) t))))))
\def
 \lambda (b: B).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: 
(sn3 c (THead (Bind b) u t))).(insert_eq T (THead (Bind b) u t) (\lambda (t0: 
T).(sn3 c t0)) (\lambda (_: T).(land (sn3 c u) (sn3 (CHead c (Bind b) u) t))) 
(\lambda (y: T).(\lambda (H0: (sn3 c y)).(unintro T t (\lambda (t0: T).((eq T 
y (THead (Bind b) u t0)) \to (land (sn3 c u) (sn3 (CHead c (Bind b) u) t0)))) 
(unintro T u (\lambda (t0: T).(\forall (x: T).((eq T y (THead (Bind b) t0 x)) 
\to (land (sn3 c t0) (sn3 (CHead c (Bind b) t0) x))))) (sn3_ind c (\lambda 
(t0: T).(\forall (x: T).(\forall (x0: T).((eq T t0 (THead (Bind b) x x0)) \to 
(land (sn3 c x) (sn3 (CHead c (Bind b) x) x0)))))) (\lambda (t1: T).(\lambda 
(H1: ((\forall (t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 
c t1 t2) \to (sn3 c t2)))))).(\lambda (H2: ((\forall (t2: T).((((eq T t1 t2) 
\to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to (\forall (x: T).(\forall 
(x0: T).((eq T t2 (THead (Bind b) x x0)) \to (land (sn3 c x) (sn3 (CHead c 
(Bind b) x) x0)))))))))).(\lambda (x: T).(\lambda (x0: T).(\lambda (H3: (eq T 
t1 (THead (Bind b) x x0))).(let H4 \def (eq_ind T t1 (\lambda (t0: 
T).(\forall (t2: T).((((eq T t0 t2) \to (\forall (P: Prop).P))) \to ((pr3 c 
t0 t2) \to (\forall (x1: T).(\forall (x2: T).((eq T t2 (THead (Bind b) x1 
x2)) \to (land (sn3 c x1) (sn3 (CHead c (Bind b) x1) x2))))))))) H2 (THead 
(Bind b) x x0) H3) in (let H5 \def (eq_ind T t1 (\lambda (t0: T).(\forall 
(t2: T).((((eq T t0 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t0 t2) \to 
(sn3 c t2))))) H1 (THead (Bind b) x x0) H3) in (conj (sn3 c x) (sn3 (CHead c 
(Bind b) x) x0) (sn3_sing c x (\lambda (t2: T).(\lambda (H6: (((eq T x t2) 
\to (\forall (P: Prop).P)))).(\lambda (H7: (pr3 c x t2)).(let H8 \def (H4 
(THead (Bind b) t2 x0) (\lambda (H8: (eq T (THead (Bind b) x x0) (THead (Bind 
b) t2 x0))).(\lambda (P: Prop).(let H9 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x | 
(TLRef _) \Rightarrow x | (THead _ t0 _) \Rightarrow t0])) (THead (Bind b) x 
x0) (THead (Bind b) t2 x0) H8) in (let H10 \def (eq_ind_r T t2 (\lambda (t0: 
T).(pr3 c x t0)) H7 x H9) in (let H11 \def (eq_ind_r T t2 (\lambda (t0: 
T).((eq T x t0) \to (\forall (P0: Prop).P0))) H6 x H9) in (H11 (refl_equal T 
x) P)))))) (pr3_head_12 c x t2 H7 (Bind b) x0 x0 (pr3_refl (CHead c (Bind b) 
t2) x0)) t2 x0 (refl_equal T (THead (Bind b) t2 x0))) in (land_ind (sn3 c t2) 
(sn3 (CHead c (Bind b) t2) x0) (sn3 c t2) (\lambda (H9: (sn3 c t2)).(\lambda 
(_: (sn3 (CHead c (Bind b) t2) x0)).H9)) H8)))))) (sn3_sing (CHead c (Bind b) 
x) x0 (\lambda (t2: T).(\lambda (H6: (((eq T x0 t2) \to (\forall (P: 
Prop).P)))).(\lambda (H7: (pr3 (CHead c (Bind b) x) x0 t2)).(let H8 \def (H4 
(THead (Bind b) x t2) (\lambda (H8: (eq T (THead (Bind b) x x0) (THead (Bind 
b) x t2))).(\lambda (P: Prop).(let H9 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | 
(TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Bind b) x 
x0) (THead (Bind b) x t2) H8) in (let H10 \def (eq_ind_r T t2 (\lambda (t0: 
T).(pr3 (CHead c (Bind b) x) x0 t0)) H7 x0 H9) in (let H11 \def (eq_ind_r T 
t2 (\lambda (t0: T).((eq T x0 t0) \to (\forall (P0: Prop).P0))) H6 x0 H9) in 
(H11 (refl_equal T x0) P)))))) (pr3_head_12 c x x (pr3_refl c x) (Bind b) x0 
t2 H7) x t2 (refl_equal T (THead (Bind b) x t2))) in (land_ind (sn3 c x) (sn3 
(CHead c (Bind b) x) t2) (sn3 (CHead c (Bind b) x) t2) (\lambda (_: (sn3 c 
x)).(\lambda (H10: (sn3 (CHead c (Bind b) x) t2)).H10)) H8))))))))))))))) y 
H0))))) H))))).
(* COMMENTS
Initial nodes: 1055
END *)

theorem sn3_gen_flat:
 \forall (f: F).(\forall (c: C).(\forall (u: T).(\forall (t: T).((sn3 c 
(THead (Flat f) u t)) \to (land (sn3 c u) (sn3 c t))))))
\def
 \lambda (f: F).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: 
(sn3 c (THead (Flat f) u t))).(insert_eq T (THead (Flat f) u t) (\lambda (t0: 
T).(sn3 c t0)) (\lambda (_: T).(land (sn3 c u) (sn3 c t))) (\lambda (y: 
T).(\lambda (H0: (sn3 c y)).(unintro T t (\lambda (t0: T).((eq T y (THead 
(Flat f) u t0)) \to (land (sn3 c u) (sn3 c t0)))) (unintro T u (\lambda (t0: 
T).(\forall (x: T).((eq T y (THead (Flat f) t0 x)) \to (land (sn3 c t0) (sn3 
c x))))) (sn3_ind c (\lambda (t0: T).(\forall (x: T).(\forall (x0: T).((eq T 
t0 (THead (Flat f) x x0)) \to (land (sn3 c x) (sn3 c x0)))))) (\lambda (t1: 
T).(\lambda (H1: ((\forall (t2: T).((((eq T t1 t2) \to (\forall (P: 
Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c t2)))))).(\lambda (H2: ((\forall 
(t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to 
(\forall (x: T).(\forall (x0: T).((eq T t2 (THead (Flat f) x x0)) \to (land 
(sn3 c x) (sn3 c x0)))))))))).(\lambda (x: T).(\lambda (x0: T).(\lambda (H3: 
(eq T t1 (THead (Flat f) x x0))).(let H4 \def (eq_ind T t1 (\lambda (t0: 
T).(\forall (t2: T).((((eq T t0 t2) \to (\forall (P: Prop).P))) \to ((pr3 c 
t0 t2) \to (\forall (x1: T).(\forall (x2: T).((eq T t2 (THead (Flat f) x1 
x2)) \to (land (sn3 c x1) (sn3 c x2))))))))) H2 (THead (Flat f) x x0) H3) in 
(let H5 \def (eq_ind T t1 (\lambda (t0: T).(\forall (t2: T).((((eq T t0 t2) 
\to (\forall (P: Prop).P))) \to ((pr3 c t0 t2) \to (sn3 c t2))))) H1 (THead 
(Flat f) x x0) H3) in (conj (sn3 c x) (sn3 c x0) (sn3_sing c x (\lambda (t2: 
T).(\lambda (H6: (((eq T x t2) \to (\forall (P: Prop).P)))).(\lambda (H7: 
(pr3 c x t2)).(let H8 \def (H4 (THead (Flat f) t2 x0) (\lambda (H8: (eq T 
(THead (Flat f) x x0) (THead (Flat f) t2 x0))).(\lambda (P: Prop).(let H9 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow x | (TLRef _) \Rightarrow x | (THead _ t0 _) 
\Rightarrow t0])) (THead (Flat f) x x0) (THead (Flat f) t2 x0) H8) in (let 
H10 \def (eq_ind_r T t2 (\lambda (t0: T).(pr3 c x t0)) H7 x H9) in (let H11 
\def (eq_ind_r T t2 (\lambda (t0: T).((eq T x t0) \to (\forall (P0: 
Prop).P0))) H6 x H9) in (H11 (refl_equal T x) P)))))) (pr3_head_12 c x t2 H7 
(Flat f) x0 x0 (pr3_refl (CHead c (Flat f) t2) x0)) t2 x0 (refl_equal T 
(THead (Flat f) t2 x0))) in (land_ind (sn3 c t2) (sn3 c x0) (sn3 c t2) 
(\lambda (H9: (sn3 c t2)).(\lambda (_: (sn3 c x0)).H9)) H8)))))) (sn3_sing c 
x0 (\lambda (t2: T).(\lambda (H6: (((eq T x0 t2) \to (\forall (P: 
Prop).P)))).(\lambda (H7: (pr3 c x0 t2)).(let H8 \def (H4 (THead (Flat f) x 
t2) (\lambda (H8: (eq T (THead (Flat f) x x0) (THead (Flat f) x 
t2))).(\lambda (P: Prop).(let H9 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x0 | (TLRef _) 
\Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) (THead (Flat f) x x0) 
(THead (Flat f) x t2) H8) in (let H10 \def (eq_ind_r T t2 (\lambda (t0: 
T).(pr3 c x0 t0)) H7 x0 H9) in (let H11 \def (eq_ind_r T t2 (\lambda (t0: 
T).((eq T x0 t0) \to (\forall (P0: Prop).P0))) H6 x0 H9) in (H11 (refl_equal 
T x0) P)))))) (pr3_thin_dx c x0 t2 H7 x f) x t2 (refl_equal T (THead (Flat f) 
x t2))) in (land_ind (sn3 c x) (sn3 c t2) (sn3 c t2) (\lambda (_: (sn3 c 
x)).(\lambda (H10: (sn3 c t2)).H10)) H8))))))))))))))) y H0))))) H))))).
(* COMMENTS
Initial nodes: 925
END *)

theorem sn3_gen_head:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).((sn3 c 
(THead k u t)) \to (sn3 c u)))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (c: C).(\forall (u: 
T).(\forall (t: T).((sn3 c (THead k0 u t)) \to (sn3 c u)))))) (\lambda (b: 
B).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: (sn3 c (THead 
(Bind b) u t))).(let H_x \def (sn3_gen_bind b c u t H) in (let H0 \def H_x in 
(land_ind (sn3 c u) (sn3 (CHead c (Bind b) u) t) (sn3 c u) (\lambda (H1: (sn3 
c u)).(\lambda (_: (sn3 (CHead c (Bind b) u) t)).H1)) H0)))))))) (\lambda (f: 
F).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: (sn3 c (THead 
(Flat f) u t))).(let H_x \def (sn3_gen_flat f c u t H) in (let H0 \def H_x in 
(land_ind (sn3 c u) (sn3 c t) (sn3 c u) (\lambda (H1: (sn3 c u)).(\lambda (_: 
(sn3 c t)).H1)) H0)))))))) k).
(* COMMENTS
Initial nodes: 191
END *)

theorem sn3_gen_cflat:
 \forall (f: F).(\forall (c: C).(\forall (u: T).(\forall (t: T).((sn3 (CHead 
c (Flat f) u) t) \to (sn3 c t)))))
\def
 \lambda (f: F).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: 
(sn3 (CHead c (Flat f) u) t)).(sn3_ind (CHead c (Flat f) u) (\lambda (t0: 
T).(sn3 c t0)) (\lambda (t1: T).(\lambda (_: ((\forall (t2: T).((((eq T t1 
t2) \to (\forall (P: Prop).P))) \to ((pr3 (CHead c (Flat f) u) t1 t2) \to 
(sn3 (CHead c (Flat f) u) t2)))))).(\lambda (H1: ((\forall (t2: T).((((eq T 
t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 (CHead c (Flat f) u) t1 t2) \to 
(sn3 c t2)))))).(sn3_sing c t1 (\lambda (t2: T).(\lambda (H2: (((eq T t1 t2) 
\to (\forall (P: Prop).P)))).(\lambda (H3: (pr3 c t1 t2)).(H1 t2 H2 
(pr3_cflat c t1 t2 H3 f u))))))))) t H))))).
(* COMMENTS
Initial nodes: 175
END *)

theorem sn3_gen_lift:
 \forall (c1: C).(\forall (t: T).(\forall (h: nat).(\forall (d: nat).((sn3 c1 
(lift h d t)) \to (\forall (c2: C).((drop h d c1 c2) \to (sn3 c2 t)))))))
\def
 \lambda (c1: C).(\lambda (t: T).(\lambda (h: nat).(\lambda (d: nat).(\lambda 
(H: (sn3 c1 (lift h d t))).(insert_eq T (lift h d t) (\lambda (t0: T).(sn3 c1 
t0)) (\lambda (_: T).(\forall (c2: C).((drop h d c1 c2) \to (sn3 c2 t)))) 
(\lambda (y: T).(\lambda (H0: (sn3 c1 y)).(unintro T t (\lambda (t0: T).((eq 
T y (lift h d t0)) \to (\forall (c2: C).((drop h d c1 c2) \to (sn3 c2 t0))))) 
(sn3_ind c1 (\lambda (t0: T).(\forall (x: T).((eq T t0 (lift h d x)) \to 
(\forall (c2: C).((drop h d c1 c2) \to (sn3 c2 x)))))) (\lambda (t1: 
T).(\lambda (H1: ((\forall (t2: T).((((eq T t1 t2) \to (\forall (P: 
Prop).P))) \to ((pr3 c1 t1 t2) \to (sn3 c1 t2)))))).(\lambda (H2: ((\forall 
(t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c1 t1 t2) \to 
(\forall (x: T).((eq T t2 (lift h d x)) \to (\forall (c2: C).((drop h d c1 
c2) \to (sn3 c2 x)))))))))).(\lambda (x: T).(\lambda (H3: (eq T t1 (lift h d 
x))).(\lambda (c2: C).(\lambda (H4: (drop h d c1 c2)).(let H5 \def (eq_ind T 
t1 (\lambda (t0: T).(\forall (t2: T).((((eq T t0 t2) \to (\forall (P: 
Prop).P))) \to ((pr3 c1 t0 t2) \to (\forall (x0: T).((eq T t2 (lift h d x0)) 
\to (\forall (c3: C).((drop h d c1 c3) \to (sn3 c3 x0))))))))) H2 (lift h d 
x) H3) in (let H6 \def (eq_ind T t1 (\lambda (t0: T).(\forall (t2: T).((((eq 
T t0 t2) \to (\forall (P: Prop).P))) \to ((pr3 c1 t0 t2) \to (sn3 c1 t2))))) 
H1 (lift h d x) H3) in (sn3_sing c2 x (\lambda (t2: T).(\lambda (H7: (((eq T 
x t2) \to (\forall (P: Prop).P)))).(\lambda (H8: (pr3 c2 x t2)).(H5 (lift h d 
t2) (\lambda (H9: (eq T (lift h d x) (lift h d t2))).(\lambda (P: Prop).(let 
H10 \def (eq_ind_r T t2 (\lambda (t0: T).(pr3 c2 x t0)) H8 x (lift_inj x t2 h 
d H9)) in (let H11 \def (eq_ind_r T t2 (\lambda (t0: T).((eq T x t0) \to 
(\forall (P0: Prop).P0))) H7 x (lift_inj x t2 h d H9)) in (H11 (refl_equal T 
x) P))))) (pr3_lift c1 c2 h d H4 x t2 H8) t2 (refl_equal T (lift h d t2)) c2 
H4)))))))))))))) y H0)))) H))))).
(* COMMENTS
Initial nodes: 565
END *)

