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

include "Basic-1/ty3/pr3_props.ma".

include "Basic-1/sty0/fwd.ma".

theorem ty3_sty0:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t1: T).((ty3 g c u 
t1) \to (\forall (t2: T).((sty0 g c u t2) \to (ty3 g c u t2)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda (H: 
(ty3 g c u t1)).(ty3_ind g (\lambda (c0: C).(\lambda (t: T).(\lambda (_: 
T).(\forall (t2: T).((sty0 g c0 t t2) \to (ty3 g c0 t t2)))))) (\lambda (c0: 
C).(\lambda (t2: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 t2 t)).(\lambda 
(_: ((\forall (t3: T).((sty0 g c0 t2 t3) \to (ty3 g c0 t2 t3))))).(\lambda 
(u0: T).(\lambda (t3: T).(\lambda (_: (ty3 g c0 u0 t3)).(\lambda (H3: 
((\forall (t4: T).((sty0 g c0 u0 t4) \to (ty3 g c0 u0 t4))))).(\lambda (_: 
(pc3 c0 t3 t2)).(\lambda (t0: T).(\lambda (H5: (sty0 g c0 u0 t0)).(H3 t0 
H5))))))))))))) (\lambda (c0: C).(\lambda (m: nat).(\lambda (t2: T).(\lambda 
(H0: (sty0 g c0 (TSort m) t2)).(let H_y \def (sty0_gen_sort g c0 t2 m H0) in 
(let H1 \def (f_equal T T (\lambda (e: T).e) t2 (TSort (next g m)) H_y) in 
(eq_ind_r T (TSort (next g m)) (\lambda (t: T).(ty3 g c0 (TSort m) t)) 
(ty3_sort g c0 m) t2 H1))))))) (\lambda (n: nat).(\lambda (c0: C).(\lambda 
(d: C).(\lambda (u0: T).(\lambda (H0: (getl n c0 (CHead d (Bind Abbr) 
u0))).(\lambda (t: T).(\lambda (_: (ty3 g d u0 t)).(\lambda (H2: ((\forall 
(t2: T).((sty0 g d u0 t2) \to (ty3 g d u0 t2))))).(\lambda (t2: T).(\lambda 
(H3: (sty0 g c0 (TLRef n) t2)).(let H_x \def (sty0_gen_lref g c0 t2 n H3) in 
(let H4 \def H_x in (or_ind (ex3_3 C T T (\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abbr) u1))))) (\lambda (e: 
C).(\lambda (u1: T).(\lambda (t0: T).(sty0 g e u1 t0)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (t0: T).(eq T t2 (lift (S n) O t0)))))) (ex3_3 C 
T T (\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(getl n c0 (CHead e 
(Bind Abst) u1))))) (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(sty0 g 
e u1 t0)))) (\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq T t2 (lift 
(S n) O u1)))))) (ty3 g c0 (TLRef n) t2) (\lambda (H5: (ex3_3 C T T (\lambda 
(e: C).(\lambda (u1: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abbr) 
u1))))) (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(sty0 g e u1 t0)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(eq T t2 (lift (S n) O 
t0))))))).(ex3_3_ind C T T (\lambda (e: C).(\lambda (u1: T).(\lambda (_: 
T).(getl n c0 (CHead e (Bind Abbr) u1))))) (\lambda (e: C).(\lambda (u1: 
T).(\lambda (t0: T).(sty0 g e u1 t0)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (t0: T).(eq T t2 (lift (S n) O t0))))) (ty3 g c0 (TLRef n) t2) 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: T).(\lambda (H6: (getl n c0 
(CHead x0 (Bind Abbr) x1))).(\lambda (H7: (sty0 g x0 x1 x2)).(\lambda (H8: 
(eq T t2 (lift (S n) O x2))).(let H9 \def (f_equal T T (\lambda (e: T).e) t2 
(lift (S n) O x2) H8) in (eq_ind_r T (lift (S n) O x2) (\lambda (t0: T).(ty3 
g c0 (TLRef n) t0)) (let H10 \def (eq_ind C (CHead d (Bind Abbr) u0) (\lambda 
(c1: C).(getl n c0 c1)) H0 (CHead x0 (Bind Abbr) x1) (getl_mono c0 (CHead d 
(Bind Abbr) u0) n H0 (CHead x0 (Bind Abbr) x1) H6)) in (let H11 \def (f_equal 
C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow d | (CHead c1 _ _) \Rightarrow c1])) (CHead d (Bind Abbr) u0) 
(CHead x0 (Bind Abbr) x1) (getl_mono c0 (CHead d (Bind Abbr) u0) n H0 (CHead 
x0 (Bind Abbr) x1) H6)) in ((let H12 \def (f_equal C T (\lambda (e: C).(match 
e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | (CHead _ _ 
t0) \Rightarrow t0])) (CHead d (Bind Abbr) u0) (CHead x0 (Bind Abbr) x1) 
(getl_mono c0 (CHead d (Bind Abbr) u0) n H0 (CHead x0 (Bind Abbr) x1) H6)) in 
(\lambda (H13: (eq C d x0)).(let H14 \def (eq_ind_r T x1 (\lambda (t0: 
T).(getl n c0 (CHead x0 (Bind Abbr) t0))) H10 u0 H12) in (let H15 \def 
(eq_ind_r T x1 (\lambda (t0: T).(sty0 g x0 t0 x2)) H7 u0 H12) in (let H16 
\def (eq_ind_r C x0 (\lambda (c1: C).(getl n c0 (CHead c1 (Bind Abbr) u0))) 
H14 d H13) in (let H17 \def (eq_ind_r C x0 (\lambda (c1: C).(sty0 g c1 u0 
x2)) H15 d H13) in (ty3_abbr g n c0 d u0 H16 x2 (H2 x2 H17)))))))) H11))) t2 
H9)))))))) H5)) (\lambda (H5: (ex3_3 C T T (\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u1))))) (\lambda (e: 
C).(\lambda (u1: T).(\lambda (t0: T).(sty0 g e u1 t0)))) (\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq T t2 (lift (S n) O 
u1))))))).(ex3_3_ind C T T (\lambda (e: C).(\lambda (u1: T).(\lambda (_: 
T).(getl n c0 (CHead e (Bind Abst) u1))))) (\lambda (e: C).(\lambda (u1: 
T).(\lambda (t0: T).(sty0 g e u1 t0)))) (\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(eq T t2 (lift (S n) O u1))))) (ty3 g c0 (TLRef n) t2) 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: T).(\lambda (H6: (getl n c0 
(CHead x0 (Bind Abst) x1))).(\lambda (_: (sty0 g x0 x1 x2)).(\lambda (H8: (eq 
T t2 (lift (S n) O x1))).(let H9 \def (f_equal T T (\lambda (e: T).e) t2 
(lift (S n) O x1) H8) in (eq_ind_r T (lift (S n) O x1) (\lambda (t0: T).(ty3 
g c0 (TLRef n) t0)) (let H10 \def (eq_ind C (CHead d (Bind Abbr) u0) (\lambda 
(c1: C).(getl n c0 c1)) H0 (CHead x0 (Bind Abst) x1) (getl_mono c0 (CHead d 
(Bind Abbr) u0) n H0 (CHead x0 (Bind Abst) x1) H6)) in (let H11 \def (eq_ind 
C (CHead d (Bind Abbr) u0) (\lambda (ee: C).(match ee in C return (\lambda 
(_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind b) \Rightarrow (match 
b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow True | Abst 
\Rightarrow False | Void \Rightarrow False]) | (Flat _) \Rightarrow 
False])])) I (CHead x0 (Bind Abst) x1) (getl_mono c0 (CHead d (Bind Abbr) u0) 
n H0 (CHead x0 (Bind Abst) x1) H6)) in (False_ind (ty3 g c0 (TLRef n) (lift 
(S n) O x1)) H11))) t2 H9)))))))) H5)) H4))))))))))))) (\lambda (n: 
nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u0: T).(\lambda (H0: (getl n 
c0 (CHead d (Bind Abst) u0))).(\lambda (t: T).(\lambda (H1: (ty3 g d u0 
t)).(\lambda (_: ((\forall (t2: T).((sty0 g d u0 t2) \to (ty3 g d u0 
t2))))).(\lambda (t2: T).(\lambda (H3: (sty0 g c0 (TLRef n) t2)).(let H_x 
\def (sty0_gen_lref g c0 t2 n H3) in (let H4 \def H_x in (or_ind (ex3_3 C T T 
(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(getl n c0 (CHead e (Bind 
Abbr) u1))))) (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(sty0 g e u1 
t0)))) (\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(eq T t2 (lift (S n) 
O t0)))))) (ex3_3 C T T (\lambda (e: C).(\lambda (u1: T).(\lambda (_: 
T).(getl n c0 (CHead e (Bind Abst) u1))))) (\lambda (e: C).(\lambda (u1: 
T).(\lambda (t0: T).(sty0 g e u1 t0)))) (\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(eq T t2 (lift (S n) O u1)))))) (ty3 g c0 (TLRef n) t2) 
(\lambda (H5: (ex3_3 C T T (\lambda (e: C).(\lambda (u1: T).(\lambda (_: 
T).(getl n c0 (CHead e (Bind Abbr) u1))))) (\lambda (e: C).(\lambda (u1: 
T).(\lambda (t0: T).(sty0 g e u1 t0)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (t0: T).(eq T t2 (lift (S n) O t0))))))).(ex3_3_ind C T T 
(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(getl n c0 (CHead e (Bind 
Abbr) u1))))) (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(sty0 g e u1 
t0)))) (\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(eq T t2 (lift (S n) 
O t0))))) (ty3 g c0 (TLRef n) t2) (\lambda (x0: C).(\lambda (x1: T).(\lambda 
(x2: T).(\lambda (H6: (getl n c0 (CHead x0 (Bind Abbr) x1))).(\lambda (_: 
(sty0 g x0 x1 x2)).(\lambda (H8: (eq T t2 (lift (S n) O x2))).(let H9 \def 
(f_equal T T (\lambda (e: T).e) t2 (lift (S n) O x2) H8) in (eq_ind_r T (lift 
(S n) O x2) (\lambda (t0: T).(ty3 g c0 (TLRef n) t0)) (let H10 \def (eq_ind C 
(CHead d (Bind Abst) u0) (\lambda (c1: C).(getl n c0 c1)) H0 (CHead x0 (Bind 
Abbr) x1) (getl_mono c0 (CHead d (Bind Abst) u0) n H0 (CHead x0 (Bind Abbr) 
x1) H6)) in (let H11 \def (eq_ind C (CHead d (Bind Abst) u0) (\lambda (ee: 
C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow 
False | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) 
with [(Bind b) \Rightarrow (match b in B return (\lambda (_: B).Prop) with 
[Abbr \Rightarrow False | Abst \Rightarrow True | Void \Rightarrow False]) | 
(Flat _) \Rightarrow False])])) I (CHead x0 (Bind Abbr) x1) (getl_mono c0 
(CHead d (Bind Abst) u0) n H0 (CHead x0 (Bind Abbr) x1) H6)) in (False_ind 
(ty3 g c0 (TLRef n) (lift (S n) O x2)) H11))) t2 H9)))))))) H5)) (\lambda 
(H5: (ex3_3 C T T (\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(getl n c0 
(CHead e (Bind Abst) u1))))) (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: 
T).(sty0 g e u1 t0)))) (\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq T 
t2 (lift (S n) O u1))))))).(ex3_3_ind C T T (\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u1))))) (\lambda (e: 
C).(\lambda (u1: T).(\lambda (t0: T).(sty0 g e u1 t0)))) (\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq T t2 (lift (S n) O u1))))) (ty3 g c0 
(TLRef n) t2) (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: T).(\lambda 
(H6: (getl n c0 (CHead x0 (Bind Abst) x1))).(\lambda (H7: (sty0 g x0 x1 
x2)).(\lambda (H8: (eq T t2 (lift (S n) O x1))).(let H9 \def (f_equal T T 
(\lambda (e: T).e) t2 (lift (S n) O x1) H8) in (eq_ind_r T (lift (S n) O x1) 
(\lambda (t0: T).(ty3 g c0 (TLRef n) t0)) (let H10 \def (eq_ind C (CHead d 
(Bind Abst) u0) (\lambda (c1: C).(getl n c0 c1)) H0 (CHead x0 (Bind Abst) x1) 
(getl_mono c0 (CHead d (Bind Abst) u0) n H0 (CHead x0 (Bind Abst) x1) H6)) in 
(let H11 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: 
C).C) with [(CSort _) \Rightarrow d | (CHead c1 _ _) \Rightarrow c1])) (CHead 
d (Bind Abst) u0) (CHead x0 (Bind Abst) x1) (getl_mono c0 (CHead d (Bind 
Abst) u0) n H0 (CHead x0 (Bind Abst) x1) H6)) in ((let H12 \def (f_equal C T 
(\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow u0 | (CHead _ _ t0) \Rightarrow t0])) (CHead d (Bind Abst) u0) 
(CHead x0 (Bind Abst) x1) (getl_mono c0 (CHead d (Bind Abst) u0) n H0 (CHead 
x0 (Bind Abst) x1) H6)) in (\lambda (H13: (eq C d x0)).(let H14 \def 
(eq_ind_r T x1 (\lambda (t0: T).(getl n c0 (CHead x0 (Bind Abst) t0))) H10 u0 
H12) in (let H15 \def (eq_ind_r T x1 (\lambda (t0: T).(sty0 g x0 t0 x2)) H7 
u0 H12) in (eq_ind T u0 (\lambda (t0: T).(ty3 g c0 (TLRef n) (lift (S n) O 
t0))) (let H16 \def (eq_ind_r C x0 (\lambda (c1: C).(getl n c0 (CHead c1 
(Bind Abst) u0))) H14 d H13) in (let H17 \def (eq_ind_r C x0 (\lambda (c1: 
C).(sty0 g c1 u0 x2)) H15 d H13) in (ty3_abst g n c0 d u0 H16 t H1))) x1 
H12))))) H11))) t2 H9)))))))) H5)) H4))))))))))))) (\lambda (c0: C).(\lambda 
(u0: T).(\lambda (t: T).(\lambda (H0: (ty3 g c0 u0 t)).(\lambda (_: ((\forall 
(t2: T).((sty0 g c0 u0 t2) \to (ty3 g c0 u0 t2))))).(\lambda (b: B).(\lambda 
(t2: T).(\lambda (t3: T).(\lambda (_: (ty3 g (CHead c0 (Bind b) u0) t2 
t3)).(\lambda (H3: ((\forall (t4: T).((sty0 g (CHead c0 (Bind b) u0) t2 t4) 
\to (ty3 g (CHead c0 (Bind b) u0) t2 t4))))).(\lambda (t0: T).(\lambda (H4: 
(sty0 g c0 (THead (Bind b) u0 t2) t0)).(let H_x \def (sty0_gen_bind g b c0 u0 
t2 t0 H4) in (let H5 \def H_x in (ex2_ind T (\lambda (t4: T).(sty0 g (CHead 
c0 (Bind b) u0) t2 t4)) (\lambda (t4: T).(eq T t0 (THead (Bind b) u0 t4))) 
(ty3 g c0 (THead (Bind b) u0 t2) t0) (\lambda (x: T).(\lambda (H6: (sty0 g 
(CHead c0 (Bind b) u0) t2 x)).(\lambda (H7: (eq T t0 (THead (Bind b) u0 
x))).(let H8 \def (f_equal T T (\lambda (e: T).e) t0 (THead (Bind b) u0 x) 
H7) in (eq_ind_r T (THead (Bind b) u0 x) (\lambda (t4: T).(ty3 g c0 (THead 
(Bind b) u0 t2) t4)) (ty3_bind g c0 u0 t H0 b t2 x (H3 x H6)) t0 H8))))) 
H5))))))))))))))) (\lambda (c0: C).(\lambda (w: T).(\lambda (u0: T).(\lambda 
(H0: (ty3 g c0 w u0)).(\lambda (_: ((\forall (t2: T).((sty0 g c0 w t2) \to 
(ty3 g c0 w t2))))).(\lambda (v: T).(\lambda (t: T).(\lambda (H2: (ty3 g c0 v 
(THead (Bind Abst) u0 t))).(\lambda (H3: ((\forall (t2: T).((sty0 g c0 v t2) 
\to (ty3 g c0 v t2))))).(\lambda (t2: T).(\lambda (H4: (sty0 g c0 (THead 
(Flat Appl) w v) t2)).(let H_x \def (sty0_gen_appl g c0 w v t2 H4) in (let H5 
\def H_x in (ex2_ind T (\lambda (t3: T).(sty0 g c0 v t3)) (\lambda (t3: 
T).(eq T t2 (THead (Flat Appl) w t3))) (ty3 g c0 (THead (Flat Appl) w v) t2) 
(\lambda (x: T).(\lambda (H6: (sty0 g c0 v x)).(\lambda (H7: (eq T t2 (THead 
(Flat Appl) w x))).(let H8 \def (f_equal T T (\lambda (e: T).e) t2 (THead 
(Flat Appl) w x) H7) in (eq_ind_r T (THead (Flat Appl) w x) (\lambda (t0: 
T).(ty3 g c0 (THead (Flat Appl) w v) t0)) (let H_y \def (H3 x H6) in (let H9 
\def (ty3_unique g c0 v x H_y (THead (Bind Abst) u0 t) H2) in (ex_ind T 
(\lambda (t0: T).(ty3 g c0 x t0)) (ty3 g c0 (THead (Flat Appl) w v) (THead 
(Flat Appl) w x)) (\lambda (x0: T).(\lambda (H10: (ty3 g c0 x x0)).(ex_ind T 
(\lambda (t0: T).(ty3 g c0 u0 t0)) (ty3 g c0 (THead (Flat Appl) w v) (THead 
(Flat Appl) w x)) (\lambda (x1: T).(\lambda (_: (ty3 g c0 u0 x1)).(ex_ind T 
(\lambda (t0: T).(ty3 g c0 (THead (Bind Abst) u0 t) t0)) (ty3 g c0 (THead 
(Flat Appl) w v) (THead (Flat Appl) w x)) (\lambda (x2: T).(\lambda (H12: 
(ty3 g c0 (THead (Bind Abst) u0 t) x2)).(ex3_2_ind T T (\lambda (t3: 
T).(\lambda (_: T).(pc3 c0 (THead (Bind Abst) u0 t3) x2))) (\lambda (_: 
T).(\lambda (t0: T).(ty3 g c0 u0 t0))) (\lambda (t3: T).(\lambda (_: T).(ty3 
g (CHead c0 (Bind Abst) u0) t t3))) (ty3 g c0 (THead (Flat Appl) w v) (THead 
(Flat Appl) w x)) (\lambda (x3: T).(\lambda (x4: T).(\lambda (_: (pc3 c0 
(THead (Bind Abst) u0 x3) x2)).(\lambda (H14: (ty3 g c0 u0 x4)).(\lambda 
(H15: (ty3 g (CHead c0 (Bind Abst) u0) t x3)).(ty3_conv g c0 (THead (Flat 
Appl) w x) (THead (Flat Appl) w (THead (Bind Abst) u0 x3)) (ty3_appl g c0 w 
u0 H0 x x3 (ty3_sconv g c0 x x0 H10 (THead (Bind Abst) u0 t) (THead (Bind 
Abst) u0 x3) (ty3_bind g c0 u0 x4 H14 Abst t x3 H15) H9)) (THead (Flat Appl) 
w v) (THead (Flat Appl) w (THead (Bind Abst) u0 t)) (ty3_appl g c0 w u0 H0 v 
t H2) (pc3_thin_dx c0 (THead (Bind Abst) u0 t) x (ty3_unique g c0 v (THead 
(Bind Abst) u0 t) H2 x H_y) w Appl))))))) (ty3_gen_bind g Abst c0 u0 t x2 
H12)))) (ty3_correct g c0 v (THead (Bind Abst) u0 t) H2)))) (ty3_correct g c0 
w u0 H0)))) (ty3_correct g c0 v x H_y)))) t2 H8))))) H5)))))))))))))) 
(\lambda (c0: C).(\lambda (t2: T).(\lambda (t3: T).(\lambda (H0: (ty3 g c0 t2 
t3)).(\lambda (H1: ((\forall (t4: T).((sty0 g c0 t2 t4) \to (ty3 g c0 t2 
t4))))).(\lambda (t0: T).(\lambda (_: (ty3 g c0 t3 t0)).(\lambda (H3: 
((\forall (t4: T).((sty0 g c0 t3 t4) \to (ty3 g c0 t3 t4))))).(\lambda (t4: 
T).(\lambda (H4: (sty0 g c0 (THead (Flat Cast) t3 t2) t4)).(let H_x \def 
(sty0_gen_cast g c0 t3 t2 t4 H4) in (let H5 \def H_x in (ex3_2_ind T T 
(\lambda (v2: T).(\lambda (_: T).(sty0 g c0 t3 v2))) (\lambda (_: T).(\lambda 
(t5: T).(sty0 g c0 t2 t5))) (\lambda (v2: T).(\lambda (t5: T).(eq T t4 (THead 
(Flat Cast) v2 t5)))) (ty3 g c0 (THead (Flat Cast) t3 t2) t4) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H6: (sty0 g c0 t3 x0)).(\lambda (H7: (sty0 g c0 
t2 x1)).(\lambda (H8: (eq T t4 (THead (Flat Cast) x0 x1))).(let H9 \def 
(f_equal T T (\lambda (e: T).e) t4 (THead (Flat Cast) x0 x1) H8) in (eq_ind_r 
T (THead (Flat Cast) x0 x1) (\lambda (t: T).(ty3 g c0 (THead (Flat Cast) t3 
t2) t)) (let H_y \def (H1 x1 H7) in (let H_y0 \def (H3 x0 H6) in (let H10 
\def (ty3_unique g c0 t2 x1 H_y t3 H0) in (ex_ind T (\lambda (t: T).(ty3 g c0 
x0 t)) (ty3 g c0 (THead (Flat Cast) t3 t2) (THead (Flat Cast) x0 x1)) 
(\lambda (x: T).(\lambda (H11: (ty3 g c0 x0 x)).(ex_ind T (\lambda (t: 
T).(ty3 g c0 x1 t)) (ty3 g c0 (THead (Flat Cast) t3 t2) (THead (Flat Cast) x0 
x1)) (\lambda (x2: T).(\lambda (H12: (ty3 g c0 x1 x2)).(ty3_conv g c0 (THead 
(Flat Cast) x0 x1) (THead (Flat Cast) x x0) (ty3_cast g c0 x1 x0 (ty3_sconv g 
c0 x1 x2 H12 t3 x0 H_y0 H10) x H11) (THead (Flat Cast) t3 t2) (THead (Flat 
Cast) x0 t3) (ty3_cast g c0 t2 t3 H0 x0 H_y0) (pc3_thin_dx c0 t3 x1 
(ty3_unique g c0 t2 t3 H0 x1 H_y) x0 Cast)))) (ty3_correct g c0 t2 x1 H_y)))) 
(ty3_correct g c0 t3 x0 H_y0))))) t4 H9))))))) H5))))))))))))) c u t1 H))))).
(* COMMENTS
Initial nodes: 4539
END *)

