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

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/nf2/props".

include "nf2/defs.ma".

include "pr2/fwd.ma".

theorem nf2_sort:
 \forall (c: C).(\forall (n: nat).(nf2 c (TSort n)))
\def
 \lambda (c: C).(\lambda (n: nat).(\lambda (t2: T).(\lambda (H: (pr2 c (TSort 
n) t2)).(eq_ind_r T (TSort n) (\lambda (t: T).(eq T (TSort n) t)) (refl_equal 
T (TSort n)) t2 (pr2_gen_sort c t2 n H))))).

theorem nf2_abst:
 \forall (c: C).(\forall (u: T).((nf2 c u) \to (\forall (b: B).(\forall (v: 
T).(\forall (t: T).((nf2 (CHead c (Bind b) v) t) \to (nf2 c (THead (Bind 
Abst) u t))))))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (H: ((\forall (t2: T).((pr2 c u t2) 
\to (eq T u t2))))).(\lambda (b: B).(\lambda (v: T).(\lambda (t: T).(\lambda 
(H0: ((\forall (t2: T).((pr2 (CHead c (Bind b) v) t t2) \to (eq T t 
t2))))).(\lambda (t2: T).(\lambda (H1: (pr2 c (THead (Bind Abst) u t) 
t2)).(let H2 \def (pr2_gen_abst c u t t2 H1) in (ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abst) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b0: B).(\forall (u0: T).(pr2 (CHead c (Bind b0) u0) t t3))))) (eq T (THead 
(Bind Abst) u t) t2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H3: (eq T t2 
(THead (Bind Abst) x0 x1))).(\lambda (H4: (pr2 c u x0)).(\lambda (H5: 
((\forall (b0: B).(\forall (u0: T).(pr2 (CHead c (Bind b0) u0) t 
x1))))).(eq_ind_r T (THead (Bind Abst) x0 x1) (\lambda (t0: T).(eq T (THead 
(Bind Abst) u t) t0)) (f_equal3 K T T T THead (Bind Abst) (Bind Abst) u x0 t 
x1 (refl_equal K (Bind Abst)) (H x0 H4) (H0 x1 (H5 b v))) t2 H3)))))) 
H2)))))))))).

theorem nf2_appl_lref:
 \forall (c: C).(\forall (u: T).((nf2 c u) \to (\forall (i: nat).((nf2 c 
(TLRef i)) \to (nf2 c (THead (Flat Appl) u (TLRef i)))))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (H: ((\forall (t2: T).((pr2 c u t2) 
\to (eq T u t2))))).(\lambda (i: nat).(\lambda (H0: ((\forall (t2: T).((pr2 c 
(TLRef i) t2) \to (eq T (TLRef i) t2))))).(\lambda (t2: T).(\lambda (H1: (pr2 
c (THead (Flat Appl) u (TLRef i)) t2)).(let H2 \def (pr2_gen_appl c u (TLRef 
i) t2 H1) in (or3_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 
(THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c (TLRef i) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(TLRef i) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 t3)))))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T (TLRef i) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq 
T t2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 z2)))))))) 
(eq T (THead (Flat Appl) u (TLRef i)) t2) (\lambda (H3: (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c 
(TLRef i) t3))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 
(THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c u u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr2 c (TLRef i) t3))) (eq T (THead (Flat 
Appl) u (TLRef i)) t2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H4: (eq T 
t2 (THead (Flat Appl) x0 x1))).(\lambda (H5: (pr2 c u x0)).(\lambda (H6: (pr2 
c (TLRef i) x1)).(eq_ind_r T (THead (Flat Appl) x0 x1) (\lambda (t: T).(eq T 
(THead (Flat Appl) u (TLRef i)) t)) (let H7 \def (eq_ind_r T x1 (\lambda (t: 
T).(pr2 c (TLRef i) t)) H6 (TLRef i) (H0 x1 H6)) in (eq_ind T (TLRef i) 
(\lambda (t: T).(eq T (THead (Flat Appl) u (TLRef i)) (THead (Flat Appl) x0 
t))) (let H8 \def (eq_ind_r T x0 (\lambda (t: T).(pr2 c u t)) H5 u (H x0 H5)) 
in (eq_ind T u (\lambda (t: T).(eq T (THead (Flat Appl) u (TLRef i)) (THead 
(Flat Appl) t (TLRef i)))) (refl_equal T (THead (Flat Appl) u (TLRef i))) x0 
(H x0 H5))) x1 (H0 x1 H6))) t2 H4)))))) H3)) (\lambda (H3: (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(TLRef i) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) z1 
t3))))))))).(ex4_4_ind T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (TLRef i) (THead (Bind Abst) y1 z1)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c (Bind 
b) u0) z1 t3))))))) (eq T (THead (Flat Appl) u (TLRef i)) t2) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H4: (eq T 
(TLRef i) (THead (Bind Abst) x0 x1))).(\lambda (H5: (eq T t2 (THead (Bind 
Abbr) x2 x3))).(\lambda (_: (pr2 c u x2)).(\lambda (_: ((\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c (Bind b) u0) x1 x3))))).(eq_ind_r T (THead 
(Bind Abbr) x2 x3) (\lambda (t: T).(eq T (THead (Flat Appl) u (TLRef i)) t)) 
(let H8 \def (eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead (Bind Abst) x0 
x1) H4) in (False_ind (eq T (THead (Flat Appl) u (TLRef i)) (THead (Bind 
Abbr) x2 x3)) H8)) t2 H5))))))))) H3)) (\lambda (H3: (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(TLRef i) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T 
t2 (THead (Bind b) y2 (THead (Flat Appl) (lift (S O) O u2) z2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c u u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 (CHead c (Bind b) y2) z1 
z2))))))))).(ex6_6_ind B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b 
Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (TLRef i) (THead (Bind b) y1 
z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: 
T).(\lambda (u2: T).(\lambda (y2: T).(eq T t2 (THead (Bind b) y2 (THead (Flat 
Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c u u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(pr2 
(CHead c (Bind b) y2) z1 z2))))))) (eq T (THead (Flat Appl) u (TLRef i)) t2) 
(\lambda (x0: B).(\lambda (x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda 
(x4: T).(\lambda (x5: T).(\lambda (_: (not (eq B x0 Abst))).(\lambda (H5: (eq 
T (TLRef i) (THead (Bind x0) x1 x2))).(\lambda (H6: (eq T t2 (THead (Bind x0) 
x5 (THead (Flat Appl) (lift (S O) O x4) x3)))).(\lambda (_: (pr2 c u 
x4)).(\lambda (_: (pr2 c x1 x5)).(\lambda (_: (pr2 (CHead c (Bind x0) x5) x2 
x3)).(eq_ind_r T (THead (Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) 
x3)) (\lambda (t: T).(eq T (THead (Flat Appl) u (TLRef i)) t)) (let H10 \def 
(eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (THead (Bind x0) x1 x2) H5) in 
(False_ind (eq T (THead (Flat Appl) u (TLRef i)) (THead (Bind x0) x5 (THead 
(Flat Appl) (lift (S O) O x4) x3))) H10)) t2 H6))))))))))))) H3)) H2)))))))).

theorem nf2_lref_abst:
 \forall (c: C).(\forall (e: C).(\forall (u: T).(\forall (i: nat).((getl i c 
(CHead e (Bind Abst) u)) \to (nf2 c (TLRef i))))))
\def
 \lambda (c: C).(\lambda (e: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead e (Bind Abst) u))).(\lambda (t2: T).(\lambda (H0: (pr2 c 
(TLRef i) t2)).(let H1 \def (pr2_gen_lref c t2 i H0) in (or_ind (eq T t2 
(TLRef i)) (ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i c (CHead d 
(Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(eq T t2 (lift (S i) O 
u0))))) (eq T (TLRef i) t2) (\lambda (H2: (eq T t2 (TLRef i))).(eq_ind_r T 
(TLRef i) (\lambda (t: T).(eq T (TLRef i) t)) (refl_equal T (TLRef i)) t2 
H2)) (\lambda (H2: (ex2_2 C T (\lambda (d: C).(\lambda (u0: T).(getl i c 
(CHead d (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(eq T t2 (lift 
(S i) O u0)))))).(ex2_2_ind C T (\lambda (d: C).(\lambda (u0: T).(getl i c 
(CHead d (Bind Abbr) u0)))) (\lambda (_: C).(\lambda (u0: T).(eq T t2 (lift 
(S i) O u0)))) (eq T (TLRef i) t2) (\lambda (x0: C).(\lambda (x1: T).(\lambda 
(H3: (getl i c (CHead x0 (Bind Abbr) x1))).(\lambda (H4: (eq T t2 (lift (S i) 
O x1))).(eq_ind_r T (lift (S i) O x1) (\lambda (t: T).(eq T (TLRef i) t)) 
(let H5 \def (eq_ind C (CHead e (Bind Abst) u) (\lambda (c0: C).(getl i c 
c0)) H (CHead x0 (Bind Abbr) x1) (getl_mono c (CHead e (Bind Abst) u) i H 
(CHead x0 (Bind Abbr) x1) H3)) in (let H6 \def (eq_ind C (CHead e (Bind Abst) 
u) (\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort 
_) \Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind b) \Rightarrow (match b in B return 
(\lambda (_: B).Prop) with [Abbr \Rightarrow False | Abst \Rightarrow True | 
Void \Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead x0 (Bind 
Abbr) x1) (getl_mono c (CHead e (Bind Abst) u) i H (CHead x0 (Bind Abbr) x1) 
H3)) in (False_ind (eq T (TLRef i) (lift (S i) O x1)) H6))) t2 H4))))) H2)) 
H1)))))))).

theorem nf2_lift:
 \forall (d: C).(\forall (t: T).((nf2 d t) \to (\forall (c: C).(\forall (h: 
nat).(\forall (i: nat).((drop h i c d) \to (nf2 c (lift h i t))))))))
\def
 \lambda (d: C).(\lambda (t: T).(\lambda (H: ((\forall (t2: T).((pr2 d t t2) 
\to (eq T t t2))))).(\lambda (c: C).(\lambda (h: nat).(\lambda (i: 
nat).(\lambda (H0: (drop h i c d)).(\lambda (t2: T).(\lambda (H1: (pr2 c 
(lift h i t) t2)).(let H2 \def (pr2_gen_lift c t t2 h i H1 d H0) in (ex2_ind 
T (\lambda (t3: T).(eq T t2 (lift h i t3))) (\lambda (t3: T).(pr2 d t t3)) 
(eq T (lift h i t) t2) (\lambda (x: T).(\lambda (H3: (eq T t2 (lift h i 
x))).(\lambda (H4: (pr2 d t x)).(eq_ind_r T (lift h i x) (\lambda (t0: T).(eq 
T (lift h i t) t0)) (let H_y \def (H x H4) in (let H5 \def (eq_ind_r T x 
(\lambda (t0: T).(pr2 d t t0)) H4 t H_y) in (eq_ind T t (\lambda (t0: T).(eq 
T (lift h i t) (lift h i t0))) (refl_equal T (lift h i t)) x H_y))) t2 H3)))) 
H2)))))))))).

