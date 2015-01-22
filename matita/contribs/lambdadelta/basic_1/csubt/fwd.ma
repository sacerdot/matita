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

include "Basic-1/csubt/defs.ma".

theorem csubt_gen_abbr:
 \forall (g: G).(\forall (e1: C).(\forall (c2: C).(\forall (v: T).((csubt g 
(CHead e1 (Bind Abbr) v) c2) \to (ex2 C (\lambda (e2: C).(eq C c2 (CHead e2 
(Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 e2)))))))
\def
 \lambda (g: G).(\lambda (e1: C).(\lambda (c2: C).(\lambda (v: T).(\lambda 
(H: (csubt g (CHead e1 (Bind Abbr) v) c2)).(insert_eq C (CHead e1 (Bind Abbr) 
v) (\lambda (c: C).(csubt g c c2)) (\lambda (_: C).(ex2 C (\lambda (e2: 
C).(eq C c2 (CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 e2)))) 
(\lambda (y: C).(\lambda (H0: (csubt g y c2)).(csubt_ind g (\lambda (c: 
C).(\lambda (c0: C).((eq C c (CHead e1 (Bind Abbr) v)) \to (ex2 C (\lambda 
(e2: C).(eq C c0 (CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 
e2)))))) (\lambda (n: nat).(\lambda (H1: (eq C (CSort n) (CHead e1 (Bind 
Abbr) v))).(let H2 \def (eq_ind C (CSort n) (\lambda (ee: C).(match ee in C 
return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) 
\Rightarrow False])) I (CHead e1 (Bind Abbr) v) H1) in (False_ind (ex2 C 
(\lambda (e2: C).(eq C (CSort n) (CHead e2 (Bind Abbr) v))) (\lambda (e2: 
C).(csubt g e1 e2))) H2)))) (\lambda (c1: C).(\lambda (c3: C).(\lambda (H1: 
(csubt g c1 c3)).(\lambda (H2: (((eq C c1 (CHead e1 (Bind Abbr) v)) \to (ex2 
C (\lambda (e2: C).(eq C c3 (CHead e2 (Bind Abbr) v))) (\lambda (e2: 
C).(csubt g e1 e2)))))).(\lambda (k: K).(\lambda (u: T).(\lambda (H3: (eq C 
(CHead c1 k u) (CHead e1 (Bind Abbr) v))).(let H4 \def (f_equal C C (\lambda 
(e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c1 
| (CHead c _ _) \Rightarrow c])) (CHead c1 k u) (CHead e1 (Bind Abbr) v) H3) 
in ((let H5 \def (f_equal C K (\lambda (e: C).(match e in C return (\lambda 
(_: C).K) with [(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) 
(CHead c1 k u) (CHead e1 (Bind Abbr) v) H3) in ((let H6 \def (f_equal C T 
(\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead c1 k u) (CHead e1 (Bind 
Abbr) v) H3) in (\lambda (H7: (eq K k (Bind Abbr))).(\lambda (H8: (eq C c1 
e1)).(eq_ind_r T v (\lambda (t: T).(ex2 C (\lambda (e2: C).(eq C (CHead c3 k 
t) (CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 e2)))) (eq_ind_r K 
(Bind Abbr) (\lambda (k0: K).(ex2 C (\lambda (e2: C).(eq C (CHead c3 k0 v) 
(CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 e2)))) (let H9 \def 
(eq_ind C c1 (\lambda (c: C).((eq C c (CHead e1 (Bind Abbr) v)) \to (ex2 C 
(\lambda (e2: C).(eq C c3 (CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csubt 
g e1 e2))))) H2 e1 H8) in (let H10 \def (eq_ind C c1 (\lambda (c: C).(csubt g 
c c3)) H1 e1 H8) in (ex_intro2 C (\lambda (e2: C).(eq C (CHead c3 (Bind Abbr) 
v) (CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 e2)) c3 
(refl_equal C (CHead c3 (Bind Abbr) v)) H10))) k H7) u H6)))) H5)) 
H4))))))))) (\lambda (c1: C).(\lambda (c3: C).(\lambda (_: (csubt g c1 
c3)).(\lambda (_: (((eq C c1 (CHead e1 (Bind Abbr) v)) \to (ex2 C (\lambda 
(e2: C).(eq C c3 (CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 
e2)))))).(\lambda (b: B).(\lambda (_: (not (eq B b Void))).(\lambda (u1: 
T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead c1 (Bind Void) u1) (CHead e1 
(Bind Abbr) v))).(let H5 \def (eq_ind C (CHead c1 (Bind Void) u1) (\lambda 
(ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b0) \Rightarrow (match b0 in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow False | Abst \Rightarrow False | Void 
\Rightarrow True]) | (Flat _) \Rightarrow False])])) I (CHead e1 (Bind Abbr) 
v) H4) in (False_ind (ex2 C (\lambda (e2: C).(eq C (CHead c3 (Bind b) u2) 
(CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 e2))) H5))))))))))) 
(\lambda (c1: C).(\lambda (c3: C).(\lambda (_: (csubt g c1 c3)).(\lambda (_: 
(((eq C c1 (CHead e1 (Bind Abbr) v)) \to (ex2 C (\lambda (e2: C).(eq C c3 
(CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 e2)))))).(\lambda (u: 
T).(\lambda (t: T).(\lambda (_: (ty3 g c1 u t)).(\lambda (_: (ty3 g c3 u 
t)).(\lambda (H5: (eq C (CHead c1 (Bind Abst) t) (CHead e1 (Bind Abbr) 
v))).(let H6 \def (eq_ind C (CHead c1 (Bind Abst) t) (\lambda (ee: C).(match 
ee in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | 
(CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind b) \Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr 
\Rightarrow False | Abst \Rightarrow True | Void \Rightarrow False]) | (Flat 
_) \Rightarrow False])])) I (CHead e1 (Bind Abbr) v) H5) in (False_ind (ex2 C 
(\lambda (e2: C).(eq C (CHead c3 (Bind Abbr) u) (CHead e2 (Bind Abbr) v))) 
(\lambda (e2: C).(csubt g e1 e2))) H6))))))))))) y c2 H0))) H))))).
(* COMMENTS
Initial nodes: 1111
END *)

theorem csubt_gen_abst:
 \forall (g: G).(\forall (e1: C).(\forall (c2: C).(\forall (v1: T).((csubt g 
(CHead e1 (Bind Abst) v1) c2) \to (or (ex2 C (\lambda (e2: C).(eq C c2 (CHead 
e2 (Bind Abst) v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex4_2 C T (\lambda 
(e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (_: C).(\lambda (v2: T).(ty3 g 
e1 v2 v1))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1)))))))))
\def
 \lambda (g: G).(\lambda (e1: C).(\lambda (c2: C).(\lambda (v1: T).(\lambda 
(H: (csubt g (CHead e1 (Bind Abst) v1) c2)).(insert_eq C (CHead e1 (Bind 
Abst) v1) (\lambda (c: C).(csubt g c c2)) (\lambda (_: C).(or (ex2 C (\lambda 
(e2: C).(eq C c2 (CHead e2 (Bind Abst) v1))) (\lambda (e2: C).(csubt g e1 
e2))) (ex4_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind 
Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (_: 
C).(\lambda (v2: T).(ty3 g e1 v2 v1))) (\lambda (e2: C).(\lambda (v2: T).(ty3 
g e2 v2 v1)))))) (\lambda (y: C).(\lambda (H0: (csubt g y c2)).(csubt_ind g 
(\lambda (c: C).(\lambda (c0: C).((eq C c (CHead e1 (Bind Abst) v1)) \to (or 
(ex2 C (\lambda (e2: C).(eq C c0 (CHead e2 (Bind Abst) v1))) (\lambda (e2: 
C).(csubt g e1 e2))) (ex4_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C c0 
(CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csubt g e1 
e2))) (\lambda (_: C).(\lambda (v2: T).(ty3 g e1 v2 v1))) (\lambda (e2: 
C).(\lambda (v2: T).(ty3 g e2 v2 v1)))))))) (\lambda (n: nat).(\lambda (H1: 
(eq C (CSort n) (CHead e1 (Bind Abst) v1))).(let H2 \def (eq_ind C (CSort n) 
(\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow True | (CHead _ _ _) \Rightarrow False])) I (CHead e1 (Bind Abst) 
v1) H1) in (False_ind (or (ex2 C (\lambda (e2: C).(eq C (CSort n) (CHead e2 
(Bind Abst) v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex4_2 C T (\lambda (e2: 
C).(\lambda (v2: T).(eq C (CSort n) (CHead e2 (Bind Abbr) v2)))) (\lambda 
(e2: C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (_: C).(\lambda (v2: 
T).(ty3 g e1 v2 v1))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1))))) 
H2)))) (\lambda (c1: C).(\lambda (c3: C).(\lambda (H1: (csubt g c1 
c3)).(\lambda (H2: (((eq C c1 (CHead e1 (Bind Abst) v1)) \to (or (ex2 C 
(\lambda (e2: C).(eq C c3 (CHead e2 (Bind Abst) v1))) (\lambda (e2: C).(csubt 
g e1 e2))) (ex4_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C c3 (CHead e2 
(Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2))) 
(\lambda (_: C).(\lambda (v2: T).(ty3 g e1 v2 v1))) (\lambda (e2: C).(\lambda 
(v2: T).(ty3 g e2 v2 v1)))))))).(\lambda (k: K).(\lambda (u: T).(\lambda (H3: 
(eq C (CHead c1 k u) (CHead e1 (Bind Abst) v1))).(let H4 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow c1 | (CHead c _ _) \Rightarrow c])) (CHead c1 k u) (CHead e1 
(Bind Abst) v1) H3) in ((let H5 \def (f_equal C K (\lambda (e: C).(match e in 
C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k | (CHead _ k0 _) 
\Rightarrow k0])) (CHead c1 k u) (CHead e1 (Bind Abst) v1) H3) in ((let H6 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead c1 k u) 
(CHead e1 (Bind Abst) v1) H3) in (\lambda (H7: (eq K k (Bind Abst))).(\lambda 
(H8: (eq C c1 e1)).(eq_ind_r T v1 (\lambda (t: T).(or (ex2 C (\lambda (e2: 
C).(eq C (CHead c3 k t) (CHead e2 (Bind Abst) v1))) (\lambda (e2: C).(csubt g 
e1 e2))) (ex4_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c3 k t) 
(CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csubt g e1 
e2))) (\lambda (_: C).(\lambda (v2: T).(ty3 g e1 v2 v1))) (\lambda (e2: 
C).(\lambda (v2: T).(ty3 g e2 v2 v1)))))) (eq_ind_r K (Bind Abst) (\lambda 
(k0: K).(or (ex2 C (\lambda (e2: C).(eq C (CHead c3 k0 v1) (CHead e2 (Bind 
Abst) v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex4_2 C T (\lambda (e2: 
C).(\lambda (v2: T).(eq C (CHead c3 k0 v1) (CHead e2 (Bind Abbr) v2)))) 
(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (_: C).(\lambda 
(v2: T).(ty3 g e1 v2 v1))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 
v1)))))) (let H9 \def (eq_ind C c1 (\lambda (c: C).((eq C c (CHead e1 (Bind 
Abst) v1)) \to (or (ex2 C (\lambda (e2: C).(eq C c3 (CHead e2 (Bind Abst) 
v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex4_2 C T (\lambda (e2: C).(\lambda 
(v2: T).(eq C c3 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: 
T).(csubt g e1 e2))) (\lambda (_: C).(\lambda (v2: T).(ty3 g e1 v2 v1))) 
(\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1))))))) H2 e1 H8) in (let 
H10 \def (eq_ind C c1 (\lambda (c: C).(csubt g c c3)) H1 e1 H8) in (or_introl 
(ex2 C (\lambda (e2: C).(eq C (CHead c3 (Bind Abst) v1) (CHead e2 (Bind Abst) 
v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex4_2 C T (\lambda (e2: C).(\lambda 
(v2: T).(eq C (CHead c3 (Bind Abst) v1) (CHead e2 (Bind Abbr) v2)))) (\lambda 
(e2: C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (_: C).(\lambda (v2: 
T).(ty3 g e1 v2 v1))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1)))) 
(ex_intro2 C (\lambda (e2: C).(eq C (CHead c3 (Bind Abst) v1) (CHead e2 (Bind 
Abst) v1))) (\lambda (e2: C).(csubt g e1 e2)) c3 (refl_equal C (CHead c3 
(Bind Abst) v1)) H10)))) k H7) u H6)))) H5)) H4))))))))) (\lambda (c1: 
C).(\lambda (c3: C).(\lambda (_: (csubt g c1 c3)).(\lambda (_: (((eq C c1 
(CHead e1 (Bind Abst) v1)) \to (or (ex2 C (\lambda (e2: C).(eq C c3 (CHead e2 
(Bind Abst) v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex4_2 C T (\lambda (e2: 
C).(\lambda (v2: T).(eq C c3 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (_: C).(\lambda (v2: T).(ty3 g 
e1 v2 v1))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 
v1)))))))).(\lambda (b: B).(\lambda (_: (not (eq B b Void))).(\lambda (u1: 
T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead c1 (Bind Void) u1) (CHead e1 
(Bind Abst) v1))).(let H5 \def (eq_ind C (CHead c1 (Bind Void) u1) (\lambda 
(ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b0) \Rightarrow (match b0 in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow False | Abst \Rightarrow False | Void 
\Rightarrow True]) | (Flat _) \Rightarrow False])])) I (CHead e1 (Bind Abst) 
v1) H4) in (False_ind (or (ex2 C (\lambda (e2: C).(eq C (CHead c3 (Bind b) 
u2) (CHead e2 (Bind Abst) v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex4_2 C T 
(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c3 (Bind b) u2) (CHead e2 
(Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2))) 
(\lambda (_: C).(\lambda (v2: T).(ty3 g e1 v2 v1))) (\lambda (e2: C).(\lambda 
(v2: T).(ty3 g e2 v2 v1))))) H5))))))))))) (\lambda (c1: C).(\lambda (c3: 
C).(\lambda (H1: (csubt g c1 c3)).(\lambda (H2: (((eq C c1 (CHead e1 (Bind 
Abst) v1)) \to (or (ex2 C (\lambda (e2: C).(eq C c3 (CHead e2 (Bind Abst) 
v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex4_2 C T (\lambda (e2: C).(\lambda 
(v2: T).(eq C c3 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: 
T).(csubt g e1 e2))) (\lambda (_: C).(\lambda (v2: T).(ty3 g e1 v2 v1))) 
(\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1)))))))).(\lambda (u: 
T).(\lambda (t: T).(\lambda (H3: (ty3 g c1 u t)).(\lambda (H4: (ty3 g c3 u 
t)).(\lambda (H5: (eq C (CHead c1 (Bind Abst) t) (CHead e1 (Bind Abst) 
v1))).(let H6 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) 
(CHead c1 (Bind Abst) t) (CHead e1 (Bind Abst) v1) H5) in ((let H7 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow t | (CHead _ _ t0) \Rightarrow t0])) (CHead c1 (Bind 
Abst) t) (CHead e1 (Bind Abst) v1) H5) in (\lambda (H8: (eq C c1 e1)).(let H9 
\def (eq_ind T t (\lambda (t0: T).(ty3 g c3 u t0)) H4 v1 H7) in (let H10 \def 
(eq_ind T t (\lambda (t0: T).(ty3 g c1 u t0)) H3 v1 H7) in (let H11 \def 
(eq_ind C c1 (\lambda (c: C).(ty3 g c u v1)) H10 e1 H8) in (let H12 \def 
(eq_ind C c1 (\lambda (c: C).((eq C c (CHead e1 (Bind Abst) v1)) \to (or (ex2 
C (\lambda (e2: C).(eq C c3 (CHead e2 (Bind Abst) v1))) (\lambda (e2: 
C).(csubt g e1 e2))) (ex4_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C c3 
(CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csubt g e1 
e2))) (\lambda (_: C).(\lambda (v2: T).(ty3 g e1 v2 v1))) (\lambda (e2: 
C).(\lambda (v2: T).(ty3 g e2 v2 v1))))))) H2 e1 H8) in (let H13 \def (eq_ind 
C c1 (\lambda (c: C).(csubt g c c3)) H1 e1 H8) in (or_intror (ex2 C (\lambda 
(e2: C).(eq C (CHead c3 (Bind Abbr) u) (CHead e2 (Bind Abst) v1))) (\lambda 
(e2: C).(csubt g e1 e2))) (ex4_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C 
(CHead c3 (Bind Abbr) u) (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (_: C).(\lambda (v2: T).(ty3 g 
e1 v2 v1))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1)))) 
(ex4_2_intro C T (\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c3 (Bind 
Abbr) u) (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csubt 
g e1 e2))) (\lambda (_: C).(\lambda (v2: T).(ty3 g e1 v2 v1))) (\lambda (e2: 
C).(\lambda (v2: T).(ty3 g e2 v2 v1))) c3 u (refl_equal C (CHead c3 (Bind 
Abbr) u)) H13 H11 H9))))))))) H6))))))))))) y c2 H0))) H))))).
(* COMMENTS
Initial nodes: 2362
END *)

theorem csubt_gen_flat:
 \forall (g: G).(\forall (e1: C).(\forall (c2: C).(\forall (v: T).(\forall 
(f: F).((csubt g (CHead e1 (Flat f) v) c2) \to (ex2 C (\lambda (e2: C).(eq C 
c2 (CHead e2 (Flat f) v))) (\lambda (e2: C).(csubt g e1 e2))))))))
\def
 \lambda (g: G).(\lambda (e1: C).(\lambda (c2: C).(\lambda (v: T).(\lambda 
(f: F).(\lambda (H: (csubt g (CHead e1 (Flat f) v) c2)).(insert_eq C (CHead 
e1 (Flat f) v) (\lambda (c: C).(csubt g c c2)) (\lambda (_: C).(ex2 C 
(\lambda (e2: C).(eq C c2 (CHead e2 (Flat f) v))) (\lambda (e2: C).(csubt g 
e1 e2)))) (\lambda (y: C).(\lambda (H0: (csubt g y c2)).(csubt_ind g (\lambda 
(c: C).(\lambda (c0: C).((eq C c (CHead e1 (Flat f) v)) \to (ex2 C (\lambda 
(e2: C).(eq C c0 (CHead e2 (Flat f) v))) (\lambda (e2: C).(csubt g e1 
e2)))))) (\lambda (n: nat).(\lambda (H1: (eq C (CSort n) (CHead e1 (Flat f) 
v))).(let H2 \def (eq_ind C (CSort n) (\lambda (ee: C).(match ee in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) 
\Rightarrow False])) I (CHead e1 (Flat f) v) H1) in (False_ind (ex2 C 
(\lambda (e2: C).(eq C (CSort n) (CHead e2 (Flat f) v))) (\lambda (e2: 
C).(csubt g e1 e2))) H2)))) (\lambda (c1: C).(\lambda (c3: C).(\lambda (H1: 
(csubt g c1 c3)).(\lambda (H2: (((eq C c1 (CHead e1 (Flat f) v)) \to (ex2 C 
(\lambda (e2: C).(eq C c3 (CHead e2 (Flat f) v))) (\lambda (e2: C).(csubt g 
e1 e2)))))).(\lambda (k: K).(\lambda (u: T).(\lambda (H3: (eq C (CHead c1 k 
u) (CHead e1 (Flat f) v))).(let H4 \def (f_equal C C (\lambda (e: C).(match e 
in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c1 | (CHead c _ _) 
\Rightarrow c])) (CHead c1 k u) (CHead e1 (Flat f) v) H3) in ((let H5 \def 
(f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) with 
[(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) (CHead c1 k u) 
(CHead e1 (Flat f) v) H3) in ((let H6 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | 
(CHead _ _ t) \Rightarrow t])) (CHead c1 k u) (CHead e1 (Flat f) v) H3) in 
(\lambda (H7: (eq K k (Flat f))).(\lambda (H8: (eq C c1 e1)).(eq_ind_r T v 
(\lambda (t: T).(ex2 C (\lambda (e2: C).(eq C (CHead c3 k t) (CHead e2 (Flat 
f) v))) (\lambda (e2: C).(csubt g e1 e2)))) (eq_ind_r K (Flat f) (\lambda 
(k0: K).(ex2 C (\lambda (e2: C).(eq C (CHead c3 k0 v) (CHead e2 (Flat f) v))) 
(\lambda (e2: C).(csubt g e1 e2)))) (let H9 \def (eq_ind C c1 (\lambda (c: 
C).((eq C c (CHead e1 (Flat f) v)) \to (ex2 C (\lambda (e2: C).(eq C c3 
(CHead e2 (Flat f) v))) (\lambda (e2: C).(csubt g e1 e2))))) H2 e1 H8) in 
(let H10 \def (eq_ind C c1 (\lambda (c: C).(csubt g c c3)) H1 e1 H8) in 
(ex_intro2 C (\lambda (e2: C).(eq C (CHead c3 (Flat f) v) (CHead e2 (Flat f) 
v))) (\lambda (e2: C).(csubt g e1 e2)) c3 (refl_equal C (CHead c3 (Flat f) 
v)) H10))) k H7) u H6)))) H5)) H4))))))))) (\lambda (c1: C).(\lambda (c3: 
C).(\lambda (_: (csubt g c1 c3)).(\lambda (_: (((eq C c1 (CHead e1 (Flat f) 
v)) \to (ex2 C (\lambda (e2: C).(eq C c3 (CHead e2 (Flat f) v))) (\lambda 
(e2: C).(csubt g e1 e2)))))).(\lambda (b: B).(\lambda (_: (not (eq B b 
Void))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead c1 (Bind 
Void) u1) (CHead e1 (Flat f) v))).(let H5 \def (eq_ind C (CHead c1 (Bind 
Void) u1) (\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with 
[(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow 
False])])) I (CHead e1 (Flat f) v) H4) in (False_ind (ex2 C (\lambda (e2: 
C).(eq C (CHead c3 (Bind b) u2) (CHead e2 (Flat f) v))) (\lambda (e2: 
C).(csubt g e1 e2))) H5))))))))))) (\lambda (c1: C).(\lambda (c3: C).(\lambda 
(_: (csubt g c1 c3)).(\lambda (_: (((eq C c1 (CHead e1 (Flat f) v)) \to (ex2 
C (\lambda (e2: C).(eq C c3 (CHead e2 (Flat f) v))) (\lambda (e2: C).(csubt g 
e1 e2)))))).(\lambda (u: T).(\lambda (t: T).(\lambda (_: (ty3 g c1 u 
t)).(\lambda (_: (ty3 g c3 u t)).(\lambda (H5: (eq C (CHead c1 (Bind Abst) t) 
(CHead e1 (Flat f) v))).(let H6 \def (eq_ind C (CHead c1 (Bind Abst) t) 
(\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow 
False])])) I (CHead e1 (Flat f) v) H5) in (False_ind (ex2 C (\lambda (e2: 
C).(eq C (CHead c3 (Bind Abbr) u) (CHead e2 (Flat f) v))) (\lambda (e2: 
C).(csubt g e1 e2))) H6))))))))))) y c2 H0))) H)))))).
(* COMMENTS
Initial nodes: 1103
END *)

theorem csubt_gen_bind:
 \forall (g: G).(\forall (b1: B).(\forall (e1: C).(\forall (c2: C).(\forall 
(v1: T).((csubt g (CHead e1 (Bind b1) v1) c2) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2))))))))))
\def
 \lambda (g: G).(\lambda (b1: B).(\lambda (e1: C).(\lambda (c2: C).(\lambda 
(v1: T).(\lambda (H: (csubt g (CHead e1 (Bind b1) v1) c2)).(insert_eq C 
(CHead e1 (Bind b1) v1) (\lambda (c: C).(csubt g c c2)) (\lambda (_: 
C).(ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csubt g e1 e2)))))) (\lambda (y: C).(\lambda (H0: (csubt g y 
c2)).(csubt_ind g (\lambda (c: C).(\lambda (c0: C).((eq C c (CHead e1 (Bind 
b1) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: 
T).(eq C c0 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2)))))))) (\lambda (n: nat).(\lambda (H1: (eq 
C (CSort n) (CHead e1 (Bind b1) v1))).(let H2 \def (eq_ind C (CSort n) 
(\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow True | (CHead _ _ _) \Rightarrow False])) I (CHead e1 (Bind b1) 
v1) H1) in (False_ind (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda 
(v2: T).(eq C (CSort n) (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda 
(e2: C).(\lambda (_: T).(csubt g e1 e2))))) H2)))) (\lambda (c1: C).(\lambda 
(c3: C).(\lambda (H1: (csubt g c1 c3)).(\lambda (H2: (((eq C c1 (CHead e1 
(Bind b1) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda 
(v2: T).(eq C c3 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2)))))))).(\lambda (k: K).(\lambda (u: 
T).(\lambda (H3: (eq C (CHead c1 k u) (CHead e1 (Bind b1) v1))).(let H4 \def 
(f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) (CHead c1 k u) 
(CHead e1 (Bind b1) v1) H3) in ((let H5 \def (f_equal C K (\lambda (e: 
C).(match e in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k | 
(CHead _ k0 _) \Rightarrow k0])) (CHead c1 k u) (CHead e1 (Bind b1) v1) H3) 
in ((let H6 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda 
(_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) 
(CHead c1 k u) (CHead e1 (Bind b1) v1) H3) in (\lambda (H7: (eq K k (Bind 
b1))).(\lambda (H8: (eq C c1 e1)).(eq_ind_r T v1 (\lambda (t: T).(ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c3 k t) 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csubt g e1 e2)))))) (eq_ind_r K (Bind b1) (\lambda (k0: K).(ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c3 k0 v1) 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csubt g e1 e2)))))) (let H9 \def (eq_ind C c1 (\lambda (c: C).((eq C c 
(CHead e1 (Bind b1) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: 
C).(\lambda (v2: T).(eq C c3 (CHead e2 (Bind b2) v2))))) (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2))))))) H2 e1 H8) in (let 
H10 \def (eq_ind C c1 (\lambda (c: C).(csubt g c c3)) H1 e1 H8) in 
(ex2_3_intro B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C 
(CHead c3 (Bind b1) v1) (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda 
(e2: C).(\lambda (_: T).(csubt g e1 e2)))) b1 c3 v1 (refl_equal C (CHead c3 
(Bind b1) v1)) H10))) k H7) u H6)))) H5)) H4))))))))) (\lambda (c1: 
C).(\lambda (c3: C).(\lambda (H1: (csubt g c1 c3)).(\lambda (H2: (((eq C c1 
(CHead e1 (Bind b1) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: 
C).(\lambda (v2: T).(eq C c3 (CHead e2 (Bind b2) v2))))) (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2)))))))).(\lambda (b: 
B).(\lambda (_: (not (eq B b Void))).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (H4: (eq C (CHead c1 (Bind Void) u1) (CHead e1 (Bind b1) 
v1))).(let H5 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) 
(CHead c1 (Bind Void) u1) (CHead e1 (Bind b1) v1) H4) in ((let H6 \def 
(f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow Void | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow 
Void])])) (CHead c1 (Bind Void) u1) (CHead e1 (Bind b1) v1) H4) in ((let H7 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u1 | (CHead _ _ t) \Rightarrow t])) (CHead c1 
(Bind Void) u1) (CHead e1 (Bind b1) v1) H4) in (\lambda (H8: (eq B Void 
b1)).(\lambda (H9: (eq C c1 e1)).(let H10 \def (eq_ind C c1 (\lambda (c: 
C).((eq C c (CHead e1 (Bind b1) v1)) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c3 (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2))))))) H2 e1 
H9) in (let H11 \def (eq_ind C c1 (\lambda (c: C).(csubt g c c3)) H1 e1 H9) 
in (let H12 \def (eq_ind_r B b1 (\lambda (b0: B).((eq C e1 (CHead e1 (Bind 
b0) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: 
T).(eq C c3 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2))))))) H10 Void H8) in (ex2_3_intro B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c3 (Bind b) 
u2) (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csubt g e1 e2)))) b c3 u2 (refl_equal C (CHead c3 (Bind b) u2)) 
H11))))))) H6)) H5))))))))))) (\lambda (c1: C).(\lambda (c3: C).(\lambda (H1: 
(csubt g c1 c3)).(\lambda (H2: (((eq C c1 (CHead e1 (Bind b1) v1)) \to (ex2_3 
B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c3 (CHead e2 
(Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g 
e1 e2)))))))).(\lambda (u: T).(\lambda (t: T).(\lambda (H3: (ty3 g c1 u 
t)).(\lambda (H4: (ty3 g c3 u t)).(\lambda (H5: (eq C (CHead c1 (Bind Abst) 
t) (CHead e1 (Bind b1) v1))).(let H6 \def (f_equal C C (\lambda (e: C).(match 
e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c1 | (CHead c _ 
_) \Rightarrow c])) (CHead c1 (Bind Abst) t) (CHead e1 (Bind b1) v1) H5) in 
((let H7 \def (f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: 
C).B) with [(CSort _) \Rightarrow Abst | (CHead _ k _) \Rightarrow (match k 
in K return (\lambda (_: K).B) with [(Bind b) \Rightarrow b | (Flat _) 
\Rightarrow Abst])])) (CHead c1 (Bind Abst) t) (CHead e1 (Bind b1) v1) H5) in 
((let H8 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: 
C).T) with [(CSort _) \Rightarrow t | (CHead _ _ t0) \Rightarrow t0])) (CHead 
c1 (Bind Abst) t) (CHead e1 (Bind b1) v1) H5) in (\lambda (H9: (eq B Abst 
b1)).(\lambda (H10: (eq C c1 e1)).(let H11 \def (eq_ind T t (\lambda (t0: 
T).(ty3 g c3 u t0)) H4 v1 H8) in (let H12 \def (eq_ind T t (\lambda (t0: 
T).(ty3 g c1 u t0)) H3 v1 H8) in (let H13 \def (eq_ind C c1 (\lambda (c: 
C).(ty3 g c u v1)) H12 e1 H10) in (let H14 \def (eq_ind C c1 (\lambda (c: 
C).((eq C c (CHead e1 (Bind b1) v1)) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c3 (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2))))))) H2 e1 
H10) in (let H15 \def (eq_ind C c1 (\lambda (c: C).(csubt g c c3)) H1 e1 H10) 
in (let H16 \def (eq_ind_r B b1 (\lambda (b: B).((eq C e1 (CHead e1 (Bind b) 
v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq 
C c3 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda 
(_: T).(csubt g e1 e2))))))) H14 Abst H9) in (ex2_3_intro B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c3 (Bind Abbr) u) (CHead e2 
(Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g 
e1 e2)))) Abbr c3 u (refl_equal C (CHead c3 (Bind Abbr) u)) H15)))))))))) 
H7)) H6))))))))))) y c2 H0))) H)))))).
(* COMMENTS
Initial nodes: 1899
END *)

