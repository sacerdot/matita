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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/csubt/fwd".

include "csubt/defs.ma".

theorem csubt_inv_coq:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).(\forall (P: ((G \to (C \to 
(C \to Prop))))).((((csubt g c1 c2) \to (\forall (n: nat).((eq C (CSort n) 
c1) \to ((eq C (CSort n) c2) \to (P g c1 c2)))))) \to ((((csubt g c1 c2) \to 
(\forall (c0: C).(\forall (c3: C).(\forall (k: K).(\forall (u: T).((eq C 
(CHead c0 k u) c1) \to ((eq C (CHead c3 k u) c2) \to ((csubt g c0 c3) \to (P 
g c1 c2)))))))))) \to ((((csubt g c1 c2) \to (\forall (c0: C).(\forall (c3: 
C).(\forall (b: B).(\forall (u1: T).(\forall (u2: T).((eq C (CHead c0 (Bind 
Void) u1) c1) \to ((eq C (CHead c3 (Bind b) u2) c2) \to ((csubt g c0 c3) \to 
((not (eq B b Void)) \to (P g c1 c2)))))))))))) \to ((((csubt g c1 c2) \to 
(\forall (c0: C).(\forall (c3: C).(\forall (u: T).(\forall (t: T).((eq C 
(CHead c0 (Bind Abst) t) c1) \to ((eq C (CHead c3 (Bind Abbr) u) c2) \to 
((csubt g c0 c3) \to ((ty3 g c3 u t) \to (P g c1 c2))))))))))) \to ((csubt g 
c1 c2) \to (P g c1 c2)))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (P: ((G \to (C \to 
(C \to Prop))))).(\lambda (H: (((csubt g c1 c2) \to (\forall (n: nat).((eq C 
(CSort n) c1) \to ((eq C (CSort n) c2) \to (P g c1 c2))))))).(\lambda (H0: 
(((csubt g c1 c2) \to (\forall (c0: C).(\forall (c3: C).(\forall (k: 
K).(\forall (u: T).((eq C (CHead c0 k u) c1) \to ((eq C (CHead c3 k u) c2) 
\to ((csubt g c0 c3) \to (P g c1 c2))))))))))).(\lambda (H1: (((csubt g c1 
c2) \to (\forall (c0: C).(\forall (c3: C).(\forall (b: B).(\forall (u1: 
T).(\forall (u2: T).((eq C (CHead c0 (Bind Void) u1) c1) \to ((eq C (CHead c3 
(Bind b) u2) c2) \to ((csubt g c0 c3) \to ((not (eq B b Void)) \to (P g c1 
c2))))))))))))).(\lambda (H2: (((csubt g c1 c2) \to (\forall (c0: C).(\forall 
(c3: C).(\forall (u: T).(\forall (t: T).((eq C (CHead c0 (Bind Abst) t) c1) 
\to ((eq C (CHead c3 (Bind Abbr) u) c2) \to ((csubt g c0 c3) \to ((ty3 g c3 u 
t) \to (P g c1 c2)))))))))))).(\lambda (H3: (csubt g c1 c2)).(let H4 \def 
(match H3 in csubt return (\lambda (c: C).(\lambda (c0: C).(\lambda (_: 
(csubt ? c c0)).((eq C c c1) \to ((eq C c0 c2) \to (P g c1 c2)))))) with 
[(csubt_sort n) \Rightarrow (\lambda (H4: (eq C (CSort n) c1)).(\lambda (H5: 
(eq C (CSort n) c2)).(H H3 n H4 H5))) | (csubt_head c0 c3 H4 k u) \Rightarrow 
(\lambda (H5: (eq C (CHead c0 k u) c1)).(\lambda (H6: (eq C (CHead c3 k u) 
c2)).(H0 H3 c0 c3 k u H5 H6 H4))) | (csubt_void c0 c3 H4 b H5 u1 u2) 
\Rightarrow (\lambda (H6: (eq C (CHead c0 (Bind Void) u1) c1)).(\lambda (H7: 
(eq C (CHead c3 (Bind b) u2) c2)).(H1 H3 c0 c3 b u1 u2 H6 H7 H4 H5))) | 
(csubt_abst c0 c3 H4 u t H5) \Rightarrow (\lambda (H6: (eq C (CHead c0 (Bind 
Abst) t) c1)).(\lambda (H7: (eq C (CHead c3 (Bind Abbr) u) c2)).(H2 H3 c0 c3 
u t H6 H7 H4 H5)))]) in (H4 (refl_equal C c1) (refl_equal C c2))))))))))).

theorem csubt_gen_abbr:
 \forall (g: G).(\forall (e1: C).(\forall (c2: C).(\forall (v: T).((csubt g 
(CHead e1 (Bind Abbr) v) c2) \to (ex2 C (\lambda (e2: C).(eq C c2 (CHead e2 
(Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 e2)))))))
\def
 \lambda (g: G).(\lambda (e1: C).(\lambda (c2: C).(\lambda (v: T).(\lambda 
(H: (csubt g (CHead e1 (Bind Abbr) v) c2)).(csubt_inv_coq g (CHead e1 (Bind 
Abbr) v) c2 (\lambda (g0: G).(\lambda (_: C).(\lambda (c0: C).(ex2 C (\lambda 
(e2: C).(eq C c0 (CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csubt g0 e1 
e2)))))) (\lambda (H0: (csubt g (CHead e1 (Bind Abbr) v) c2)).(\lambda (n: 
nat).(\lambda (H1: (eq C (CSort n) (CHead e1 (Bind Abbr) v))).(\lambda (H2: 
(eq C (CSort n) c2)).(let H3 \def (eq_ind_r C c2 (\lambda (c: C).(csubt g 
(CHead e1 (Bind Abbr) v) c)) H0 (CSort n) H2) in (let H4 \def (eq_ind_r C c2 
(\lambda (c: C).(csubt g (CHead e1 (Bind Abbr) v) c)) H (CSort n) H2) in 
(eq_ind C (CSort n) (\lambda (c: C).(ex2 C (\lambda (e2: C).(eq C c (CHead e2 
(Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 e2)))) (let H5 \def (eq_ind C 
(CSort n) (\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with 
[(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow False])) I (CHead e1 
(Bind Abbr) v) H1) in (False_ind (ex2 C (\lambda (e2: C).(eq C (CSort n) 
(CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 e2))) H5)) c2 
H2))))))) (\lambda (H0: (csubt g (CHead e1 (Bind Abbr) v) c2)).(\lambda (c0: 
C).(\lambda (c3: C).(\lambda (k: K).(\lambda (u: T).(\lambda (H1: (eq C 
(CHead c0 k u) (CHead e1 (Bind Abbr) v))).(\lambda (H2: (eq C (CHead c3 k u) 
c2)).(\lambda (H3: (csubt g c0 c3)).(let H4 \def (eq_ind_r C c2 (\lambda (c: 
C).(csubt g (CHead e1 (Bind Abbr) v) c)) H0 (CHead c3 k u) H2) in (let H5 
\def (eq_ind_r C c2 (\lambda (c: C).(csubt g (CHead e1 (Bind Abbr) v) c)) H 
(CHead c3 k u) H2) in (eq_ind C (CHead c3 k u) (\lambda (c: C).(ex2 C 
(\lambda (e2: C).(eq C c (CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csubt g 
e1 e2)))) (let H6 \def (f_equal C C (\lambda (e: C).(match e in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow 
c])) (CHead c0 k u) (CHead e1 (Bind Abbr) v) H1) in ((let H7 \def (f_equal C 
K (\lambda (e: C).(match e in C return (\lambda (_: C).K) with [(CSort _) 
\Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) (CHead c0 k u) (CHead e1 
(Bind Abbr) v) H1) in ((let H8 \def (f_equal C T (\lambda (e: C).(match e in 
C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t) 
\Rightarrow t])) (CHead c0 k u) (CHead e1 (Bind Abbr) v) H1) in (\lambda (H9: 
(eq K k (Bind Abbr))).(\lambda (H10: (eq C c0 e1)).(let H11 \def (eq_ind T u 
(\lambda (t: T).(csubt g (CHead e1 (Bind Abbr) v) (CHead c3 k t))) H5 v H8) 
in (let H12 \def (eq_ind T u (\lambda (t: T).(csubt g (CHead e1 (Bind Abbr) 
v) (CHead c3 k t))) H4 v H8) in (eq_ind_r T v (\lambda (t: T).(ex2 C (\lambda 
(e2: C).(eq C (CHead c3 k t) (CHead e2 (Bind Abbr) v))) (\lambda (e2: 
C).(csubt g e1 e2)))) (let H13 \def (eq_ind K k (\lambda (k0: K).(csubt g 
(CHead e1 (Bind Abbr) v) (CHead c3 k0 v))) H11 (Bind Abbr) H9) in (let H14 
\def (eq_ind K k (\lambda (k0: K).(csubt g (CHead e1 (Bind Abbr) v) (CHead c3 
k0 v))) H12 (Bind Abbr) H9) in (eq_ind_r K (Bind Abbr) (\lambda (k0: K).(ex2 
C (\lambda (e2: C).(eq C (CHead c3 k0 v) (CHead e2 (Bind Abbr) v))) (\lambda 
(e2: C).(csubt g e1 e2)))) (let H15 \def (eq_ind C c0 (\lambda (c: C).(csubt 
g c c3)) H3 e1 H10) in (ex_intro2 C (\lambda (e2: C).(eq C (CHead c3 (Bind 
Abbr) v) (CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 e2)) c3 
(refl_equal C (CHead c3 (Bind Abbr) v)) H15)) k H9))) u H8)))))) H7)) H6)) c2 
H2))))))))))) (\lambda (H0: (csubt g (CHead e1 (Bind Abbr) v) c2)).(\lambda 
(c0: C).(\lambda (c3: C).(\lambda (b: B).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (H2: (eq C (CHead c0 (Bind Void) u1) (CHead e1 (Bind Abbr) 
v))).(\lambda (H3: (eq C (CHead c3 (Bind b) u2) c2)).(\lambda (_: (csubt g c0 
c3)).(\lambda (_: (not (eq B b Void))).(let H5 \def (eq_ind_r C c2 (\lambda 
(c: C).(csubt g (CHead e1 (Bind Abbr) v) c)) H0 (CHead c3 (Bind b) u2) H3) in 
(let H6 \def (eq_ind_r C c2 (\lambda (c: C).(csubt g (CHead e1 (Bind Abbr) v) 
c)) H (CHead c3 (Bind b) u2) H3) in (eq_ind C (CHead c3 (Bind b) u2) (\lambda 
(c: C).(ex2 C (\lambda (e2: C).(eq C c (CHead e2 (Bind Abbr) v))) (\lambda 
(e2: C).(csubt g e1 e2)))) (let H7 \def (eq_ind C (CHead c0 (Bind Void) u1) 
(\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b0) \Rightarrow (match b0 in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow False | Abst \Rightarrow False | Void 
\Rightarrow True]) | (Flat _) \Rightarrow False])])) I (CHead e1 (Bind Abbr) 
v) H2) in (False_ind (ex2 C (\lambda (e2: C).(eq C (CHead c3 (Bind b) u2) 
(CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 e2))) H7)) c2 
H3))))))))))))) (\lambda (H0: (csubt g (CHead e1 (Bind Abbr) v) c2)).(\lambda 
(c0: C).(\lambda (c3: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H2: (eq C 
(CHead c0 (Bind Abst) t) (CHead e1 (Bind Abbr) v))).(\lambda (H3: (eq C 
(CHead c3 (Bind Abbr) u) c2)).(\lambda (_: (csubt g c0 c3)).(\lambda (_: (ty3 
g c3 u t)).(let H5 \def (eq_ind_r C c2 (\lambda (c: C).(csubt g (CHead e1 
(Bind Abbr) v) c)) H0 (CHead c3 (Bind Abbr) u) H3) in (let H6 \def (eq_ind_r 
C c2 (\lambda (c: C).(csubt g (CHead e1 (Bind Abbr) v) c)) H (CHead c3 (Bind 
Abbr) u) H3) in (eq_ind C (CHead c3 (Bind Abbr) u) (\lambda (c: C).(ex2 C 
(\lambda (e2: C).(eq C c (CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csubt g 
e1 e2)))) (let H7 \def (eq_ind C (CHead c0 (Bind Abst) t) (\lambda (ee: 
C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow 
False | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) 
with [(Bind b) \Rightarrow (match b in B return (\lambda (_: B).Prop) with 
[Abbr \Rightarrow False | Abst \Rightarrow True | Void \Rightarrow False]) | 
(Flat _) \Rightarrow False])])) I (CHead e1 (Bind Abbr) v) H2) in (False_ind 
(ex2 C (\lambda (e2: C).(eq C (CHead c3 (Bind Abbr) u) (CHead e2 (Bind Abbr) 
v))) (\lambda (e2: C).(csubt g e1 e2))) H7)) c2 H3)))))))))))) H))))).

theorem csubt_gen_abst:
 \forall (g: G).(\forall (e1: C).(\forall (c2: C).(\forall (v1: T).((csubt g 
(CHead e1 (Bind Abst) v1) c2) \to (or (ex2 C (\lambda (e2: C).(eq C c2 (CHead 
e2 (Bind Abst) v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex3_2 C T (\lambda 
(e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g 
e2 v2 v1)))))))))
\def
 \lambda (g: G).(\lambda (e1: C).(\lambda (c2: C).(\lambda (v1: T).(\lambda 
(H: (csubt g (CHead e1 (Bind Abst) v1) c2)).(csubt_inv_coq g (CHead e1 (Bind 
Abst) v1) c2 (\lambda (g0: G).(\lambda (_: C).(\lambda (c0: C).(or (ex2 C 
(\lambda (e2: C).(eq C c0 (CHead e2 (Bind Abst) v1))) (\lambda (e2: C).(csubt 
g0 e1 e2))) (ex3_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C c0 (CHead e2 
(Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csubt g0 e1 e2))) 
(\lambda (e2: C).(\lambda (v2: T).(ty3 g0 e2 v2 v1)))))))) (\lambda (H0: 
(csubt g (CHead e1 (Bind Abst) v1) c2)).(\lambda (n: nat).(\lambda (H1: (eq C 
(CSort n) (CHead e1 (Bind Abst) v1))).(\lambda (H2: (eq C (CSort n) c2)).(let 
H3 \def (eq_ind_r C c2 (\lambda (c: C).(csubt g (CHead e1 (Bind Abst) v1) c)) 
H0 (CSort n) H2) in (let H4 \def (eq_ind_r C c2 (\lambda (c: C).(csubt g 
(CHead e1 (Bind Abst) v1) c)) H (CSort n) H2) in (eq_ind C (CSort n) (\lambda 
(c: C).(or (ex2 C (\lambda (e2: C).(eq C c (CHead e2 (Bind Abst) v1))) 
(\lambda (e2: C).(csubt g e1 e2))) (ex3_2 C T (\lambda (e2: C).(\lambda (v2: 
T).(eq C c (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: 
T).(csubt g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1)))))) 
(let H5 \def (eq_ind C (CSort n) (\lambda (ee: C).(match ee in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) 
\Rightarrow False])) I (CHead e1 (Bind Abst) v1) H1) in (False_ind (or (ex2 C 
(\lambda (e2: C).(eq C (CSort n) (CHead e2 (Bind Abst) v1))) (\lambda (e2: 
C).(csubt g e1 e2))) (ex3_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C 
(CSort n) (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: 
T).(csubt g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1))))) 
H5)) c2 H2))))))) (\lambda (H0: (csubt g (CHead e1 (Bind Abst) v1) 
c2)).(\lambda (c0: C).(\lambda (c3: C).(\lambda (k: K).(\lambda (u: 
T).(\lambda (H1: (eq C (CHead c0 k u) (CHead e1 (Bind Abst) v1))).(\lambda 
(H2: (eq C (CHead c3 k u) c2)).(\lambda (H3: (csubt g c0 c3)).(let H4 \def 
(eq_ind_r C c2 (\lambda (c: C).(csubt g (CHead e1 (Bind Abst) v1) c)) H0 
(CHead c3 k u) H2) in (let H5 \def (eq_ind_r C c2 (\lambda (c: C).(csubt g 
(CHead e1 (Bind Abst) v1) c)) H (CHead c3 k u) H2) in (eq_ind C (CHead c3 k 
u) (\lambda (c: C).(or (ex2 C (\lambda (e2: C).(eq C c (CHead e2 (Bind Abst) 
v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex3_2 C T (\lambda (e2: C).(\lambda 
(v2: T).(eq C c (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: 
T).(csubt g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1)))))) 
(let H6 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: 
C).C) with [(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead 
c0 k u) (CHead e1 (Bind Abst) v1) H1) in ((let H7 \def (f_equal C K (\lambda 
(e: C).(match e in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k 
| (CHead _ k0 _) \Rightarrow k0])) (CHead c0 k u) (CHead e1 (Bind Abst) v1) 
H1) in ((let H8 \def (f_equal C T (\lambda (e: C).(match e in C return 
(\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow 
t])) (CHead c0 k u) (CHead e1 (Bind Abst) v1) H1) in (\lambda (H9: (eq K k 
(Bind Abst))).(\lambda (H10: (eq C c0 e1)).(let H11 \def (eq_ind T u (\lambda 
(t: T).(csubt g (CHead e1 (Bind Abst) v1) (CHead c3 k t))) H5 v1 H8) in (let 
H12 \def (eq_ind T u (\lambda (t: T).(csubt g (CHead e1 (Bind Abst) v1) 
(CHead c3 k t))) H4 v1 H8) in (eq_ind_r T v1 (\lambda (t: T).(or (ex2 C 
(\lambda (e2: C).(eq C (CHead c3 k t) (CHead e2 (Bind Abst) v1))) (\lambda 
(e2: C).(csubt g e1 e2))) (ex3_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C 
(CHead c3 k t) (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: 
T).(csubt g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1)))))) 
(let H13 \def (eq_ind K k (\lambda (k0: K).(csubt g (CHead e1 (Bind Abst) v1) 
(CHead c3 k0 v1))) H11 (Bind Abst) H9) in (let H14 \def (eq_ind K k (\lambda 
(k0: K).(csubt g (CHead e1 (Bind Abst) v1) (CHead c3 k0 v1))) H12 (Bind Abst) 
H9) in (eq_ind_r K (Bind Abst) (\lambda (k0: K).(or (ex2 C (\lambda (e2: 
C).(eq C (CHead c3 k0 v1) (CHead e2 (Bind Abst) v1))) (\lambda (e2: C).(csubt 
g e1 e2))) (ex3_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c3 k0 
v1) (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csubt g e1 
e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1)))))) (let H15 \def 
(eq_ind C c0 (\lambda (c: C).(csubt g c c3)) H3 e1 H10) in (or_introl (ex2 C 
(\lambda (e2: C).(eq C (CHead c3 (Bind Abst) v1) (CHead e2 (Bind Abst) v1))) 
(\lambda (e2: C).(csubt g e1 e2))) (ex3_2 C T (\lambda (e2: C).(\lambda (v2: 
T).(eq C (CHead c3 (Bind Abst) v1) (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g 
e2 v2 v1)))) (ex_intro2 C (\lambda (e2: C).(eq C (CHead c3 (Bind Abst) v1) 
(CHead e2 (Bind Abst) v1))) (\lambda (e2: C).(csubt g e1 e2)) c3 (refl_equal 
C (CHead c3 (Bind Abst) v1)) H15))) k H9))) u H8)))))) H7)) H6)) c2 
H2))))))))))) (\lambda (H0: (csubt g (CHead e1 (Bind Abst) v1) c2)).(\lambda 
(c0: C).(\lambda (c3: C).(\lambda (b: B).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (H2: (eq C (CHead c0 (Bind Void) u1) (CHead e1 (Bind Abst) 
v1))).(\lambda (H3: (eq C (CHead c3 (Bind b) u2) c2)).(\lambda (_: (csubt g 
c0 c3)).(\lambda (_: (not (eq B b Void))).(let H5 \def (eq_ind_r C c2 
(\lambda (c: C).(csubt g (CHead e1 (Bind Abst) v1) c)) H0 (CHead c3 (Bind b) 
u2) H3) in (let H6 \def (eq_ind_r C c2 (\lambda (c: C).(csubt g (CHead e1 
(Bind Abst) v1) c)) H (CHead c3 (Bind b) u2) H3) in (eq_ind C (CHead c3 (Bind 
b) u2) (\lambda (c: C).(or (ex2 C (\lambda (e2: C).(eq C c (CHead e2 (Bind 
Abst) v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex3_2 C T (\lambda (e2: 
C).(\lambda (v2: T).(eq C c (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g 
e2 v2 v1)))))) (let H7 \def (eq_ind C (CHead c0 (Bind Void) u1) (\lambda (ee: 
C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow 
False | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) 
with [(Bind b0) \Rightarrow (match b0 in B return (\lambda (_: B).Prop) with 
[Abbr \Rightarrow False | Abst \Rightarrow False | Void \Rightarrow True]) | 
(Flat _) \Rightarrow False])])) I (CHead e1 (Bind Abst) v1) H2) in (False_ind 
(or (ex2 C (\lambda (e2: C).(eq C (CHead c3 (Bind b) u2) (CHead e2 (Bind 
Abst) v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex3_2 C T (\lambda (e2: 
C).(\lambda (v2: T).(eq C (CHead c3 (Bind b) u2) (CHead e2 (Bind Abbr) v2)))) 
(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (e2: C).(\lambda 
(v2: T).(ty3 g e2 v2 v1))))) H7)) c2 H3))))))))))))) (\lambda (H0: (csubt g 
(CHead e1 (Bind Abst) v1) c2)).(\lambda (c0: C).(\lambda (c3: C).(\lambda (u: 
T).(\lambda (t: T).(\lambda (H2: (eq C (CHead c0 (Bind Abst) t) (CHead e1 
(Bind Abst) v1))).(\lambda (H3: (eq C (CHead c3 (Bind Abbr) u) c2)).(\lambda 
(H1: (csubt g c0 c3)).(\lambda (H4: (ty3 g c3 u t)).(let H5 \def (eq_ind_r C 
c2 (\lambda (c: C).(csubt g (CHead e1 (Bind Abst) v1) c)) H0 (CHead c3 (Bind 
Abbr) u) H3) in (let H6 \def (eq_ind_r C c2 (\lambda (c: C).(csubt g (CHead 
e1 (Bind Abst) v1) c)) H (CHead c3 (Bind Abbr) u) H3) in (eq_ind C (CHead c3 
(Bind Abbr) u) (\lambda (c: C).(or (ex2 C (\lambda (e2: C).(eq C c (CHead e2 
(Bind Abst) v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex3_2 C T (\lambda (e2: 
C).(\lambda (v2: T).(eq C c (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g 
e2 v2 v1)))))) (let H7 \def (f_equal C C (\lambda (e: C).(match e in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow 
c])) (CHead c0 (Bind Abst) t) (CHead e1 (Bind Abst) v1) H2) in ((let H8 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow t | (CHead _ _ t0) \Rightarrow t0])) (CHead c0 (Bind 
Abst) t) (CHead e1 (Bind Abst) v1) H2) in (\lambda (H9: (eq C c0 e1)).(let 
H10 \def (eq_ind T t (\lambda (t0: T).(ty3 g c3 u t0)) H4 v1 H8) in (let H11 
\def (eq_ind C c0 (\lambda (c: C).(csubt g c c3)) H1 e1 H9) in (or_intror 
(ex2 C (\lambda (e2: C).(eq C (CHead c3 (Bind Abbr) u) (CHead e2 (Bind Abst) 
v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex3_2 C T (\lambda (e2: C).(\lambda 
(v2: T).(eq C (CHead c3 (Bind Abbr) u) (CHead e2 (Bind Abbr) v2)))) (\lambda 
(e2: C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (e2: C).(\lambda (v2: 
T).(ty3 g e2 v2 v1)))) (ex3_2_intro C T (\lambda (e2: C).(\lambda (v2: T).(eq 
C (CHead c3 (Bind Abbr) u) (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g 
e2 v2 v1))) c3 u (refl_equal C (CHead c3 (Bind Abbr) u)) H11 H10)))))) H7)) 
c2 H3)))))))))))) H))))).

theorem csubt_gen_bind:
 \forall (g: G).(\forall (b1: B).(\forall (e1: C).(\forall (c2: C).(\forall 
(v1: T).((csubt g (CHead e1 (Bind b1) v1) c2) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2))))))))))
\def
 \lambda (g: G).(\lambda (b1: B).(\lambda (e1: C).(\lambda (c2: C).(\lambda 
(v1: T).(\lambda (H: (csubt g (CHead e1 (Bind b1) v1) c2)).(csubt_inv_coq g 
(CHead e1 (Bind b1) v1) c2 (\lambda (g0: G).(\lambda (_: C).(\lambda (c0: 
C).(ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c0 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csubt g0 e1 e2)))))))) (\lambda (H0: (csubt g (CHead e1 (Bind b1) v1) 
c2)).(\lambda (n: nat).(\lambda (H1: (eq C (CSort n) (CHead e1 (Bind b1) 
v1))).(\lambda (H2: (eq C (CSort n) c2)).(let H3 \def (eq_ind_r C c2 (\lambda 
(c: C).(csubt g (CHead e1 (Bind b1) v1) c)) H0 (CSort n) H2) in (let H4 \def 
(eq_ind_r C c2 (\lambda (c: C).(csubt g (CHead e1 (Bind b1) v1) c)) H (CSort 
n) H2) in (eq_ind C (CSort n) (\lambda (c: C).(ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2)))))) (let H5 
\def (eq_ind C (CSort n) (\lambda (ee: C).(match ee in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow 
False])) I (CHead e1 (Bind b1) v1) H1) in (False_ind (ex2_3 B C T (\lambda 
(b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CSort n) (CHead e2 (Bind b2) 
v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2))))) 
H5)) c2 H2))))))) (\lambda (H0: (csubt g (CHead e1 (Bind b1) v1) 
c2)).(\lambda (c0: C).(\lambda (c3: C).(\lambda (k: K).(\lambda (u: 
T).(\lambda (H1: (eq C (CHead c0 k u) (CHead e1 (Bind b1) v1))).(\lambda (H2: 
(eq C (CHead c3 k u) c2)).(\lambda (H3: (csubt g c0 c3)).(let H4 \def 
(eq_ind_r C c2 (\lambda (c: C).(csubt g (CHead e1 (Bind b1) v1) c)) H0 (CHead 
c3 k u) H2) in (let H5 \def (eq_ind_r C c2 (\lambda (c: C).(csubt g (CHead e1 
(Bind b1) v1) c)) H (CHead c3 k u) H2) in (eq_ind C (CHead c3 k u) (\lambda 
(c: C).(ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C 
c (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csubt g e1 e2)))))) (let H6 \def (f_equal C C (\lambda (e: C).(match e in 
C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | (CHead c _ _) 
\Rightarrow c])) (CHead c0 k u) (CHead e1 (Bind b1) v1) H1) in ((let H7 \def 
(f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) with 
[(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) (CHead c0 k u) 
(CHead e1 (Bind b1) v1) H1) in ((let H8 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | 
(CHead _ _ t) \Rightarrow t])) (CHead c0 k u) (CHead e1 (Bind b1) v1) H1) in 
(\lambda (H9: (eq K k (Bind b1))).(\lambda (H10: (eq C c0 e1)).(let H11 \def 
(eq_ind T u (\lambda (t: T).(csubt g (CHead e1 (Bind b1) v1) (CHead c3 k t))) 
H5 v1 H8) in (let H12 \def (eq_ind T u (\lambda (t: T).(csubt g (CHead e1 
(Bind b1) v1) (CHead c3 k t))) H4 v1 H8) in (eq_ind_r T v1 (\lambda (t: 
T).(ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C 
(CHead c3 k t) (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2)))))) (let H13 \def (eq_ind K k (\lambda 
(k0: K).(csubt g (CHead e1 (Bind b1) v1) (CHead c3 k0 v1))) H11 (Bind b1) H9) 
in (let H14 \def (eq_ind K k (\lambda (k0: K).(csubt g (CHead e1 (Bind b1) 
v1) (CHead c3 k0 v1))) H12 (Bind b1) H9) in (eq_ind_r K (Bind b1) (\lambda 
(k0: K).(ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C 
(CHead c3 k0 v1) (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2)))))) (let H15 \def (eq_ind C c0 (\lambda 
(c: C).(csubt g c c3)) H3 e1 H10) in (ex2_3_intro B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c3 (Bind b1) v1) (CHead e2 
(Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g 
e1 e2)))) b1 c3 v1 (refl_equal C (CHead c3 (Bind b1) v1)) H15)) k H9))) u 
H8)))))) H7)) H6)) c2 H2))))))))))) (\lambda (H0: (csubt g (CHead e1 (Bind 
b1) v1) c2)).(\lambda (c0: C).(\lambda (c3: C).(\lambda (b: B).(\lambda (u1: 
T).(\lambda (u2: T).(\lambda (H2: (eq C (CHead c0 (Bind Void) u1) (CHead e1 
(Bind b1) v1))).(\lambda (H3: (eq C (CHead c3 (Bind b) u2) c2)).(\lambda (H1: 
(csubt g c0 c3)).(\lambda (_: (not (eq B b Void))).(let H5 \def (eq_ind_r C 
c2 (\lambda (c: C).(csubt g (CHead e1 (Bind b1) v1) c)) H0 (CHead c3 (Bind b) 
u2) H3) in (let H6 \def (eq_ind_r C c2 (\lambda (c: C).(csubt g (CHead e1 
(Bind b1) v1) c)) H (CHead c3 (Bind b) u2) H3) in (eq_ind C (CHead c3 (Bind 
b) u2) (\lambda (c: C).(ex2_3 B C T (\lambda (b2: B).(\lambda (e2: 
C).(\lambda (v2: T).(eq C c (CHead e2 (Bind b2) v2))))) (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2)))))) (let H7 \def 
(f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead c0 (Bind 
Void) u1) (CHead e1 (Bind b1) v1) H2) in ((let H8 \def (f_equal C B (\lambda 
(e: C).(match e in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow 
Void | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).B) with 
[(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Void])])) (CHead c0 (Bind 
Void) u1) (CHead e1 (Bind b1) v1) H2) in ((let H9 \def (f_equal C T (\lambda 
(e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u1 
| (CHead _ _ t) \Rightarrow t])) (CHead c0 (Bind Void) u1) (CHead e1 (Bind 
b1) v1) H2) in (\lambda (H10: (eq B Void b1)).(\lambda (H11: (eq C c0 
e1)).(let H12 \def (eq_ind C c0 (\lambda (c: C).(csubt g c c3)) H1 e1 H11) in 
(let H13 \def (eq_ind_r B b1 (\lambda (b0: B).(csubt g (CHead e1 (Bind b0) 
v1) (CHead c3 (Bind b) u2))) H6 Void H10) in (let H14 \def (eq_ind_r B b1 
(\lambda (b0: B).(csubt g (CHead e1 (Bind b0) v1) (CHead c3 (Bind b) u2))) H5 
Void H10) in (ex2_3_intro B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda 
(v2: T).(eq C (CHead c3 (Bind b) u2) (CHead e2 (Bind b2) v2))))) (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2)))) b c3 u2 (refl_equal C 
(CHead c3 (Bind b) u2)) H12))))))) H8)) H7)) c2 H3))))))))))))) (\lambda (H0: 
(csubt g (CHead e1 (Bind b1) v1) c2)).(\lambda (c0: C).(\lambda (c3: 
C).(\lambda (u: T).(\lambda (t: T).(\lambda (H2: (eq C (CHead c0 (Bind Abst) 
t) (CHead e1 (Bind b1) v1))).(\lambda (H3: (eq C (CHead c3 (Bind Abbr) u) 
c2)).(\lambda (H1: (csubt g c0 c3)).(\lambda (H4: (ty3 g c3 u t)).(let H5 
\def (eq_ind_r C c2 (\lambda (c: C).(csubt g (CHead e1 (Bind b1) v1) c)) H0 
(CHead c3 (Bind Abbr) u) H3) in (let H6 \def (eq_ind_r C c2 (\lambda (c: 
C).(csubt g (CHead e1 (Bind b1) v1) c)) H (CHead c3 (Bind Abbr) u) H3) in 
(eq_ind C (CHead c3 (Bind Abbr) u) (\lambda (c: C).(ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2)))))) (let H7 
\def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) 
with [(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead c0 
(Bind Abst) t) (CHead e1 (Bind b1) v1) H2) in ((let H8 \def (f_equal C B 
(\lambda (e: C).(match e in C return (\lambda (_: C).B) with [(CSort _) 
\Rightarrow Abst | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).B) with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow Abst])])) 
(CHead c0 (Bind Abst) t) (CHead e1 (Bind b1) v1) H2) in ((let H9 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow t | (CHead _ _ t0) \Rightarrow t0])) (CHead c0 (Bind 
Abst) t) (CHead e1 (Bind b1) v1) H2) in (\lambda (H10: (eq B Abst 
b1)).(\lambda (H11: (eq C c0 e1)).(let H12 \def (eq_ind T t (\lambda (t0: 
T).(ty3 g c3 u t0)) H4 v1 H9) in (let H13 \def (eq_ind C c0 (\lambda (c: 
C).(csubt g c c3)) H1 e1 H11) in (let H14 \def (eq_ind_r B b1 (\lambda (b: 
B).(csubt g (CHead e1 (Bind b) v1) (CHead c3 (Bind Abbr) u))) H6 Abst H10) in 
(let H15 \def (eq_ind_r B b1 (\lambda (b: B).(csubt g (CHead e1 (Bind b) v1) 
(CHead c3 (Bind Abbr) u))) H5 Abst H10) in (ex2_3_intro B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c3 (Bind Abbr) u) (CHead e2 
(Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g 
e1 e2)))) Abbr c3 u (refl_equal C (CHead c3 (Bind Abbr) u)) H13)))))))) H8)) 
H7)) c2 H3)))))))))))) H)))))).

