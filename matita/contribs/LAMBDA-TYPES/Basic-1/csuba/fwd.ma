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

include "Basic-1/csuba/defs.ma".

theorem csuba_gen_abbr:
 \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u: T).((csuba g 
(CHead d1 (Bind Abbr) u) c) \to (ex2 C (\lambda (d2: C).(eq C c (CHead d2 
(Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))))))
\def
 \lambda (g: G).(\lambda (d1: C).(\lambda (c: C).(\lambda (u: T).(\lambda (H: 
(csuba g (CHead d1 (Bind Abbr) u) c)).(insert_eq C (CHead d1 (Bind Abbr) u) 
(\lambda (c0: C).(csuba g c0 c)) (\lambda (_: C).(ex2 C (\lambda (d2: C).(eq 
C c (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))) (\lambda 
(y: C).(\lambda (H0: (csuba g y c)).(csuba_ind g (\lambda (c0: C).(\lambda 
(c1: C).((eq C c0 (CHead d1 (Bind Abbr) u)) \to (ex2 C (\lambda (d2: C).(eq C 
c1 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))))) (\lambda 
(n: nat).(\lambda (H1: (eq C (CSort n) (CHead d1 (Bind Abbr) u))).(let H2 
\def (eq_ind C (CSort n) (\lambda (ee: C).(match ee in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow 
False])) I (CHead d1 (Bind Abbr) u) H1) in (False_ind (ex2 C (\lambda (d2: 
C).(eq C (CSort n) (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 
d2))) H2)))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (H1: (csuba g c1 
c2)).(\lambda (H2: (((eq C c1 (CHead d1 (Bind Abbr) u)) \to (ex2 C (\lambda 
(d2: C).(eq C c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 
d2)))))).(\lambda (k: K).(\lambda (u0: T).(\lambda (H3: (eq C (CHead c1 k u0) 
(CHead d1 (Bind Abbr) u))).(let H4 \def (f_equal C C (\lambda (e: C).(match e 
in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c1 | (CHead c0 _ 
_) \Rightarrow c0])) (CHead c1 k u0) (CHead d1 (Bind Abbr) u) H3) in ((let H5 
\def (f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) 
with [(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) (CHead c1 k 
u0) (CHead d1 (Bind Abbr) u) H3) in ((let H6 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | 
(CHead _ _ t) \Rightarrow t])) (CHead c1 k u0) (CHead d1 (Bind Abbr) u) H3) 
in (\lambda (H7: (eq K k (Bind Abbr))).(\lambda (H8: (eq C c1 d1)).(eq_ind_r 
T u (\lambda (t: T).(ex2 C (\lambda (d2: C).(eq C (CHead c2 k t) (CHead d2 
(Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))) (eq_ind_r K (Bind Abbr) 
(\lambda (k0: K).(ex2 C (\lambda (d2: C).(eq C (CHead c2 k0 u) (CHead d2 
(Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))) (let H9 \def (eq_ind C 
c1 (\lambda (c0: C).((eq C c0 (CHead d1 (Bind Abbr) u)) \to (ex2 C (\lambda 
(d2: C).(eq C c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 
d2))))) H2 d1 H8) in (let H10 \def (eq_ind C c1 (\lambda (c0: C).(csuba g c0 
c2)) H1 d1 H8) in (ex_intro2 C (\lambda (d2: C).(eq C (CHead c2 (Bind Abbr) 
u) (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)) c2 
(refl_equal C (CHead c2 (Bind Abbr) u)) H10))) k H7) u0 H6)))) H5)) 
H4))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (_: (csuba g c1 
c2)).(\lambda (_: (((eq C c1 (CHead d1 (Bind Abbr) u)) \to (ex2 C (\lambda 
(d2: C).(eq C c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 
d2)))))).(\lambda (b: B).(\lambda (_: (not (eq B b Void))).(\lambda (u1: 
T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead c1 (Bind Void) u1) (CHead d1 
(Bind Abbr) u))).(let H5 \def (eq_ind C (CHead c1 (Bind Void) u1) (\lambda 
(ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b0) \Rightarrow (match b0 in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow False | Abst \Rightarrow False | Void 
\Rightarrow True]) | (Flat _) \Rightarrow False])])) I (CHead d1 (Bind Abbr) 
u) H4) in (False_ind (ex2 C (\lambda (d2: C).(eq C (CHead c2 (Bind b) u2) 
(CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))) H5))))))))))) 
(\lambda (c1: C).(\lambda (c2: C).(\lambda (_: (csuba g c1 c2)).(\lambda (_: 
(((eq C c1 (CHead d1 (Bind Abbr) u)) \to (ex2 C (\lambda (d2: C).(eq C c2 
(CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))))).(\lambda (t: 
T).(\lambda (a: A).(\lambda (_: (arity g c1 t (asucc g a))).(\lambda (u0: 
T).(\lambda (_: (arity g c2 u0 a)).(\lambda (H5: (eq C (CHead c1 (Bind Abst) 
t) (CHead d1 (Bind Abbr) u))).(let H6 \def (eq_ind C (CHead c1 (Bind Abst) t) 
(\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b) \Rightarrow (match b in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow False | Abst \Rightarrow True | Void 
\Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead d1 (Bind Abbr) 
u) H5) in (False_ind (ex2 C (\lambda (d2: C).(eq C (CHead c2 (Bind Abbr) u0) 
(CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))) H6)))))))))))) 
y c H0))) H))))).
(* COMMENTS
Initial nodes: 1117
END *)

theorem csuba_gen_void:
 \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u1: T).((csuba g 
(CHead d1 (Bind Void) u1) c) \to (ex2_3 B C T (\lambda (b: B).(\lambda (d2: 
C).(\lambda (u2: T).(eq C c (CHead d2 (Bind b) u2))))) (\lambda (_: 
B).(\lambda (d2: C).(\lambda (_: T).(csuba g d1 d2)))))))))
\def
 \lambda (g: G).(\lambda (d1: C).(\lambda (c: C).(\lambda (u1: T).(\lambda 
(H: (csuba g (CHead d1 (Bind Void) u1) c)).(insert_eq C (CHead d1 (Bind Void) 
u1) (\lambda (c0: C).(csuba g c0 c)) (\lambda (_: C).(ex2_3 B C T (\lambda 
(b: B).(\lambda (d2: C).(\lambda (u2: T).(eq C c (CHead d2 (Bind b) u2))))) 
(\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csuba g d1 d2)))))) 
(\lambda (y: C).(\lambda (H0: (csuba g y c)).(csuba_ind g (\lambda (c0: 
C).(\lambda (c1: C).((eq C c0 (CHead d1 (Bind Void) u1)) \to (ex2_3 B C T 
(\lambda (b: B).(\lambda (d2: C).(\lambda (u2: T).(eq C c1 (CHead d2 (Bind b) 
u2))))) (\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csuba g d1 
d2)))))))) (\lambda (n: nat).(\lambda (H1: (eq C (CSort n) (CHead d1 (Bind 
Void) u1))).(let H2 \def (eq_ind C (CSort n) (\lambda (ee: C).(match ee in C 
return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) 
\Rightarrow False])) I (CHead d1 (Bind Void) u1) H1) in (False_ind (ex2_3 B C 
T (\lambda (b: B).(\lambda (d2: C).(\lambda (u2: T).(eq C (CSort n) (CHead d2 
(Bind b) u2))))) (\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csuba g d1 
d2))))) H2)))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (H1: (csuba g c1 
c2)).(\lambda (H2: (((eq C c1 (CHead d1 (Bind Void) u1)) \to (ex2_3 B C T 
(\lambda (b: B).(\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 (Bind b) 
u2))))) (\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csuba g d1 
d2)))))))).(\lambda (k: K).(\lambda (u: T).(\lambda (H3: (eq C (CHead c1 k u) 
(CHead d1 (Bind Void) u1))).(let H4 \def (f_equal C C (\lambda (e: C).(match 
e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c1 | (CHead c0 _ 
_) \Rightarrow c0])) (CHead c1 k u) (CHead d1 (Bind Void) u1) H3) in ((let H5 
\def (f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) 
with [(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) (CHead c1 k 
u) (CHead d1 (Bind Void) u1) H3) in ((let H6 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | 
(CHead _ _ t) \Rightarrow t])) (CHead c1 k u) (CHead d1 (Bind Void) u1) H3) 
in (\lambda (H7: (eq K k (Bind Void))).(\lambda (H8: (eq C c1 d1)).(eq_ind_r 
T u1 (\lambda (t: T).(ex2_3 B C T (\lambda (b: B).(\lambda (d2: C).(\lambda 
(u2: T).(eq C (CHead c2 k t) (CHead d2 (Bind b) u2))))) (\lambda (_: 
B).(\lambda (d2: C).(\lambda (_: T).(csuba g d1 d2)))))) (eq_ind_r K (Bind 
Void) (\lambda (k0: K).(ex2_3 B C T (\lambda (b: B).(\lambda (d2: C).(\lambda 
(u2: T).(eq C (CHead c2 k0 u1) (CHead d2 (Bind b) u2))))) (\lambda (_: 
B).(\lambda (d2: C).(\lambda (_: T).(csuba g d1 d2)))))) (let H9 \def (eq_ind 
C c1 (\lambda (c0: C).((eq C c0 (CHead d1 (Bind Void) u1)) \to (ex2_3 B C T 
(\lambda (b: B).(\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 (Bind b) 
u2))))) (\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csuba g d1 
d2))))))) H2 d1 H8) in (let H10 \def (eq_ind C c1 (\lambda (c0: C).(csuba g 
c0 c2)) H1 d1 H8) in (ex2_3_intro B C T (\lambda (b: B).(\lambda (d2: 
C).(\lambda (u2: T).(eq C (CHead c2 (Bind Void) u1) (CHead d2 (Bind b) 
u2))))) (\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csuba g d1 d2)))) 
Void c2 u1 (refl_equal C (CHead c2 (Bind Void) u1)) H10))) k H7) u H6)))) 
H5)) H4))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (H1: (csuba g c1 
c2)).(\lambda (H2: (((eq C c1 (CHead d1 (Bind Void) u1)) \to (ex2_3 B C T 
(\lambda (b: B).(\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 (Bind b) 
u2))))) (\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csuba g d1 
d2)))))))).(\lambda (b: B).(\lambda (_: (not (eq B b Void))).(\lambda (u0: 
T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead c1 (Bind Void) u0) (CHead d1 
(Bind Void) u1))).(let H5 \def (f_equal C C (\lambda (e: C).(match e in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow c1 | (CHead c0 _ _) 
\Rightarrow c0])) (CHead c1 (Bind Void) u0) (CHead d1 (Bind Void) u1) H4) in 
((let H6 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: 
C).T) with [(CSort _) \Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) (CHead 
c1 (Bind Void) u0) (CHead d1 (Bind Void) u1) H4) in (\lambda (H7: (eq C c1 
d1)).(let H8 \def (eq_ind C c1 (\lambda (c0: C).((eq C c0 (CHead d1 (Bind 
Void) u1)) \to (ex2_3 B C T (\lambda (b0: B).(\lambda (d2: C).(\lambda (u3: 
T).(eq C c2 (CHead d2 (Bind b0) u3))))) (\lambda (_: B).(\lambda (d2: 
C).(\lambda (_: T).(csuba g d1 d2))))))) H2 d1 H7) in (let H9 \def (eq_ind C 
c1 (\lambda (c0: C).(csuba g c0 c2)) H1 d1 H7) in (ex2_3_intro B C T (\lambda 
(b0: B).(\lambda (d2: C).(\lambda (u3: T).(eq C (CHead c2 (Bind b) u2) (CHead 
d2 (Bind b0) u3))))) (\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csuba 
g d1 d2)))) b c2 u2 (refl_equal C (CHead c2 (Bind b) u2)) H9))))) 
H5))))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (_: (csuba g c1 
c2)).(\lambda (_: (((eq C c1 (CHead d1 (Bind Void) u1)) \to (ex2_3 B C T 
(\lambda (b: B).(\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 (Bind b) 
u2))))) (\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csuba g d1 
d2)))))))).(\lambda (t: T).(\lambda (a: A).(\lambda (_: (arity g c1 t (asucc 
g a))).(\lambda (u: T).(\lambda (_: (arity g c2 u a)).(\lambda (H5: (eq C 
(CHead c1 (Bind Abst) t) (CHead d1 (Bind Void) u1))).(let H6 \def (eq_ind C 
(CHead c1 (Bind Abst) t) (\lambda (ee: C).(match ee in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match 
k in K return (\lambda (_: K).Prop) with [(Bind b) \Rightarrow (match b in B 
return (\lambda (_: B).Prop) with [Abbr \Rightarrow False | Abst \Rightarrow 
True | Void \Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead d1 
(Bind Void) u1) H5) in (False_ind (ex2_3 B C T (\lambda (b: B).(\lambda (d2: 
C).(\lambda (u2: T).(eq C (CHead c2 (Bind Abbr) u) (CHead d2 (Bind b) u2))))) 
(\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csuba g d1 d2))))) 
H6)))))))))))) y c H0))) H))))).
(* COMMENTS
Initial nodes: 1418
END *)

theorem csuba_gen_abst:
 \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u1: T).((csuba g 
(CHead d1 (Bind Abst) u1) c) \to (or (ex2 C (\lambda (d2: C).(eq C c (CHead 
d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))))))))
\def
 \lambda (g: G).(\lambda (d1: C).(\lambda (c: C).(\lambda (u1: T).(\lambda 
(H: (csuba g (CHead d1 (Bind Abst) u1) c)).(insert_eq C (CHead d1 (Bind Abst) 
u1) (\lambda (c0: C).(csuba g c0 c)) (\lambda (_: C).(or (ex2 C (\lambda (d2: 
C).(eq C c (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c (CHead 
d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a))))))) (\lambda (y: C).(\lambda (H0: (csuba g y 
c)).(csuba_ind g (\lambda (c0: C).(\lambda (c1: C).((eq C c0 (CHead d1 (Bind 
Abst) u1)) \to (or (ex2 C (\lambda (d2: C).(eq C c1 (CHead d2 (Bind Abst) 
u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(eq C c1 (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))))))) 
(\lambda (n: nat).(\lambda (H1: (eq C (CSort n) (CHead d1 (Bind Abst) 
u1))).(let H2 \def (eq_ind C (CSort n) (\lambda (ee: C).(match ee in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) 
\Rightarrow False])) I (CHead d1 (Bind Abst) u1) H1) in (False_ind (or (ex2 C 
(\lambda (d2: C).(eq C (CSort n) (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(eq C (CSort n) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) H2)))) 
(\lambda (c1: C).(\lambda (c2: C).(\lambda (H1: (csuba g c1 c2)).(\lambda 
(H2: (((eq C c1 (CHead d1 (Bind Abst) u1)) \to (or (ex2 C (\lambda (d2: 
C).(eq C c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a))))))))).(\lambda (k: K).(\lambda (u: T).(\lambda (H3: 
(eq C (CHead c1 k u) (CHead d1 (Bind Abst) u1))).(let H4 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow c1 | (CHead c0 _ _) \Rightarrow c0])) (CHead c1 k u) (CHead d1 
(Bind Abst) u1) H3) in ((let H5 \def (f_equal C K (\lambda (e: C).(match e in 
C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k | (CHead _ k0 _) 
\Rightarrow k0])) (CHead c1 k u) (CHead d1 (Bind Abst) u1) H3) in ((let H6 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead c1 k u) 
(CHead d1 (Bind Abst) u1) H3) in (\lambda (H7: (eq K k (Bind Abst))).(\lambda 
(H8: (eq C c1 d1)).(eq_ind_r T u1 (\lambda (t: T).(or (ex2 C (\lambda (d2: 
C).(eq C (CHead c2 k t) (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g 
d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C 
(CHead c2 k t) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a))))))) (eq_ind_r K (Bind Abst) 
(\lambda (k0: K).(or (ex2 C (\lambda (d2: C).(eq C (CHead c2 k0 u1) (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C (CHead c2 k0 u1) (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
(asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 
u2 a))))))) (let H9 \def (eq_ind C c1 (\lambda (c0: C).((eq C c0 (CHead d1 
(Bind Abst) u1)) \to (or (ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind 
Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))))) H2 
d1 H8) in (let H10 \def (eq_ind C c1 (\lambda (c0: C).(csuba g c0 c2)) H1 d1 
H8) in (or_introl (ex2 C (\lambda (d2: C).(eq C (CHead c2 (Bind Abst) u1) 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C (CHead c2 (Bind Abst) 
u1) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: 
A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(a: A).(arity g d2 u2 a))))) (ex_intro2 C (\lambda (d2: C).(eq C (CHead c2 
(Bind Abst) u1) (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2)) 
c2 (refl_equal C (CHead c2 (Bind Abst) u1)) H10)))) k H7) u H6)))) H5)) 
H4))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (_: (csuba g c1 
c2)).(\lambda (_: (((eq C c1 (CHead d1 (Bind Abst) u1)) \to (or (ex2 C 
(\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba 
g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq 
C c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: 
A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(a: A).(arity g d2 u2 a))))))))).(\lambda (b: B).(\lambda (_: (not (eq B b 
Void))).(\lambda (u0: T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead c1 (Bind 
Void) u0) (CHead d1 (Bind Abst) u1))).(let H5 \def (eq_ind C (CHead c1 (Bind 
Void) u0) (\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with 
[(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind b0) \Rightarrow (match b0 in B return 
(\lambda (_: B).Prop) with [Abbr \Rightarrow False | Abst \Rightarrow False | 
Void \Rightarrow True]) | (Flat _) \Rightarrow False])])) I (CHead d1 (Bind 
Abst) u1) H4) in (False_ind (or (ex2 C (\lambda (d2: C).(eq C (CHead c2 (Bind 
b) u2) (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 
C T A (\lambda (d2: C).(\lambda (u3: T).(\lambda (_: A).(eq C (CHead c2 (Bind 
b) u2) (CHead d2 (Bind Abbr) u3))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u3: T).(\lambda (a: A).(arity g d2 u3 a)))))) H5))))))))))) (\lambda (c1: 
C).(\lambda (c2: C).(\lambda (H1: (csuba g c1 c2)).(\lambda (H2: (((eq C c1 
(CHead d1 (Bind Abst) u1)) \to (or (ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))))))).(\lambda (t: T).(\lambda (a: A).(\lambda (H3: (arity g c1 t (asucc 
g a))).(\lambda (u: T).(\lambda (H4: (arity g c2 u a)).(\lambda (H5: (eq C 
(CHead c1 (Bind Abst) t) (CHead d1 (Bind Abst) u1))).(let H6 \def (f_equal C 
C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow c1 | (CHead c0 _ _) \Rightarrow c0])) (CHead c1 (Bind Abst) t) 
(CHead d1 (Bind Abst) u1) H5) in ((let H7 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow t | 
(CHead _ _ t0) \Rightarrow t0])) (CHead c1 (Bind Abst) t) (CHead d1 (Bind 
Abst) u1) H5) in (\lambda (H8: (eq C c1 d1)).(let H9 \def (eq_ind T t 
(\lambda (t0: T).(arity g c1 t0 (asucc g a))) H3 u1 H7) in (let H10 \def 
(eq_ind C c1 (\lambda (c0: C).(arity g c0 u1 (asucc g a))) H9 d1 H8) in (let 
H11 \def (eq_ind C c1 (\lambda (c0: C).((eq C c0 (CHead d1 (Bind Abst) u1)) 
\to (or (ex2 C (\lambda (d2: C).(eq C c2 (CHead d2 (Bind Abst) u1))) (\lambda 
(d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(eq C c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a0: A).(arity g d1 u1 (asucc g a0))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a0: A).(arity g d2 u2 a0)))))))) H2 d1 H8) 
in (let H12 \def (eq_ind C c1 (\lambda (c0: C).(csuba g c0 c2)) H1 d1 H8) in 
(or_intror (ex2 C (\lambda (d2: C).(eq C (CHead c2 (Bind Abbr) u) (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C (CHead c2 (Bind Abbr) u) 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(arity 
g d1 u1 (asucc g a0))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a0: 
A).(arity g d2 u2 a0))))) (ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(eq C (CHead c2 (Bind Abbr) u) (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(arity g d1 u1 (asucc g 
a0))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a0: A).(arity g d2 u2 
a0)))) c2 u a (refl_equal C (CHead c2 (Bind Abbr) u)) H12 H10 H4)))))))) 
H6)))))))))))) y c H0))) H))))).
(* COMMENTS
Initial nodes: 2550
END *)

theorem csuba_gen_flat:
 \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u1: T).(\forall 
(f: F).((csuba g (CHead d1 (Flat f) u1) c) \to (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(eq C c (CHead d2 (Flat f) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d1 d2)))))))))
\def
 \lambda (g: G).(\lambda (d1: C).(\lambda (c: C).(\lambda (u1: T).(\lambda 
(f: F).(\lambda (H: (csuba g (CHead d1 (Flat f) u1) c)).(insert_eq C (CHead 
d1 (Flat f) u1) (\lambda (c0: C).(csuba g c0 c)) (\lambda (_: C).(ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(eq C c (CHead d2 (Flat f) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d1 d2))))) (\lambda (y: C).(\lambda (H0: 
(csuba g y c)).(csuba_ind g (\lambda (c0: C).(\lambda (c1: C).((eq C c0 
(CHead d1 (Flat f) u1)) \to (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq 
C c1 (CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d1 
d2))))))) (\lambda (n: nat).(\lambda (H1: (eq C (CSort n) (CHead d1 (Flat f) 
u1))).(let H2 \def (eq_ind C (CSort n) (\lambda (ee: C).(match ee in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) 
\Rightarrow False])) I (CHead d1 (Flat f) u1) H1) in (False_ind (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(eq C (CSort n) (CHead d2 (Flat f) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d1 d2)))) H2)))) (\lambda (c1: 
C).(\lambda (c2: C).(\lambda (H1: (csuba g c1 c2)).(\lambda (H2: (((eq C c1 
(CHead d1 (Flat f) u1)) \to (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq 
C c2 (CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d1 
d2))))))).(\lambda (k: K).(\lambda (u: T).(\lambda (H3: (eq C (CHead c1 k u) 
(CHead d1 (Flat f) u1))).(let H4 \def (f_equal C C (\lambda (e: C).(match e 
in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c1 | (CHead c0 _ 
_) \Rightarrow c0])) (CHead c1 k u) (CHead d1 (Flat f) u1) H3) in ((let H5 
\def (f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) 
with [(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) (CHead c1 k 
u) (CHead d1 (Flat f) u1) H3) in ((let H6 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | 
(CHead _ _ t) \Rightarrow t])) (CHead c1 k u) (CHead d1 (Flat f) u1) H3) in 
(\lambda (H7: (eq K k (Flat f))).(\lambda (H8: (eq C c1 d1)).(eq_ind_r T u1 
(\lambda (t: T).(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C (CHead c2 
k t) (CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d1 
d2))))) (eq_ind_r K (Flat f) (\lambda (k0: K).(ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(eq C (CHead c2 k0 u1) (CHead d2 (Flat f) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d1 d2))))) (let H9 \def (eq_ind C c1 
(\lambda (c0: C).((eq C c0 (CHead d1 (Flat f) u1)) \to (ex2_2 C T (\lambda 
(d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 (Flat f) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d1 d2)))))) H2 d1 H8) in (let H10 \def (eq_ind C 
c1 (\lambda (c0: C).(csuba g c0 c2)) H1 d1 H8) in (ex2_2_intro C T (\lambda 
(d2: C).(\lambda (u2: T).(eq C (CHead c2 (Flat f) u1) (CHead d2 (Flat f) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d1 d2))) c2 u1 (refl_equal C 
(CHead c2 (Flat f) u1)) H10))) k H7) u H6)))) H5)) H4))))))))) (\lambda (c1: 
C).(\lambda (c2: C).(\lambda (_: (csuba g c1 c2)).(\lambda (_: (((eq C c1 
(CHead d1 (Flat f) u1)) \to (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq 
C c2 (CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d1 
d2))))))).(\lambda (b: B).(\lambda (_: (not (eq B b Void))).(\lambda (u0: 
T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead c1 (Bind Void) u0) (CHead d1 
(Flat f) u1))).(let H5 \def (eq_ind C (CHead c1 (Bind Void) u0) (\lambda (ee: 
C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow 
False | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) 
with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) I (CHead d1 
(Flat f) u1) H4) in (False_ind (ex2_2 C T (\lambda (d2: C).(\lambda (u3: 
T).(eq C (CHead c2 (Bind b) u2) (CHead d2 (Flat f) u3)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d1 d2)))) H5))))))))))) (\lambda (c1: C).(\lambda 
(c2: C).(\lambda (_: (csuba g c1 c2)).(\lambda (_: (((eq C c1 (CHead d1 (Flat 
f) u1)) \to (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c2 (CHead d2 
(Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d1 
d2))))))).(\lambda (t: T).(\lambda (a: A).(\lambda (_: (arity g c1 t (asucc g 
a))).(\lambda (u: T).(\lambda (_: (arity g c2 u a)).(\lambda (H5: (eq C 
(CHead c1 (Bind Abst) t) (CHead d1 (Flat f) u1))).(let H6 \def (eq_ind C 
(CHead c1 (Bind Abst) t) (\lambda (ee: C).(match ee in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match 
k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | (Flat 
_) \Rightarrow False])])) I (CHead d1 (Flat f) u1) H5) in (False_ind (ex2_2 C 
T (\lambda (d2: C).(\lambda (u2: T).(eq C (CHead c2 (Bind Abbr) u) (CHead d2 
(Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d1 d2)))) 
H6)))))))))))) y c H0))) H)))))).
(* COMMENTS
Initial nodes: 1183
END *)

theorem csuba_gen_bind:
 \forall (g: G).(\forall (b1: B).(\forall (e1: C).(\forall (c2: C).(\forall 
(v1: T).((csuba g (CHead e1 (Bind b1) v1) c2) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e1 e2))))))))))
\def
 \lambda (g: G).(\lambda (b1: B).(\lambda (e1: C).(\lambda (c2: C).(\lambda 
(v1: T).(\lambda (H: (csuba g (CHead e1 (Bind b1) v1) c2)).(insert_eq C 
(CHead e1 (Bind b1) v1) (\lambda (c: C).(csuba g c c2)) (\lambda (_: 
C).(ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csuba g e1 e2)))))) (\lambda (y: C).(\lambda (H0: (csuba g y 
c2)).(csuba_ind g (\lambda (c: C).(\lambda (c0: C).((eq C c (CHead e1 (Bind 
b1) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: 
T).(eq C c0 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csuba g e1 e2)))))))) (\lambda (n: nat).(\lambda (H1: (eq 
C (CSort n) (CHead e1 (Bind b1) v1))).(let H2 \def (eq_ind C (CSort n) 
(\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow True | (CHead _ _ _) \Rightarrow False])) I (CHead e1 (Bind b1) 
v1) H1) in (False_ind (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda 
(v2: T).(eq C (CSort n) (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda 
(e2: C).(\lambda (_: T).(csuba g e1 e2))))) H2)))) (\lambda (c1: C).(\lambda 
(c3: C).(\lambda (H1: (csuba g c1 c3)).(\lambda (H2: (((eq C c1 (CHead e1 
(Bind b1) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda 
(v2: T).(eq C c3 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csuba g e1 e2)))))))).(\lambda (k: K).(\lambda (u: 
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
T).(csuba g e1 e2)))))) (eq_ind_r K (Bind b1) (\lambda (k0: K).(ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c3 k0 v1) 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csuba g e1 e2)))))) (let H9 \def (eq_ind C c1 (\lambda (c: C).((eq C c 
(CHead e1 (Bind b1) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: 
C).(\lambda (v2: T).(eq C c3 (CHead e2 (Bind b2) v2))))) (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csuba g e1 e2))))))) H2 e1 H8) in (let 
H10 \def (eq_ind C c1 (\lambda (c: C).(csuba g c c3)) H1 e1 H8) in 
(ex2_3_intro B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C 
(CHead c3 (Bind b1) v1) (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda 
(e2: C).(\lambda (_: T).(csuba g e1 e2)))) b1 c3 v1 (refl_equal C (CHead c3 
(Bind b1) v1)) H10))) k H7) u H6)))) H5)) H4))))))))) (\lambda (c1: 
C).(\lambda (c3: C).(\lambda (H1: (csuba g c1 c3)).(\lambda (H2: (((eq C c1 
(CHead e1 (Bind b1) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: 
C).(\lambda (v2: T).(eq C c3 (CHead e2 (Bind b2) v2))))) (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csuba g e1 e2)))))))).(\lambda (b: 
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
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e1 e2))))))) H2 e1 
H9) in (let H11 \def (eq_ind C c1 (\lambda (c: C).(csuba g c c3)) H1 e1 H9) 
in (let H12 \def (eq_ind_r B b1 (\lambda (b0: B).((eq C e1 (CHead e1 (Bind 
b0) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: 
T).(eq C c3 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csuba g e1 e2))))))) H10 Void H8) in (ex2_3_intro B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c3 (Bind b) 
u2) (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csuba g e1 e2)))) b c3 u2 (refl_equal C (CHead c3 (Bind b) u2)) 
H11))))))) H6)) H5))))))))))) (\lambda (c1: C).(\lambda (c3: C).(\lambda (H1: 
(csuba g c1 c3)).(\lambda (H2: (((eq C c1 (CHead e1 (Bind b1) v1)) \to (ex2_3 
B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c3 (CHead e2 
(Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g 
e1 e2)))))))).(\lambda (t: T).(\lambda (a: A).(\lambda (H3: (arity g c1 t 
(asucc g a))).(\lambda (u: T).(\lambda (_: (arity g c3 u a)).(\lambda (H5: 
(eq C (CHead c1 (Bind Abst) t) (CHead e1 (Bind b1) v1))).(let H6 \def 
(f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) (CHead c1 (Bind 
Abst) t) (CHead e1 (Bind b1) v1) H5) in ((let H7 \def (f_equal C B (\lambda 
(e: C).(match e in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow 
Abst | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).B) with 
[(Bind b) \Rightarrow b | (Flat _) \Rightarrow Abst])])) (CHead c1 (Bind 
Abst) t) (CHead e1 (Bind b1) v1) H5) in ((let H8 \def (f_equal C T (\lambda 
(e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow t 
| (CHead _ _ t0) \Rightarrow t0])) (CHead c1 (Bind Abst) t) (CHead e1 (Bind 
b1) v1) H5) in (\lambda (H9: (eq B Abst b1)).(\lambda (H10: (eq C c1 
e1)).(let H11 \def (eq_ind T t (\lambda (t0: T).(arity g c1 t0 (asucc g a))) 
H3 v1 H8) in (let H12 \def (eq_ind C c1 (\lambda (c: C).(arity g c v1 (asucc 
g a))) H11 e1 H10) in (let H13 \def (eq_ind C c1 (\lambda (c: C).((eq C c 
(CHead e1 (Bind b1) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: 
C).(\lambda (v2: T).(eq C c3 (CHead e2 (Bind b2) v2))))) (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csuba g e1 e2))))))) H2 e1 H10) in (let 
H14 \def (eq_ind C c1 (\lambda (c: C).(csuba g c c3)) H1 e1 H10) in (let H15 
\def (eq_ind_r B b1 (\lambda (b: B).((eq C e1 (CHead e1 (Bind b) v1)) \to 
(ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c3 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csuba g e1 e2))))))) H13 Abst H9) in (ex2_3_intro B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c3 (Bind Abbr) u) (CHead e2 
(Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g 
e1 e2)))) Abbr c3 u (refl_equal C (CHead c3 (Bind Abbr) u)) H14))))))))) H7)) 
H6)))))))))))) y c2 H0))) H)))))).
(* COMMENTS
Initial nodes: 1889
END *)

theorem csuba_gen_abst_rev:
 \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u: T).((csuba g c 
(CHead d1 (Bind Abst) u)) \to (or (ex2 C (\lambda (d2: C).(eq C c (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(eq C c (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))))))))
\def
 \lambda (g: G).(\lambda (d1: C).(\lambda (c: C).(\lambda (u: T).(\lambda (H: 
(csuba g c (CHead d1 (Bind Abst) u))).(insert_eq C (CHead d1 (Bind Abst) u) 
(\lambda (c0: C).(csuba g c c0)) (\lambda (_: C).(or (ex2 C (\lambda (d2: 
C).(eq C c (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))) (\lambda (y: 
C).(\lambda (H0: (csuba g c y)).(csuba_ind g (\lambda (c0: C).(\lambda (c1: 
C).((eq C c1 (CHead d1 (Bind Abst) u)) \to (or (ex2 C (\lambda (d2: C).(eq C 
c0 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(eq C c0 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))))) (\lambda (n: 
nat).(\lambda (H1: (eq C (CSort n) (CHead d1 (Bind Abst) u))).(let H2 \def 
(eq_ind C (CSort n) (\lambda (ee: C).(match ee in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow 
False])) I (CHead d1 (Bind Abst) u) H1) in (False_ind (or (ex2 C (\lambda 
(d2: C).(eq C (CSort n) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g 
d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C (CSort n) (CHead 
d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) 
H2)))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (H1: (csuba g c1 
c2)).(\lambda (H2: (((eq C c2 (CHead d1 (Bind Abst) u)) \to (or (ex2 C 
(\lambda (d2: C).(eq C c1 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba 
g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c1 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))))))).(\lambda (k: K).(\lambda (u0: T).(\lambda (H3: (eq C (CHead c2 k 
u0) (CHead d1 (Bind Abst) u))).(let H4 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c2 | 
(CHead c0 _ _) \Rightarrow c0])) (CHead c2 k u0) (CHead d1 (Bind Abst) u) H3) 
in ((let H5 \def (f_equal C K (\lambda (e: C).(match e in C return (\lambda 
(_: C).K) with [(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) 
(CHead c2 k u0) (CHead d1 (Bind Abst) u) H3) in ((let H6 \def (f_equal C T 
(\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) (CHead c2 k u0) (CHead d1 
(Bind Abst) u) H3) in (\lambda (H7: (eq K k (Bind Abst))).(\lambda (H8: (eq C 
c2 d1)).(eq_ind_r T u (\lambda (t: T).(or (ex2 C (\lambda (d2: C).(eq C 
(CHead c1 k t) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C (CHead c1 k t) (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))) 
(eq_ind_r K (Bind Abst) (\lambda (k0: K).(or (ex2 C (\lambda (d2: C).(eq C 
(CHead c1 k0 u) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C (CHead c1 k0 u) (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))) (let 
H9 \def (eq_ind C c2 (\lambda (c0: C).((eq C c0 (CHead d1 (Bind Abst) u)) \to 
(or (ex2 C (\lambda (d2: C).(eq C c1 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c1 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))))) H2 d1 H8) in (let H10 \def (eq_ind C c2 (\lambda (c0: C).(csuba g 
c1 c0)) H1 d1 H8) in (or_introl (ex2 C (\lambda (d2: C).(eq C (CHead c1 (Bind 
Abst) u) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(eq C (CHead c1 (Bind Abst) u) (CHead 
d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) 
(ex_intro2 C (\lambda (d2: C).(eq C (CHead c1 (Bind Abst) u) (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) c1 (refl_equal C (CHead c1 (Bind 
Abst) u)) H10)))) k H7) u0 H6)))) H5)) H4))))))))) (\lambda (c1: C).(\lambda 
(c2: C).(\lambda (H1: (csuba g c1 c2)).(\lambda (H2: (((eq C c2 (CHead d1 
(Bind Abst) u)) \to (or (ex2 C (\lambda (d2: C).(eq C c1 (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(eq C c1 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))))))).(\lambda (b: B).(\lambda (H3: (not 
(eq B b Void))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead 
c2 (Bind b) u2) (CHead d1 (Bind Abst) u))).(let H5 \def (f_equal C C (\lambda 
(e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c2 
| (CHead c0 _ _) \Rightarrow c0])) (CHead c2 (Bind b) u2) (CHead d1 (Bind 
Abst) u) H4) in ((let H6 \def (f_equal C B (\lambda (e: C).(match e in C 
return (\lambda (_: C).B) with [(CSort _) \Rightarrow b | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow b])])) (CHead c2 (Bind b) u2) (CHead d1 
(Bind Abst) u) H4) in ((let H7 \def (f_equal C T (\lambda (e: C).(match e in 
C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u2 | (CHead _ _ t) 
\Rightarrow t])) (CHead c2 (Bind b) u2) (CHead d1 (Bind Abst) u) H4) in 
(\lambda (H8: (eq B b Abst)).(\lambda (H9: (eq C c2 d1)).(let H10 \def 
(eq_ind B b (\lambda (b0: B).(not (eq B b0 Void))) H3 Abst H8) in (let H11 
\def (eq_ind C c2 (\lambda (c0: C).((eq C c0 (CHead d1 (Bind Abst) u)) \to 
(or (ex2 C (\lambda (d2: C).(eq C c1 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u3: T).(eq C c1 
(CHead d2 (Bind Void) u3)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))))) H2 d1 H9) in (let H12 \def (eq_ind C c2 (\lambda (c0: C).(csuba g 
c1 c0)) H1 d1 H9) in (or_intror (ex2 C (\lambda (d2: C).(eq C (CHead c1 (Bind 
Void) u1) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u3: T).(eq C (CHead c1 (Bind Void) u1) 
(CHead d2 (Bind Void) u3)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))) (ex2_2_intro C T (\lambda (d2: C).(\lambda (u3: T).(eq C (CHead c1 
(Bind Void) u1) (CHead d2 (Bind Void) u3)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))) c1 u1 (refl_equal C (CHead c1 (Bind Void) u1)) 
H12)))))))) H6)) H5))))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (_: 
(csuba g c1 c2)).(\lambda (_: (((eq C c2 (CHead d1 (Bind Abst) u)) \to (or 
(ex2 C (\lambda (d2: C).(eq C c1 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c1 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))))))).(\lambda (t: T).(\lambda (a: A).(\lambda (_: (arity g c1 t (asucc 
g a))).(\lambda (u0: T).(\lambda (_: (arity g c2 u0 a)).(\lambda (H5: (eq C 
(CHead c2 (Bind Abbr) u0) (CHead d1 (Bind Abst) u))).(let H6 \def (eq_ind C 
(CHead c2 (Bind Abbr) u0) (\lambda (ee: C).(match ee in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match 
k in K return (\lambda (_: K).Prop) with [(Bind b) \Rightarrow (match b in B 
return (\lambda (_: B).Prop) with [Abbr \Rightarrow True | Abst \Rightarrow 
False | Void \Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead 
d1 (Bind Abst) u) H5) in (False_ind (or (ex2 C (\lambda (d2: C).(eq C (CHead 
c1 (Bind Abst) t) (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 
d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C (CHead c1 (Bind 
Abst) t) (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba 
g d2 d1))))) H6)))))))))))) c y H0))) H))))).
(* COMMENTS
Initial nodes: 1980
END *)

theorem csuba_gen_void_rev:
 \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u: T).((csuba g c 
(CHead d1 (Bind Void) u)) \to (ex2 C (\lambda (d2: C).(eq C c (CHead d2 (Bind 
Void) u))) (\lambda (d2: C).(csuba g d2 d1)))))))
\def
 \lambda (g: G).(\lambda (d1: C).(\lambda (c: C).(\lambda (u: T).(\lambda (H: 
(csuba g c (CHead d1 (Bind Void) u))).(insert_eq C (CHead d1 (Bind Void) u) 
(\lambda (c0: C).(csuba g c c0)) (\lambda (_: C).(ex2 C (\lambda (d2: C).(eq 
C c (CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d2 d1)))) (\lambda 
(y: C).(\lambda (H0: (csuba g c y)).(csuba_ind g (\lambda (c0: C).(\lambda 
(c1: C).((eq C c1 (CHead d1 (Bind Void) u)) \to (ex2 C (\lambda (d2: C).(eq C 
c0 (CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d2 d1)))))) (\lambda 
(n: nat).(\lambda (H1: (eq C (CSort n) (CHead d1 (Bind Void) u))).(let H2 
\def (eq_ind C (CSort n) (\lambda (ee: C).(match ee in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow 
False])) I (CHead d1 (Bind Void) u) H1) in (False_ind (ex2 C (\lambda (d2: 
C).(eq C (CSort n) (CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d2 
d1))) H2)))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (H1: (csuba g c1 
c2)).(\lambda (H2: (((eq C c2 (CHead d1 (Bind Void) u)) \to (ex2 C (\lambda 
(d2: C).(eq C c1 (CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d2 
d1)))))).(\lambda (k: K).(\lambda (u0: T).(\lambda (H3: (eq C (CHead c2 k u0) 
(CHead d1 (Bind Void) u))).(let H4 \def (f_equal C C (\lambda (e: C).(match e 
in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c2 | (CHead c0 _ 
_) \Rightarrow c0])) (CHead c2 k u0) (CHead d1 (Bind Void) u) H3) in ((let H5 
\def (f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) 
with [(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) (CHead c2 k 
u0) (CHead d1 (Bind Void) u) H3) in ((let H6 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | 
(CHead _ _ t) \Rightarrow t])) (CHead c2 k u0) (CHead d1 (Bind Void) u) H3) 
in (\lambda (H7: (eq K k (Bind Void))).(\lambda (H8: (eq C c2 d1)).(eq_ind_r 
T u (\lambda (t: T).(ex2 C (\lambda (d2: C).(eq C (CHead c1 k t) (CHead d2 
(Bind Void) u))) (\lambda (d2: C).(csuba g d2 d1)))) (eq_ind_r K (Bind Void) 
(\lambda (k0: K).(ex2 C (\lambda (d2: C).(eq C (CHead c1 k0 u) (CHead d2 
(Bind Void) u))) (\lambda (d2: C).(csuba g d2 d1)))) (let H9 \def (eq_ind C 
c2 (\lambda (c0: C).((eq C c0 (CHead d1 (Bind Void) u)) \to (ex2 C (\lambda 
(d2: C).(eq C c1 (CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d2 
d1))))) H2 d1 H8) in (let H10 \def (eq_ind C c2 (\lambda (c0: C).(csuba g c1 
c0)) H1 d1 H8) in (ex_intro2 C (\lambda (d2: C).(eq C (CHead c1 (Bind Void) 
u) (CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d2 d1)) c1 
(refl_equal C (CHead c1 (Bind Void) u)) H10))) k H7) u0 H6)))) H5)) 
H4))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (H1: (csuba g c1 
c2)).(\lambda (H2: (((eq C c2 (CHead d1 (Bind Void) u)) \to (ex2 C (\lambda 
(d2: C).(eq C c1 (CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d2 
d1)))))).(\lambda (b: B).(\lambda (H3: (not (eq B b Void))).(\lambda (u1: 
T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead c2 (Bind b) u2) (CHead d1 
(Bind Void) u))).(let H5 \def (f_equal C C (\lambda (e: C).(match e in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow c2 | (CHead c0 _ _) 
\Rightarrow c0])) (CHead c2 (Bind b) u2) (CHead d1 (Bind Void) u) H4) in 
((let H6 \def (f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: 
C).B) with [(CSort _) \Rightarrow b | (CHead _ k _) \Rightarrow (match k in K 
return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) 
\Rightarrow b])])) (CHead c2 (Bind b) u2) (CHead d1 (Bind Void) u) H4) in 
((let H7 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: 
C).T) with [(CSort _) \Rightarrow u2 | (CHead _ _ t) \Rightarrow t])) (CHead 
c2 (Bind b) u2) (CHead d1 (Bind Void) u) H4) in (\lambda (H8: (eq B b 
Void)).(\lambda (H9: (eq C c2 d1)).(let H10 \def (eq_ind B b (\lambda (b0: 
B).(not (eq B b0 Void))) H3 Void H8) in (let H11 \def (eq_ind C c2 (\lambda 
(c0: C).((eq C c0 (CHead d1 (Bind Void) u)) \to (ex2 C (\lambda (d2: C).(eq C 
c1 (CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d2 d1))))) H2 d1 H9) 
in (let H12 \def (eq_ind C c2 (\lambda (c0: C).(csuba g c1 c0)) H1 d1 H9) in 
(let H13 \def (match (H10 (refl_equal B Void)) in False return (\lambda (_: 
False).(ex2 C (\lambda (d2: C).(eq C (CHead c1 (Bind Void) u1) (CHead d2 
(Bind Void) u))) (\lambda (d2: C).(csuba g d2 d1)))) with []) in H13))))))) 
H6)) H5))))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (_: (csuba g c1 
c2)).(\lambda (_: (((eq C c2 (CHead d1 (Bind Void) u)) \to (ex2 C (\lambda 
(d2: C).(eq C c1 (CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d2 
d1)))))).(\lambda (t: T).(\lambda (a: A).(\lambda (_: (arity g c1 t (asucc g 
a))).(\lambda (u0: T).(\lambda (_: (arity g c2 u0 a)).(\lambda (H5: (eq C 
(CHead c2 (Bind Abbr) u0) (CHead d1 (Bind Void) u))).(let H6 \def (eq_ind C 
(CHead c2 (Bind Abbr) u0) (\lambda (ee: C).(match ee in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match 
k in K return (\lambda (_: K).Prop) with [(Bind b) \Rightarrow (match b in B 
return (\lambda (_: B).Prop) with [Abbr \Rightarrow True | Abst \Rightarrow 
False | Void \Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead 
d1 (Bind Void) u) H5) in (False_ind (ex2 C (\lambda (d2: C).(eq C (CHead c1 
(Bind Abst) t) (CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d2 d1))) 
H6)))))))))))) c y H0))) H))))).
(* COMMENTS
Initial nodes: 1326
END *)

theorem csuba_gen_abbr_rev:
 \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u1: T).((csuba g c 
(CHead d1 (Bind Abbr) u1)) \to (or3 (ex2 C (\lambda (d2: C).(eq C c (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))))))
\def
 \lambda (g: G).(\lambda (d1: C).(\lambda (c: C).(\lambda (u1: T).(\lambda 
(H: (csuba g c (CHead d1 (Bind Abbr) u1))).(insert_eq C (CHead d1 (Bind Abbr) 
u1) (\lambda (c0: C).(csuba g c c0)) (\lambda (_: C).(or3 (ex2 C (\lambda 
(d2: C).(eq C c (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq 
C c (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))))) (\lambda (y: C).(\lambda (H0: (csuba g c y)).(csuba_ind g (\lambda 
(c0: C).(\lambda (c1: C).((eq C c1 (CHead d1 (Bind Abbr) u1)) \to (or3 (ex2 C 
(\lambda (d2: C).(eq C c0 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba 
g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq 
C c0 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq 
C c0 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g 
d2 d1)))))))) (\lambda (n: nat).(\lambda (H1: (eq C (CSort n) (CHead d1 (Bind 
Abbr) u1))).(let H2 \def (eq_ind C (CSort n) (\lambda (ee: C).(match ee in C 
return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) 
\Rightarrow False])) I (CHead d1 (Bind Abbr) u1) H1) in (False_ind (or3 (ex2 
C (\lambda (d2: C).(eq C (CSort n) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(eq C (CSort n) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(eq C (CSort n) (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) H2)))) (\lambda 
(c1: C).(\lambda (c2: C).(\lambda (H1: (csuba g c1 c2)).(\lambda (H2: (((eq C 
c2 (CHead d1 (Bind Abbr) u1)) \to (or3 (ex2 C (\lambda (d2: C).(eq C c1 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c1 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c1 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))))))).(\lambda (k: K).(\lambda (u: T).(\lambda (H3: (eq C (CHead c2 k u) 
(CHead d1 (Bind Abbr) u1))).(let H4 \def (f_equal C C (\lambda (e: C).(match 
e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c2 | (CHead c0 _ 
_) \Rightarrow c0])) (CHead c2 k u) (CHead d1 (Bind Abbr) u1) H3) in ((let H5 
\def (f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) 
with [(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) (CHead c2 k 
u) (CHead d1 (Bind Abbr) u1) H3) in ((let H6 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | 
(CHead _ _ t) \Rightarrow t])) (CHead c2 k u) (CHead d1 (Bind Abbr) u1) H3) 
in (\lambda (H7: (eq K k (Bind Abbr))).(\lambda (H8: (eq C c2 d1)).(eq_ind_r 
T u1 (\lambda (t: T).(or3 (ex2 C (\lambda (d2: C).(eq C (CHead c1 k t) (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C (CHead c1 k t) (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C (CHead c1 k t) 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))))) (eq_ind_r K (Bind Abbr) (\lambda (k0: K).(or3 (ex2 C (\lambda (d2: 
C).(eq C (CHead c1 k0 u1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba 
g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq 
C (CHead c1 k0 u1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda 
(_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(eq C (CHead c1 k0 u1) (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))) (let H9 \def (eq_ind C 
c2 (\lambda (c0: C).((eq C c0 (CHead d1 (Bind Abbr) u1)) \to (or3 (ex2 C 
(\lambda (d2: C).(eq C c1 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba 
g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq 
C c1 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq 
C c1 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g 
d2 d1))))))) H2 d1 H8) in (let H10 \def (eq_ind C c2 (\lambda (c0: C).(csuba 
g c1 c0)) H1 d1 H8) in (or3_intro0 (ex2 C (\lambda (d2: C).(eq C (CHead c1 
(Bind Abbr) u1) (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C 
(CHead c1 (Bind Abbr) u1) (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(eq C (CHead c1 (Bind Abbr) u1) (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) 
(ex_intro2 C (\lambda (d2: C).(eq C (CHead c1 (Bind Abbr) u1) (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) c1 (refl_equal C (CHead c1 
(Bind Abbr) u1)) H10)))) k H7) u H6)))) H5)) H4))))))))) (\lambda (c1: 
C).(\lambda (c2: C).(\lambda (H1: (csuba g c1 c2)).(\lambda (H2: (((eq C c2 
(CHead d1 (Bind Abbr) u1)) \to (or3 (ex2 C (\lambda (d2: C).(eq C c1 (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c1 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c1 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))))).(\lambda (b: 
B).(\lambda (H3: (not (eq B b Void))).(\lambda (u0: T).(\lambda (u2: 
T).(\lambda (H4: (eq C (CHead c2 (Bind b) u2) (CHead d1 (Bind Abbr) 
u1))).(let H5 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow c2 | (CHead c0 _ _) \Rightarrow c0])) 
(CHead c2 (Bind b) u2) (CHead d1 (Bind Abbr) u1) H4) in ((let H6 \def 
(f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow b | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow 
b])])) (CHead c2 (Bind b) u2) (CHead d1 (Bind Abbr) u1) H4) in ((let H7 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u2 | (CHead _ _ t) \Rightarrow t])) (CHead c2 (Bind b) 
u2) (CHead d1 (Bind Abbr) u1) H4) in (\lambda (H8: (eq B b Abbr)).(\lambda 
(H9: (eq C c2 d1)).(let H10 \def (eq_ind B b (\lambda (b0: B).(not (eq B b0 
Void))) H3 Abbr H8) in (let H11 \def (eq_ind C c2 (\lambda (c0: C).((eq C c0 
(CHead d1 (Bind Abbr) u1)) \to (or3 (ex2 C (\lambda (d2: C).(eq C c1 (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u3: T).(\lambda (_: A).(eq C c1 (CHead d2 (Bind Abst) 
u3))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u3: T).(\lambda (a: A).(arity g d2 u3 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u3: T).(eq C c1 (CHead d2 (Bind Void) 
u3)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))))) H2 d1 H9) in 
(let H12 \def (eq_ind C c2 (\lambda (c0: C).(csuba g c1 c0)) H1 d1 H9) in 
(or3_intro2 (ex2 C (\lambda (d2: C).(eq C (CHead c1 (Bind Void) u0) (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u3: T).(\lambda (_: A).(eq C (CHead c1 (Bind Void) u0) 
(CHead d2 (Bind Abst) u3))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u3: T).(\lambda (a: 
A).(arity g d2 u3 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u3: T).(eq 
C (CHead c1 (Bind Void) u0) (CHead d2 (Bind Void) u3)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda (d2: 
C).(\lambda (u3: T).(eq C (CHead c1 (Bind Void) u0) (CHead d2 (Bind Void) 
u3)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) c1 u0 (refl_equal C 
(CHead c1 (Bind Void) u0)) H12)))))))) H6)) H5))))))))))) (\lambda (c1: 
C).(\lambda (c2: C).(\lambda (H1: (csuba g c1 c2)).(\lambda (H2: (((eq C c2 
(CHead d1 (Bind Abbr) u1)) \to (or3 (ex2 C (\lambda (d2: C).(eq C c1 (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c1 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c1 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))))).(\lambda (t: 
T).(\lambda (a: A).(\lambda (H3: (arity g c1 t (asucc g a))).(\lambda (u: 
T).(\lambda (H4: (arity g c2 u a)).(\lambda (H5: (eq C (CHead c2 (Bind Abbr) 
u) (CHead d1 (Bind Abbr) u1))).(let H6 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c2 | 
(CHead c0 _ _) \Rightarrow c0])) (CHead c2 (Bind Abbr) u) (CHead d1 (Bind 
Abbr) u1) H5) in ((let H7 \def (f_equal C T (\lambda (e: C).(match e in C 
return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t0) 
\Rightarrow t0])) (CHead c2 (Bind Abbr) u) (CHead d1 (Bind Abbr) u1) H5) in 
(\lambda (H8: (eq C c2 d1)).(let H9 \def (eq_ind T u (\lambda (t0: T).(arity 
g c2 t0 a)) H4 u1 H7) in (let H10 \def (eq_ind C c2 (\lambda (c0: C).(arity g 
c0 u1 a)) H9 d1 H8) in (let H11 \def (eq_ind C c2 (\lambda (c0: C).((eq C c0 
(CHead d1 (Bind Abbr) u1)) \to (or3 (ex2 C (\lambda (d2: C).(eq C c1 (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c1 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a0: A).(arity g d2 u2 (asucc g 
a0))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(arity g d1 u1 
a0))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c1 (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))))) H2 d1 H8) 
in (let H12 \def (eq_ind C c2 (\lambda (c0: C).(csuba g c1 c0)) H1 d1 H8) in 
(or3_intro1 (ex2 C (\lambda (d2: C).(eq C (CHead c1 (Bind Abst) t) (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C (CHead c1 (Bind Abst) t) 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a0: 
A).(arity g d2 u2 (asucc g a0))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a0: A).(arity g d1 u1 a0))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(eq C (CHead c1 (Bind Abst) t) (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) (ex4_3_intro C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(eq C (CHead c1 (Bind Abst) t) (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a0: A).(arity g d2 u2 
(asucc g a0))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(arity g d1 
u1 a0)))) c1 t a (refl_equal C (CHead c1 (Bind Abst) t)) H12 H3 H10)))))))) 
H6)))))))))))) c y H0))) H))))).
(* COMMENTS
Initial nodes: 3459
END *)

theorem csuba_gen_flat_rev:
 \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u1: T).(\forall 
(f: F).((csuba g c (CHead d1 (Flat f) u1)) \to (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(eq C c (CHead d2 (Flat f) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))))))))
\def
 \lambda (g: G).(\lambda (d1: C).(\lambda (c: C).(\lambda (u1: T).(\lambda 
(f: F).(\lambda (H: (csuba g c (CHead d1 (Flat f) u1))).(insert_eq C (CHead 
d1 (Flat f) u1) (\lambda (c0: C).(csuba g c c0)) (\lambda (_: C).(ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(eq C c (CHead d2 (Flat f) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (y: C).(\lambda (H0: 
(csuba g c y)).(csuba_ind g (\lambda (c0: C).(\lambda (c1: C).((eq C c1 
(CHead d1 (Flat f) u1)) \to (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq 
C c0 (CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))))) (\lambda (n: nat).(\lambda (H1: (eq C (CSort n) (CHead d1 (Flat f) 
u1))).(let H2 \def (eq_ind C (CSort n) (\lambda (ee: C).(match ee in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) 
\Rightarrow False])) I (CHead d1 (Flat f) u1) H1) in (False_ind (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(eq C (CSort n) (CHead d2 (Flat f) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) H2)))) (\lambda (c1: 
C).(\lambda (c2: C).(\lambda (H1: (csuba g c1 c2)).(\lambda (H2: (((eq C c2 
(CHead d1 (Flat f) u1)) \to (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq 
C c1 (CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))))).(\lambda (k: K).(\lambda (u: T).(\lambda (H3: (eq C (CHead c2 k u) 
(CHead d1 (Flat f) u1))).(let H4 \def (f_equal C C (\lambda (e: C).(match e 
in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c2 | (CHead c0 _ 
_) \Rightarrow c0])) (CHead c2 k u) (CHead d1 (Flat f) u1) H3) in ((let H5 
\def (f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) 
with [(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) (CHead c2 k 
u) (CHead d1 (Flat f) u1) H3) in ((let H6 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | 
(CHead _ _ t) \Rightarrow t])) (CHead c2 k u) (CHead d1 (Flat f) u1) H3) in 
(\lambda (H7: (eq K k (Flat f))).(\lambda (H8: (eq C c2 d1)).(eq_ind_r T u1 
(\lambda (t: T).(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C (CHead c1 
k t) (CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))) (eq_ind_r K (Flat f) (\lambda (k0: K).(ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(eq C (CHead c1 k0 u1) (CHead d2 (Flat f) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1))))) (let H9 \def (eq_ind C c2 
(\lambda (c0: C).((eq C c0 (CHead d1 (Flat f) u1)) \to (ex2_2 C T (\lambda 
(d2: C).(\lambda (u2: T).(eq C c1 (CHead d2 (Flat f) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))))) H2 d1 H8) in (let H10 \def (eq_ind C 
c2 (\lambda (c0: C).(csuba g c1 c0)) H1 d1 H8) in (ex2_2_intro C T (\lambda 
(d2: C).(\lambda (u2: T).(eq C (CHead c1 (Flat f) u1) (CHead d2 (Flat f) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) c1 u1 (refl_equal C 
(CHead c1 (Flat f) u1)) H10))) k H7) u H6)))) H5)) H4))))))))) (\lambda (c1: 
C).(\lambda (c2: C).(\lambda (_: (csuba g c1 c2)).(\lambda (_: (((eq C c2 
(CHead d1 (Flat f) u1)) \to (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq 
C c1 (CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))))).(\lambda (b: B).(\lambda (_: (not (eq B b Void))).(\lambda (u0: 
T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead c2 (Bind b) u2) (CHead d1 
(Flat f) u1))).(let H5 \def (eq_ind C (CHead c2 (Bind b) u2) (\lambda (ee: 
C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow 
False | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) 
with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) I (CHead d1 
(Flat f) u1) H4) in (False_ind (ex2_2 C T (\lambda (d2: C).(\lambda (u3: 
T).(eq C (CHead c1 (Bind Void) u0) (CHead d2 (Flat f) u3)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) H5))))))))))) (\lambda (c1: C).(\lambda 
(c2: C).(\lambda (_: (csuba g c1 c2)).(\lambda (_: (((eq C c2 (CHead d1 (Flat 
f) u1)) \to (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c1 (CHead d2 
(Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))))).(\lambda (t: T).(\lambda (a: A).(\lambda (_: (arity g c1 t (asucc g 
a))).(\lambda (u: T).(\lambda (_: (arity g c2 u a)).(\lambda (H5: (eq C 
(CHead c2 (Bind Abbr) u) (CHead d1 (Flat f) u1))).(let H6 \def (eq_ind C 
(CHead c2 (Bind Abbr) u) (\lambda (ee: C).(match ee in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match 
k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | (Flat 
_) \Rightarrow False])])) I (CHead d1 (Flat f) u1) H5) in (False_ind (ex2_2 C 
T (\lambda (d2: C).(\lambda (u2: T).(eq C (CHead c1 (Bind Abst) t) (CHead d2 
(Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) 
H6)))))))))))) c y H0))) H)))))).
(* COMMENTS
Initial nodes: 1183
END *)

theorem csuba_gen_bind_rev:
 \forall (g: G).(\forall (b1: B).(\forall (e1: C).(\forall (c2: C).(\forall 
(v1: T).((csuba g c2 (CHead e1 (Bind b1) v1)) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 e1))))))))))
\def
 \lambda (g: G).(\lambda (b1: B).(\lambda (e1: C).(\lambda (c2: C).(\lambda 
(v1: T).(\lambda (H: (csuba g c2 (CHead e1 (Bind b1) v1))).(insert_eq C 
(CHead e1 (Bind b1) v1) (\lambda (c: C).(csuba g c2 c)) (\lambda (_: 
C).(ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csuba g e2 e1)))))) (\lambda (y: C).(\lambda (H0: (csuba g c2 
y)).(csuba_ind g (\lambda (c: C).(\lambda (c0: C).((eq C c0 (CHead e1 (Bind 
b1) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: 
T).(eq C c (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csuba g e2 e1)))))))) (\lambda (n: nat).(\lambda (H1: (eq 
C (CSort n) (CHead e1 (Bind b1) v1))).(let H2 \def (eq_ind C (CSort n) 
(\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow True | (CHead _ _ _) \Rightarrow False])) I (CHead e1 (Bind b1) 
v1) H1) in (False_ind (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda 
(v2: T).(eq C (CSort n) (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda 
(e2: C).(\lambda (_: T).(csuba g e2 e1))))) H2)))) (\lambda (c1: C).(\lambda 
(c3: C).(\lambda (H1: (csuba g c1 c3)).(\lambda (H2: (((eq C c3 (CHead e1 
(Bind b1) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda 
(v2: T).(eq C c1 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csuba g e2 e1)))))))).(\lambda (k: K).(\lambda (u: 
T).(\lambda (H3: (eq C (CHead c3 k u) (CHead e1 (Bind b1) v1))).(let H4 \def 
(f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c3 | (CHead c _ _) \Rightarrow c])) (CHead c3 k u) 
(CHead e1 (Bind b1) v1) H3) in ((let H5 \def (f_equal C K (\lambda (e: 
C).(match e in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k | 
(CHead _ k0 _) \Rightarrow k0])) (CHead c3 k u) (CHead e1 (Bind b1) v1) H3) 
in ((let H6 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda 
(_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) 
(CHead c3 k u) (CHead e1 (Bind b1) v1) H3) in (\lambda (H7: (eq K k (Bind 
b1))).(\lambda (H8: (eq C c3 e1)).(eq_ind_r T v1 (\lambda (t: T).(ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c1 k t) 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csuba g e2 e1)))))) (eq_ind_r K (Bind b1) (\lambda (k0: K).(ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c1 k0 v1) 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csuba g e2 e1)))))) (let H9 \def (eq_ind C c3 (\lambda (c: C).((eq C c 
(CHead e1 (Bind b1) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: 
C).(\lambda (v2: T).(eq C c1 (CHead e2 (Bind b2) v2))))) (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 e1))))))) H2 e1 H8) in (let 
H10 \def (eq_ind C c3 (\lambda (c: C).(csuba g c1 c)) H1 e1 H8) in 
(ex2_3_intro B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C 
(CHead c1 (Bind b1) v1) (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda 
(e2: C).(\lambda (_: T).(csuba g e2 e1)))) b1 c1 v1 (refl_equal C (CHead c1 
(Bind b1) v1)) H10))) k H7) u H6)))) H5)) H4))))))))) (\lambda (c1: 
C).(\lambda (c3: C).(\lambda (H1: (csuba g c1 c3)).(\lambda (H2: (((eq C c3 
(CHead e1 (Bind b1) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: 
C).(\lambda (v2: T).(eq C c1 (CHead e2 (Bind b2) v2))))) (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 e1)))))))).(\lambda (b: 
B).(\lambda (H3: (not (eq B b Void))).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (H4: (eq C (CHead c3 (Bind b) u2) (CHead e1 (Bind b1) v1))).(let 
H5 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) 
with [(CSort _) \Rightarrow c3 | (CHead c _ _) \Rightarrow c])) (CHead c3 
(Bind b) u2) (CHead e1 (Bind b1) v1) H4) in ((let H6 \def (f_equal C B 
(\lambda (e: C).(match e in C return (\lambda (_: C).B) with [(CSort _) 
\Rightarrow b | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: 
K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow b])])) (CHead c3 
(Bind b) u2) (CHead e1 (Bind b1) v1) H4) in ((let H7 \def (f_equal C T 
(\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow u2 | (CHead _ _ t) \Rightarrow t])) (CHead c3 (Bind b) u2) (CHead 
e1 (Bind b1) v1) H4) in (\lambda (H8: (eq B b b1)).(\lambda (H9: (eq C c3 
e1)).(let H10 \def (eq_ind B b (\lambda (b0: B).(not (eq B b0 Void))) H3 b1 
H8) in (let H11 \def (eq_ind C c3 (\lambda (c: C).((eq C c (CHead e1 (Bind 
b1) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: 
T).(eq C c1 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csuba g e2 e1))))))) H2 e1 H9) in (let H12 \def (eq_ind C 
c3 (\lambda (c: C).(csuba g c1 c)) H1 e1 H9) in (ex2_3_intro B C T (\lambda 
(b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c1 (Bind Void) u1) 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csuba g e2 e1)))) Void c1 u1 (refl_equal C (CHead c1 (Bind Void) u1)) 
H12))))))) H6)) H5))))))))))) (\lambda (c1: C).(\lambda (c3: C).(\lambda (H1: 
(csuba g c1 c3)).(\lambda (H2: (((eq C c3 (CHead e1 (Bind b1) v1)) \to (ex2_3 
B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c1 (CHead e2 
(Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g 
e2 e1)))))))).(\lambda (t: T).(\lambda (a: A).(\lambda (_: (arity g c1 t 
(asucc g a))).(\lambda (u: T).(\lambda (H4: (arity g c3 u a)).(\lambda (H5: 
(eq C (CHead c3 (Bind Abbr) u) (CHead e1 (Bind b1) v1))).(let H6 \def 
(f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c3 | (CHead c _ _) \Rightarrow c])) (CHead c3 (Bind 
Abbr) u) (CHead e1 (Bind b1) v1) H5) in ((let H7 \def (f_equal C B (\lambda 
(e: C).(match e in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow 
Abbr | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).B) with 
[(Bind b) \Rightarrow b | (Flat _) \Rightarrow Abbr])])) (CHead c3 (Bind 
Abbr) u) (CHead e1 (Bind b1) v1) H5) in ((let H8 \def (f_equal C T (\lambda 
(e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u 
| (CHead _ _ t0) \Rightarrow t0])) (CHead c3 (Bind Abbr) u) (CHead e1 (Bind 
b1) v1) H5) in (\lambda (H9: (eq B Abbr b1)).(\lambda (H10: (eq C c3 
e1)).(let H11 \def (eq_ind T u (\lambda (t0: T).(arity g c3 t0 a)) H4 v1 H8) 
in (let H12 \def (eq_ind C c3 (\lambda (c: C).(arity g c v1 a)) H11 e1 H10) 
in (let H13 \def (eq_ind C c3 (\lambda (c: C).((eq C c (CHead e1 (Bind b1) 
v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq 
C c1 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda 
(_: T).(csuba g e2 e1))))))) H2 e1 H10) in (let H14 \def (eq_ind C c3 
(\lambda (c: C).(csuba g c1 c)) H1 e1 H10) in (let H15 \def (eq_ind_r B b1 
(\lambda (b: B).((eq C e1 (CHead e1 (Bind b) v1)) \to (ex2_3 B C T (\lambda 
(b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c1 (CHead e2 (Bind b2) 
v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 
e1))))))) H13 Abbr H9) in (ex2_3_intro B C T (\lambda (b2: B).(\lambda (e2: 
C).(\lambda (v2: T).(eq C (CHead c1 (Bind Abst) t) (CHead e2 (Bind b2) 
v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 e1)))) 
Abst c1 t (refl_equal C (CHead c1 (Bind Abst) t)) H14))))))))) H7)) 
H6)))))))))))) c2 y H0))) H)))))).
(* COMMENTS
Initial nodes: 1831
END *)

