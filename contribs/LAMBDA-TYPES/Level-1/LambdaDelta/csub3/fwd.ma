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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/csub3/fwd".

include "csub3/defs.ma".

theorem csub3_gen_abbr:
 \forall (g: G).(\forall (e1: C).(\forall (c2: C).(\forall (v: T).((csub3 g 
(CHead e1 (Bind Abbr) v) c2) \to (ex2 C (\lambda (e2: C).(eq C c2 (CHead e2 
(Bind Abbr) v))) (\lambda (e2: C).(csub3 g e1 e2)))))))
\def
 \lambda (g: G).(\lambda (e1: C).(\lambda (c2: C).(\lambda (v: T).(\lambda 
(H: (csub3 g (CHead e1 (Bind Abbr) v) c2)).(let H0 \def (match H in csub3 
return (\lambda (c: C).(\lambda (c0: C).(\lambda (_: (csub3 ? c c0)).((eq C c 
(CHead e1 (Bind Abbr) v)) \to ((eq C c0 c2) \to (ex2 C (\lambda (e2: C).(eq C 
c2 (CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csub3 g e1 e2)))))))) with 
[(csub3_sort n) \Rightarrow (\lambda (H0: (eq C (CSort n) (CHead e1 (Bind 
Abbr) v))).(\lambda (H1: (eq C (CSort n) c2)).((let H2 \def (eq_ind C (CSort 
n) (\lambda (e: C).(match e in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow True | (CHead _ _ _) \Rightarrow False])) I (CHead e1 (Bind Abbr) 
v) H0) in (False_ind ((eq C (CSort n) c2) \to (ex2 C (\lambda (e2: C).(eq C 
c2 (CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csub3 g e1 e2)))) H2)) H1))) 
| (csub3_head c1 c0 H0 k u) \Rightarrow (\lambda (H1: (eq C (CHead c1 k u) 
(CHead e1 (Bind Abbr) v))).(\lambda (H2: (eq C (CHead c0 k u) c2)).((let H3 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead c1 k u) 
(CHead e1 (Bind Abbr) v) H1) in ((let H4 \def (f_equal C K (\lambda (e: 
C).(match e in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k | 
(CHead _ k0 _) \Rightarrow k0])) (CHead c1 k u) (CHead e1 (Bind Abbr) v) H1) 
in ((let H5 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) 
(CHead c1 k u) (CHead e1 (Bind Abbr) v) H1) in (eq_ind C e1 (\lambda (c: 
C).((eq K k (Bind Abbr)) \to ((eq T u v) \to ((eq C (CHead c0 k u) c2) \to 
((csub3 g c c0) \to (ex2 C (\lambda (e2: C).(eq C c2 (CHead e2 (Bind Abbr) 
v))) (\lambda (e2: C).(csub3 g e1 e2)))))))) (\lambda (H6: (eq K k (Bind 
Abbr))).(eq_ind K (Bind Abbr) (\lambda (k0: K).((eq T u v) \to ((eq C (CHead 
c0 k0 u) c2) \to ((csub3 g e1 c0) \to (ex2 C (\lambda (e2: C).(eq C c2 (CHead 
e2 (Bind Abbr) v))) (\lambda (e2: C).(csub3 g e1 e2))))))) (\lambda (H7: (eq 
T u v)).(eq_ind T v (\lambda (t: T).((eq C (CHead c0 (Bind Abbr) t) c2) \to 
((csub3 g e1 c0) \to (ex2 C (\lambda (e2: C).(eq C c2 (CHead e2 (Bind Abbr) 
v))) (\lambda (e2: C).(csub3 g e1 e2)))))) (\lambda (H8: (eq C (CHead c0 
(Bind Abbr) v) c2)).(eq_ind C (CHead c0 (Bind Abbr) v) (\lambda (c: 
C).((csub3 g e1 c0) \to (ex2 C (\lambda (e2: C).(eq C c (CHead e2 (Bind Abbr) 
v))) (\lambda (e2: C).(csub3 g e1 e2))))) (\lambda (H9: (csub3 g e1 c0)).(let 
H10 \def (eq_ind_r C c2 (\lambda (c: C).(csub3 g (CHead e1 (Bind Abbr) v) c)) 
H (CHead c0 (Bind Abbr) v) H8) in (ex_intro2 C (\lambda (e2: C).(eq C (CHead 
c0 (Bind Abbr) v) (CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csub3 g e1 
e2)) c0 (refl_equal C (CHead c0 (Bind Abbr) v)) H9))) c2 H8)) u (sym_eq T u v 
H7))) k (sym_eq K k (Bind Abbr) H6))) c1 (sym_eq C c1 e1 H5))) H4)) H3)) H2 
H0))) | (csub3_void c1 c0 H0 b H1 u1 u2) \Rightarrow (\lambda (H2: (eq C 
(CHead c1 (Bind Void) u1) (CHead e1 (Bind Abbr) v))).(\lambda (H3: (eq C 
(CHead c0 (Bind b) u2) c2)).((let H4 \def (eq_ind C (CHead c1 (Bind Void) u1) 
(\lambda (e: C).(match e in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b0) \Rightarrow (match b0 in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow False | Abst \Rightarrow False | Void 
\Rightarrow True]) | (Flat _) \Rightarrow False])])) I (CHead e1 (Bind Abbr) 
v) H2) in (False_ind ((eq C (CHead c0 (Bind b) u2) c2) \to ((csub3 g c1 c0) 
\to ((not (eq B b Void)) \to (ex2 C (\lambda (e2: C).(eq C c2 (CHead e2 (Bind 
Abbr) v))) (\lambda (e2: C).(csub3 g e1 e2)))))) H4)) H3 H0 H1))) | 
(csub3_abst c1 c0 H0 u t H1) \Rightarrow (\lambda (H2: (eq C (CHead c1 (Bind 
Abst) t) (CHead e1 (Bind Abbr) v))).(\lambda (H3: (eq C (CHead c0 (Bind Abbr) 
u) c2)).((let H4 \def (eq_ind C (CHead c1 (Bind Abst) t) (\lambda (e: 
C).(match e in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow 
False | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) 
with [(Bind b) \Rightarrow (match b in B return (\lambda (_: B).Prop) with 
[Abbr \Rightarrow False | Abst \Rightarrow True | Void \Rightarrow False]) | 
(Flat _) \Rightarrow False])])) I (CHead e1 (Bind Abbr) v) H2) in (False_ind 
((eq C (CHead c0 (Bind Abbr) u) c2) \to ((csub3 g c1 c0) \to ((ty3 g c0 u t) 
\to (ex2 C (\lambda (e2: C).(eq C c2 (CHead e2 (Bind Abbr) v))) (\lambda (e2: 
C).(csub3 g e1 e2)))))) H4)) H3 H0 H1)))]) in (H0 (refl_equal C (CHead e1 
(Bind Abbr) v)) (refl_equal C c2))))))).

theorem csub3_gen_abst:
 \forall (g: G).(\forall (e1: C).(\forall (c2: C).(\forall (v1: T).((csub3 g 
(CHead e1 (Bind Abst) v1) c2) \to (or (ex2 C (\lambda (e2: C).(eq C c2 (CHead 
e2 (Bind Abst) v1))) (\lambda (e2: C).(csub3 g e1 e2))) (ex3_2 C T (\lambda 
(e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csub3 g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g 
e2 v2 v1)))))))))
\def
 \lambda (g: G).(\lambda (e1: C).(\lambda (c2: C).(\lambda (v1: T).(\lambda 
(H: (csub3 g (CHead e1 (Bind Abst) v1) c2)).(let H0 \def (match H in csub3 
return (\lambda (c: C).(\lambda (c0: C).(\lambda (_: (csub3 ? c c0)).((eq C c 
(CHead e1 (Bind Abst) v1)) \to ((eq C c0 c2) \to (or (ex2 C (\lambda (e2: 
C).(eq C c2 (CHead e2 (Bind Abst) v1))) (\lambda (e2: C).(csub3 g e1 e2))) 
(ex3_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind Abbr) 
v2)))) (\lambda (e2: C).(\lambda (_: T).(csub3 g e1 e2))) (\lambda (e2: 
C).(\lambda (v2: T).(ty3 g e2 v2 v1)))))))))) with [(csub3_sort n) 
\Rightarrow (\lambda (H0: (eq C (CSort n) (CHead e1 (Bind Abst) 
v1))).(\lambda (H1: (eq C (CSort n) c2)).((let H2 \def (eq_ind C (CSort n) 
(\lambda (e: C).(match e in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow True | (CHead _ _ _) \Rightarrow False])) I (CHead e1 (Bind Abst) 
v1) H0) in (False_ind ((eq C (CSort n) c2) \to (or (ex2 C (\lambda (e2: 
C).(eq C c2 (CHead e2 (Bind Abst) v1))) (\lambda (e2: C).(csub3 g e1 e2))) 
(ex3_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind Abbr) 
v2)))) (\lambda (e2: C).(\lambda (_: T).(csub3 g e1 e2))) (\lambda (e2: 
C).(\lambda (v2: T).(ty3 g e2 v2 v1)))))) H2)) H1))) | (csub3_head c1 c0 H0 k 
u) \Rightarrow (\lambda (H1: (eq C (CHead c1 k u) (CHead e1 (Bind Abst) 
v1))).(\lambda (H2: (eq C (CHead c0 k u) c2)).((let H3 \def (f_equal C T 
(\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead c1 k u) (CHead e1 (Bind 
Abst) v1) H1) in ((let H4 \def (f_equal C K (\lambda (e: C).(match e in C 
return (\lambda (_: C).K) with [(CSort _) \Rightarrow k | (CHead _ k0 _) 
\Rightarrow k0])) (CHead c1 k u) (CHead e1 (Bind Abst) v1) H1) in ((let H5 
\def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) 
with [(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) (CHead c1 k 
u) (CHead e1 (Bind Abst) v1) H1) in (eq_ind C e1 (\lambda (c: C).((eq K k 
(Bind Abst)) \to ((eq T u v1) \to ((eq C (CHead c0 k u) c2) \to ((csub3 g c 
c0) \to (or (ex2 C (\lambda (e2: C).(eq C c2 (CHead e2 (Bind Abst) v1))) 
(\lambda (e2: C).(csub3 g e1 e2))) (ex3_2 C T (\lambda (e2: C).(\lambda (v2: 
T).(eq C c2 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: 
T).(csub3 g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 
v1)))))))))) (\lambda (H6: (eq K k (Bind Abst))).(eq_ind K (Bind Abst) 
(\lambda (k0: K).((eq T u v1) \to ((eq C (CHead c0 k0 u) c2) \to ((csub3 g e1 
c0) \to (or (ex2 C (\lambda (e2: C).(eq C c2 (CHead e2 (Bind Abst) v1))) 
(\lambda (e2: C).(csub3 g e1 e2))) (ex3_2 C T (\lambda (e2: C).(\lambda (v2: 
T).(eq C c2 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: 
T).(csub3 g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 
v1))))))))) (\lambda (H7: (eq T u v1)).(eq_ind T v1 (\lambda (t: T).((eq C 
(CHead c0 (Bind Abst) t) c2) \to ((csub3 g e1 c0) \to (or (ex2 C (\lambda 
(e2: C).(eq C c2 (CHead e2 (Bind Abst) v1))) (\lambda (e2: C).(csub3 g e1 
e2))) (ex3_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind 
Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csub3 g e1 e2))) (\lambda (e2: 
C).(\lambda (v2: T).(ty3 g e2 v2 v1)))))))) (\lambda (H8: (eq C (CHead c0 
(Bind Abst) v1) c2)).(eq_ind C (CHead c0 (Bind Abst) v1) (\lambda (c: 
C).((csub3 g e1 c0) \to (or (ex2 C (\lambda (e2: C).(eq C c (CHead e2 (Bind 
Abst) v1))) (\lambda (e2: C).(csub3 g e1 e2))) (ex3_2 C T (\lambda (e2: 
C).(\lambda (v2: T).(eq C c (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csub3 g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g 
e2 v2 v1))))))) (\lambda (H9: (csub3 g e1 c0)).(let H10 \def (eq_ind_r C c2 
(\lambda (c: C).(csub3 g (CHead e1 (Bind Abst) v1) c)) H (CHead c0 (Bind 
Abst) v1) H8) in (or_introl (ex2 C (\lambda (e2: C).(eq C (CHead c0 (Bind 
Abst) v1) (CHead e2 (Bind Abst) v1))) (\lambda (e2: C).(csub3 g e1 e2))) 
(ex3_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c0 (Bind Abst) v1) 
(CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csub3 g e1 
e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1)))) (ex_intro2 C 
(\lambda (e2: C).(eq C (CHead c0 (Bind Abst) v1) (CHead e2 (Bind Abst) v1))) 
(\lambda (e2: C).(csub3 g e1 e2)) c0 (refl_equal C (CHead c0 (Bind Abst) v1)) 
H9)))) c2 H8)) u (sym_eq T u v1 H7))) k (sym_eq K k (Bind Abst) H6))) c1 
(sym_eq C c1 e1 H5))) H4)) H3)) H2 H0))) | (csub3_void c1 c0 H0 b H1 u1 u2) 
\Rightarrow (\lambda (H2: (eq C (CHead c1 (Bind Void) u1) (CHead e1 (Bind 
Abst) v1))).(\lambda (H3: (eq C (CHead c0 (Bind b) u2) c2)).((let H4 \def 
(eq_ind C (CHead c1 (Bind Void) u1) (\lambda (e: C).(match e in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind b0) 
\Rightarrow (match b0 in B return (\lambda (_: B).Prop) with [Abbr 
\Rightarrow False | Abst \Rightarrow False | Void \Rightarrow True]) | (Flat 
_) \Rightarrow False])])) I (CHead e1 (Bind Abst) v1) H2) in (False_ind ((eq 
C (CHead c0 (Bind b) u2) c2) \to ((csub3 g c1 c0) \to ((not (eq B b Void)) 
\to (or (ex2 C (\lambda (e2: C).(eq C c2 (CHead e2 (Bind Abst) v1))) (\lambda 
(e2: C).(csub3 g e1 e2))) (ex3_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C 
c2 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csub3 g e1 
e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1)))))))) H4)) H3 H0 
H1))) | (csub3_abst c1 c0 H0 u t H1) \Rightarrow (\lambda (H2: (eq C (CHead 
c1 (Bind Abst) t) (CHead e1 (Bind Abst) v1))).(\lambda (H3: (eq C (CHead c0 
(Bind Abbr) u) c2)).((let H4 \def (f_equal C T (\lambda (e: C).(match e in C 
return (\lambda (_: C).T) with [(CSort _) \Rightarrow t | (CHead _ _ t0) 
\Rightarrow t0])) (CHead c1 (Bind Abst) t) (CHead e1 (Bind Abst) v1) H2) in 
((let H5 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: 
C).C) with [(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) (CHead 
c1 (Bind Abst) t) (CHead e1 (Bind Abst) v1) H2) in (eq_ind C e1 (\lambda (c: 
C).((eq T t v1) \to ((eq C (CHead c0 (Bind Abbr) u) c2) \to ((csub3 g c c0) 
\to ((ty3 g c0 u t) \to (or (ex2 C (\lambda (e2: C).(eq C c2 (CHead e2 (Bind 
Abst) v1))) (\lambda (e2: C).(csub3 g e1 e2))) (ex3_2 C T (\lambda (e2: 
C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csub3 g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g 
e2 v2 v1)))))))))) (\lambda (H6: (eq T t v1)).(eq_ind T v1 (\lambda (t0: 
T).((eq C (CHead c0 (Bind Abbr) u) c2) \to ((csub3 g e1 c0) \to ((ty3 g c0 u 
t0) \to (or (ex2 C (\lambda (e2: C).(eq C c2 (CHead e2 (Bind Abst) v1))) 
(\lambda (e2: C).(csub3 g e1 e2))) (ex3_2 C T (\lambda (e2: C).(\lambda (v2: 
T).(eq C c2 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: 
T).(csub3 g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 
v1))))))))) (\lambda (H7: (eq C (CHead c0 (Bind Abbr) u) c2)).(eq_ind C 
(CHead c0 (Bind Abbr) u) (\lambda (c: C).((csub3 g e1 c0) \to ((ty3 g c0 u 
v1) \to (or (ex2 C (\lambda (e2: C).(eq C c (CHead e2 (Bind Abst) v1))) 
(\lambda (e2: C).(csub3 g e1 e2))) (ex3_2 C T (\lambda (e2: C).(\lambda (v2: 
T).(eq C c (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: 
T).(csub3 g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 
v1)))))))) (\lambda (H8: (csub3 g e1 c0)).(\lambda (H9: (ty3 g c0 u v1)).(let 
H10 \def (eq_ind_r C c2 (\lambda (c: C).(csub3 g (CHead e1 (Bind Abst) v1) 
c)) H (CHead c0 (Bind Abbr) u) H7) in (or_intror (ex2 C (\lambda (e2: C).(eq 
C (CHead c0 (Bind Abbr) u) (CHead e2 (Bind Abst) v1))) (\lambda (e2: 
C).(csub3 g e1 e2))) (ex3_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C 
(CHead c0 (Bind Abbr) u) (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csub3 g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g 
e2 v2 v1)))) (ex3_2_intro C T (\lambda (e2: C).(\lambda (v2: T).(eq C (CHead 
c0 (Bind Abbr) u) (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: 
T).(csub3 g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1))) c0 
u (refl_equal C (CHead c0 (Bind Abbr) u)) H8 H9))))) c2 H7)) t (sym_eq T t v1 
H6))) c1 (sym_eq C c1 e1 H5))) H4)) H3 H0 H1)))]) in (H0 (refl_equal C (CHead 
e1 (Bind Abst) v1)) (refl_equal C c2))))))).

theorem csub3_gen_bind:
 \forall (g: G).(\forall (b1: B).(\forall (e1: C).(\forall (c2: C).(\forall 
(v1: T).((csub3 g (CHead e1 (Bind b1) v1) c2) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csub3 g e1 e2))))))))))
\def
 \lambda (g: G).(\lambda (b1: B).(\lambda (e1: C).(\lambda (c2: C).(\lambda 
(v1: T).(\lambda (H: (csub3 g (CHead e1 (Bind b1) v1) c2)).(let H0 \def 
(match H in csub3 return (\lambda (c: C).(\lambda (c0: C).(\lambda (_: (csub3 
? c c0)).((eq C c (CHead e1 (Bind b1) v1)) \to ((eq C c0 c2) \to (ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind 
b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csub3 g e1 
e2)))))))))) with [(csub3_sort n) \Rightarrow (\lambda (H0: (eq C (CSort n) 
(CHead e1 (Bind b1) v1))).(\lambda (H1: (eq C (CSort n) c2)).((let H2 \def 
(eq_ind C (CSort n) (\lambda (e: C).(match e in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow 
False])) I (CHead e1 (Bind b1) v1) H0) in (False_ind ((eq C (CSort n) c2) \to 
(ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csub3 g e1 e2)))))) H2)) H1))) | (csub3_head c1 c0 H0 k u) \Rightarrow 
(\lambda (H1: (eq C (CHead c1 k u) (CHead e1 (Bind b1) v1))).(\lambda (H2: 
(eq C (CHead c0 k u) c2)).((let H3 \def (f_equal C T (\lambda (e: C).(match e 
in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t) 
\Rightarrow t])) (CHead c1 k u) (CHead e1 (Bind b1) v1) H1) in ((let H4 \def 
(f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) with 
[(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) (CHead c1 k u) 
(CHead e1 (Bind b1) v1) H1) in ((let H5 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c1 | 
(CHead c _ _) \Rightarrow c])) (CHead c1 k u) (CHead e1 (Bind b1) v1) H1) in 
(eq_ind C e1 (\lambda (c: C).((eq K k (Bind b1)) \to ((eq T u v1) \to ((eq C 
(CHead c0 k u) c2) \to ((csub3 g c c0) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csub3 g e1 e2)))))))))) 
(\lambda (H6: (eq K k (Bind b1))).(eq_ind K (Bind b1) (\lambda (k0: K).((eq T 
u v1) \to ((eq C (CHead c0 k0 u) c2) \to ((csub3 g e1 c0) \to (ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind 
b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csub3 g e1 
e2))))))))) (\lambda (H7: (eq T u v1)).(eq_ind T v1 (\lambda (t: T).((eq C 
(CHead c0 (Bind b1) t) c2) \to ((csub3 g e1 c0) \to (ex2_3 B C T (\lambda 
(b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) 
v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csub3 g e1 
e2)))))))) (\lambda (H8: (eq C (CHead c0 (Bind b1) v1) c2)).(eq_ind C (CHead 
c0 (Bind b1) v1) (\lambda (c: C).((csub3 g e1 c0) \to (ex2_3 B C T (\lambda 
(b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csub3 g e1 e2))))))) 
(\lambda (H9: (csub3 g e1 c0)).(let H10 \def (eq_ind_r C c2 (\lambda (c: 
C).(csub3 g (CHead e1 (Bind b1) v1) c)) H (CHead c0 (Bind b1) v1) H8) in 
(ex2_3_intro B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C 
(CHead c0 (Bind b1) v1) (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda 
(e2: C).(\lambda (_: T).(csub3 g e1 e2)))) b1 c0 v1 (refl_equal C (CHead c0 
(Bind b1) v1)) H9))) c2 H8)) u (sym_eq T u v1 H7))) k (sym_eq K k (Bind b1) 
H6))) c1 (sym_eq C c1 e1 H5))) H4)) H3)) H2 H0))) | (csub3_void c1 c0 H0 b H1 
u1 u2) \Rightarrow (\lambda (H2: (eq C (CHead c1 (Bind Void) u1) (CHead e1 
(Bind b1) v1))).(\lambda (H3: (eq C (CHead c0 (Bind b) u2) c2)).((let H4 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u1 | (CHead _ _ t) \Rightarrow t])) (CHead c1 (Bind 
Void) u1) (CHead e1 (Bind b1) v1) H2) in ((let H5 \def (f_equal C B (\lambda 
(e: C).(match e in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow 
Void | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).B) with 
[(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Void])])) (CHead c1 (Bind 
Void) u1) (CHead e1 (Bind b1) v1) H2) in ((let H6 \def (f_equal C C (\lambda 
(e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c1 
| (CHead c _ _) \Rightarrow c])) (CHead c1 (Bind Void) u1) (CHead e1 (Bind 
b1) v1) H2) in (eq_ind C e1 (\lambda (c: C).((eq B Void b1) \to ((eq T u1 v1) 
\to ((eq C (CHead c0 (Bind b) u2) c2) \to ((csub3 g c c0) \to ((not (eq B b 
Void)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: 
T).(eq C c2 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csub3 g e1 e2))))))))))) (\lambda (H7: (eq B Void 
b1)).(eq_ind B Void (\lambda (_: B).((eq T u1 v1) \to ((eq C (CHead c0 (Bind 
b) u2) c2) \to ((csub3 g e1 c0) \to ((not (eq B b Void)) \to (ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind 
b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csub3 g e1 
e2)))))))))) (\lambda (H8: (eq T u1 v1)).(eq_ind T v1 (\lambda (_: T).((eq C 
(CHead c0 (Bind b) u2) c2) \to ((csub3 g e1 c0) \to ((not (eq B b Void)) \to 
(ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csub3 g e1 e2))))))))) (\lambda (H9: (eq C (CHead c0 (Bind b) u2) 
c2)).(eq_ind C (CHead c0 (Bind b) u2) (\lambda (c: C).((csub3 g e1 c0) \to 
((not (eq B b Void)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: 
C).(\lambda (v2: T).(eq C c (CHead e2 (Bind b2) v2))))) (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csub3 g e1 e2)))))))) (\lambda (H10: 
(csub3 g e1 c0)).(\lambda (_: (not (eq B b Void))).(let H12 \def (eq_ind_r C 
c2 (\lambda (c: C).(csub3 g (CHead e1 (Bind b1) v1) c)) H (CHead c0 (Bind b) 
u2) H9) in (let H13 \def (eq_ind_r B b1 (\lambda (b0: B).(csub3 g (CHead e1 
(Bind b0) v1) (CHead c0 (Bind b) u2))) H12 Void H7) in (ex2_3_intro B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C (CHead c0 (Bind b) 
u2) (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csub3 g e1 e2)))) b c0 u2 (refl_equal C (CHead c0 (Bind b) u2)) H10))))) 
c2 H9)) u1 (sym_eq T u1 v1 H8))) b1 H7)) c1 (sym_eq C c1 e1 H6))) H5)) H4)) 
H3 H0 H1))) | (csub3_abst c1 c0 H0 u t H1) \Rightarrow (\lambda (H2: (eq C 
(CHead c1 (Bind Abst) t) (CHead e1 (Bind b1) v1))).(\lambda (H3: (eq C (CHead 
c0 (Bind Abbr) u) c2)).((let H4 \def (f_equal C T (\lambda (e: C).(match e in 
C return (\lambda (_: C).T) with [(CSort _) \Rightarrow t | (CHead _ _ t0) 
\Rightarrow t0])) (CHead c1 (Bind Abst) t) (CHead e1 (Bind b1) v1) H2) in 
((let H5 \def (f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: 
C).B) with [(CSort _) \Rightarrow Abst | (CHead _ k _) \Rightarrow (match k 
in K return (\lambda (_: K).B) with [(Bind b) \Rightarrow b | (Flat _) 
\Rightarrow Abst])])) (CHead c1 (Bind Abst) t) (CHead e1 (Bind b1) v1) H2) in 
((let H6 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: 
C).C) with [(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) (CHead 
c1 (Bind Abst) t) (CHead e1 (Bind b1) v1) H2) in (eq_ind C e1 (\lambda (c: 
C).((eq B Abst b1) \to ((eq T t v1) \to ((eq C (CHead c0 (Bind Abbr) u) c2) 
\to ((csub3 g c c0) \to ((ty3 g c0 u t) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csub3 g e1 e2))))))))))) 
(\lambda (H7: (eq B Abst b1)).(eq_ind B Abst (\lambda (_: B).((eq T t v1) \to 
((eq C (CHead c0 (Bind Abbr) u) c2) \to ((csub3 g e1 c0) \to ((ty3 g c0 u t) 
\to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csub3 g e1 e2)))))))))) (\lambda (H8: (eq T t v1)).(eq_ind T v1 (\lambda 
(t0: T).((eq C (CHead c0 (Bind Abbr) u) c2) \to ((csub3 g e1 c0) \to ((ty3 g 
c0 u t0) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: 
T).(eq C c2 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csub3 g e1 e2))))))))) (\lambda (H9: (eq C (CHead c0 
(Bind Abbr) u) c2)).(eq_ind C (CHead c0 (Bind Abbr) u) (\lambda (c: 
C).((csub3 g e1 c0) \to ((ty3 g c0 u v1) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csub3 g e1 e2)))))))) 
(\lambda (H10: (csub3 g e1 c0)).(\lambda (_: (ty3 g c0 u v1)).(let H12 \def 
(eq_ind_r C c2 (\lambda (c: C).(csub3 g (CHead e1 (Bind b1) v1) c)) H (CHead 
c0 (Bind Abbr) u) H9) in (let H13 \def (eq_ind_r B b1 (\lambda (b: B).(csub3 
g (CHead e1 (Bind b) v1) (CHead c0 (Bind Abbr) u))) H12 Abst H7) in 
(ex2_3_intro B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C 
(CHead c0 (Bind Abbr) u) (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda 
(e2: C).(\lambda (_: T).(csub3 g e1 e2)))) Abbr c0 u (refl_equal C (CHead c0 
(Bind Abbr) u)) H10))))) c2 H9)) t (sym_eq T t v1 H8))) b1 H7)) c1 (sym_eq C 
c1 e1 H6))) H5)) H4)) H3 H0 H1)))]) in (H0 (refl_equal C (CHead e1 (Bind b1) 
v1)) (refl_equal C c2)))))))).

