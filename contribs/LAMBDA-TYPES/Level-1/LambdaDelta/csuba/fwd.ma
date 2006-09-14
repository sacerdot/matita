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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/csuba/fwd".

include "csuba/defs.ma".

theorem csuba_gen_abbr:
 \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u: T).((csuba g 
(CHead d1 (Bind Abbr) u) c) \to (ex2 C (\lambda (d2: C).(eq C c (CHead d2 
(Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))))))
\def
 \lambda (g: G).(\lambda (d1: C).(\lambda (c: C).(\lambda (u: T).(\lambda (H: 
(csuba g (CHead d1 (Bind Abbr) u) c)).(let H0 \def (match H in csuba return 
(\lambda (c0: C).(\lambda (c1: C).(\lambda (_: (csuba ? c0 c1)).((eq C c0 
(CHead d1 (Bind Abbr) u)) \to ((eq C c1 c) \to (ex2 C (\lambda (d2: C).(eq C 
c (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))))))) with 
[(csuba_sort n) \Rightarrow (\lambda (H0: (eq C (CSort n) (CHead d1 (Bind 
Abbr) u))).(\lambda (H1: (eq C (CSort n) c)).((let H2 \def (eq_ind C (CSort 
n) (\lambda (e: C).(match e in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow True | (CHead _ _ _) \Rightarrow False])) I (CHead d1 (Bind Abbr) 
u) H0) in (False_ind ((eq C (CSort n) c) \to (ex2 C (\lambda (d2: C).(eq C c 
(CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))) H2)) H1))) | 
(csuba_head c1 c2 H0 k u0) \Rightarrow (\lambda (H1: (eq C (CHead c1 k u0) 
(CHead d1 (Bind Abbr) u))).(\lambda (H2: (eq C (CHead c2 k u0) c)).((let H3 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) (CHead c1 k 
u0) (CHead d1 (Bind Abbr) u) H1) in ((let H4 \def (f_equal C K (\lambda (e: 
C).(match e in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k | 
(CHead _ k0 _) \Rightarrow k0])) (CHead c1 k u0) (CHead d1 (Bind Abbr) u) H1) 
in ((let H5 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow c1 | (CHead c0 _ _) \Rightarrow c0])) 
(CHead c1 k u0) (CHead d1 (Bind Abbr) u) H1) in (eq_ind C d1 (\lambda (c0: 
C).((eq K k (Bind Abbr)) \to ((eq T u0 u) \to ((eq C (CHead c2 k u0) c) \to 
((csuba g c0 c2) \to (ex2 C (\lambda (d2: C).(eq C c (CHead d2 (Bind Abbr) 
u))) (\lambda (d2: C).(csuba g d1 d2)))))))) (\lambda (H6: (eq K k (Bind 
Abbr))).(eq_ind K (Bind Abbr) (\lambda (k0: K).((eq T u0 u) \to ((eq C (CHead 
c2 k0 u0) c) \to ((csuba g d1 c2) \to (ex2 C (\lambda (d2: C).(eq C c (CHead 
d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))))))) (\lambda (H7: (eq 
T u0 u)).(eq_ind T u (\lambda (t: T).((eq C (CHead c2 (Bind Abbr) t) c) \to 
((csuba g d1 c2) \to (ex2 C (\lambda (d2: C).(eq C c (CHead d2 (Bind Abbr) 
u))) (\lambda (d2: C).(csuba g d1 d2)))))) (\lambda (H8: (eq C (CHead c2 
(Bind Abbr) u) c)).(eq_ind C (CHead c2 (Bind Abbr) u) (\lambda (c0: 
C).((csuba g d1 c2) \to (ex2 C (\lambda (d2: C).(eq C c0 (CHead d2 (Bind 
Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))))) (\lambda (H9: (csuba g d1 
c2)).(ex_intro2 C (\lambda (d2: C).(eq C (CHead c2 (Bind Abbr) u) (CHead d2 
(Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)) c2 (refl_equal C (CHead c2 
(Bind Abbr) u)) H9)) c H8)) u0 (sym_eq T u0 u H7))) k (sym_eq K k (Bind Abbr) 
H6))) c1 (sym_eq C c1 d1 H5))) H4)) H3)) H2 H0))) | (csuba_abst c1 c2 H0 t a 
H1 u0 H2) \Rightarrow (\lambda (H3: (eq C (CHead c1 (Bind Abst) t) (CHead d1 
(Bind Abbr) u))).(\lambda (H4: (eq C (CHead c2 (Bind Abbr) u0) c)).((let H5 
\def (eq_ind C (CHead c1 (Bind Abst) t) (\lambda (e: C).(match e in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind b) 
\Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow 
False | Abst \Rightarrow True | Void \Rightarrow False]) | (Flat _) 
\Rightarrow False])])) I (CHead d1 (Bind Abbr) u) H3) in (False_ind ((eq C 
(CHead c2 (Bind Abbr) u0) c) \to ((csuba g c1 c2) \to ((arity g c1 t (asucc g 
a)) \to ((arity g c2 u0 a) \to (ex2 C (\lambda (d2: C).(eq C c (CHead d2 
(Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))))))) H5)) H4 H0 H1 H2)))]) 
in (H0 (refl_equal C (CHead d1 (Bind Abbr) u)) (refl_equal C c))))))).

theorem csuba_gen_void:
 \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u: T).((csuba g 
(CHead d1 (Bind Void) u) c) \to (ex2 C (\lambda (d2: C).(eq C c (CHead d2 
(Bind Void) u))) (\lambda (d2: C).(csuba g d1 d2)))))))
\def
 \lambda (g: G).(\lambda (d1: C).(\lambda (c: C).(\lambda (u: T).(\lambda (H: 
(csuba g (CHead d1 (Bind Void) u) c)).(let H0 \def (match H in csuba return 
(\lambda (c0: C).(\lambda (c1: C).(\lambda (_: (csuba ? c0 c1)).((eq C c0 
(CHead d1 (Bind Void) u)) \to ((eq C c1 c) \to (ex2 C (\lambda (d2: C).(eq C 
c (CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d1 d2)))))))) with 
[(csuba_sort n) \Rightarrow (\lambda (H0: (eq C (CSort n) (CHead d1 (Bind 
Void) u))).(\lambda (H1: (eq C (CSort n) c)).((let H2 \def (eq_ind C (CSort 
n) (\lambda (e: C).(match e in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow True | (CHead _ _ _) \Rightarrow False])) I (CHead d1 (Bind Void) 
u) H0) in (False_ind ((eq C (CSort n) c) \to (ex2 C (\lambda (d2: C).(eq C c 
(CHead d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d1 d2)))) H2)) H1))) | 
(csuba_head c1 c2 H0 k u0) \Rightarrow (\lambda (H1: (eq C (CHead c1 k u0) 
(CHead d1 (Bind Void) u))).(\lambda (H2: (eq C (CHead c2 k u0) c)).((let H3 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) (CHead c1 k 
u0) (CHead d1 (Bind Void) u) H1) in ((let H4 \def (f_equal C K (\lambda (e: 
C).(match e in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k | 
(CHead _ k0 _) \Rightarrow k0])) (CHead c1 k u0) (CHead d1 (Bind Void) u) H1) 
in ((let H5 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow c1 | (CHead c0 _ _) \Rightarrow c0])) 
(CHead c1 k u0) (CHead d1 (Bind Void) u) H1) in (eq_ind C d1 (\lambda (c0: 
C).((eq K k (Bind Void)) \to ((eq T u0 u) \to ((eq C (CHead c2 k u0) c) \to 
((csuba g c0 c2) \to (ex2 C (\lambda (d2: C).(eq C c (CHead d2 (Bind Void) 
u))) (\lambda (d2: C).(csuba g d1 d2)))))))) (\lambda (H6: (eq K k (Bind 
Void))).(eq_ind K (Bind Void) (\lambda (k0: K).((eq T u0 u) \to ((eq C (CHead 
c2 k0 u0) c) \to ((csuba g d1 c2) \to (ex2 C (\lambda (d2: C).(eq C c (CHead 
d2 (Bind Void) u))) (\lambda (d2: C).(csuba g d1 d2))))))) (\lambda (H7: (eq 
T u0 u)).(eq_ind T u (\lambda (t: T).((eq C (CHead c2 (Bind Void) t) c) \to 
((csuba g d1 c2) \to (ex2 C (\lambda (d2: C).(eq C c (CHead d2 (Bind Void) 
u))) (\lambda (d2: C).(csuba g d1 d2)))))) (\lambda (H8: (eq C (CHead c2 
(Bind Void) u) c)).(eq_ind C (CHead c2 (Bind Void) u) (\lambda (c0: 
C).((csuba g d1 c2) \to (ex2 C (\lambda (d2: C).(eq C c0 (CHead d2 (Bind 
Void) u))) (\lambda (d2: C).(csuba g d1 d2))))) (\lambda (H9: (csuba g d1 
c2)).(ex_intro2 C (\lambda (d2: C).(eq C (CHead c2 (Bind Void) u) (CHead d2 
(Bind Void) u))) (\lambda (d2: C).(csuba g d1 d2)) c2 (refl_equal C (CHead c2 
(Bind Void) u)) H9)) c H8)) u0 (sym_eq T u0 u H7))) k (sym_eq K k (Bind Void) 
H6))) c1 (sym_eq C c1 d1 H5))) H4)) H3)) H2 H0))) | (csuba_abst c1 c2 H0 t a 
H1 u0 H2) \Rightarrow (\lambda (H3: (eq C (CHead c1 (Bind Abst) t) (CHead d1 
(Bind Void) u))).(\lambda (H4: (eq C (CHead c2 (Bind Abbr) u0) c)).((let H5 
\def (eq_ind C (CHead c1 (Bind Abst) t) (\lambda (e: C).(match e in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind b) 
\Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow 
False | Abst \Rightarrow True | Void \Rightarrow False]) | (Flat _) 
\Rightarrow False])])) I (CHead d1 (Bind Void) u) H3) in (False_ind ((eq C 
(CHead c2 (Bind Abbr) u0) c) \to ((csuba g c1 c2) \to ((arity g c1 t (asucc g 
a)) \to ((arity g c2 u0 a) \to (ex2 C (\lambda (d2: C).(eq C c (CHead d2 
(Bind Void) u))) (\lambda (d2: C).(csuba g d1 d2))))))) H5)) H4 H0 H1 H2)))]) 
in (H0 (refl_equal C (CHead d1 (Bind Void) u)) (refl_equal C c))))))).

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
(H: (csuba g (CHead d1 (Bind Abst) u1) c)).(let H0 \def (match H in csuba 
return (\lambda (c0: C).(\lambda (c1: C).(\lambda (_: (csuba ? c0 c1)).((eq C 
c0 (CHead d1 (Bind Abst) u1)) \to ((eq C c1 c) \to (or (ex2 C (\lambda (d2: 
C).(eq C c (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c (CHead 
d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a))))))))))) with [(csuba_sort n) \Rightarrow (\lambda (H0: 
(eq C (CSort n) (CHead d1 (Bind Abst) u1))).(\lambda (H1: (eq C (CSort n) 
c)).((let H2 \def (eq_ind C (CSort n) (\lambda (e: C).(match e in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) 
\Rightarrow False])) I (CHead d1 (Bind Abst) u1) H0) in (False_ind ((eq C 
(CSort n) c) \to (or (ex2 C (\lambda (d2: C).(eq C c (CHead d2 (Bind Abst) 
u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(eq C c (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))))) 
H2)) H1))) | (csuba_head c1 c2 H0 k u) \Rightarrow (\lambda (H1: (eq C (CHead 
c1 k u) (CHead d1 (Bind Abst) u1))).(\lambda (H2: (eq C (CHead c2 k u) 
c)).((let H3 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda 
(_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) 
(CHead c1 k u) (CHead d1 (Bind Abst) u1) H1) in ((let H4 \def (f_equal C K 
(\lambda (e: C).(match e in C return (\lambda (_: C).K) with [(CSort _) 
\Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) (CHead c1 k u) (CHead d1 
(Bind Abst) u1) H1) in ((let H5 \def (f_equal C C (\lambda (e: C).(match e in 
C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c1 | (CHead c0 _ _) 
\Rightarrow c0])) (CHead c1 k u) (CHead d1 (Bind Abst) u1) H1) in (eq_ind C 
d1 (\lambda (c0: C).((eq K k (Bind Abst)) \to ((eq T u u1) \to ((eq C (CHead 
c2 k u) c) \to ((csuba g c0 c2) \to (or (ex2 C (\lambda (d2: C).(eq C c 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c (CHead d2 (Bind 
Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 
d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc 
g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))))))))) (\lambda (H6: (eq K k (Bind Abst))).(eq_ind K (Bind Abst) 
(\lambda (k0: K).((eq T u u1) \to ((eq C (CHead c2 k0 u) c) \to ((csuba g d1 
c2) \to (or (ex2 C (\lambda (d2: C).(eq C c (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(eq C c (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))))))) (\lambda 
(H7: (eq T u u1)).(eq_ind T u1 (\lambda (t: T).((eq C (CHead c2 (Bind Abst) 
t) c) \to ((csuba g d1 c2) \to (or (ex2 C (\lambda (d2: C).(eq C c (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))))))) (\lambda (H8: (eq C (CHead c2 (Bind Abst) u1) c)).(eq_ind C (CHead 
c2 (Bind Abst) u1) (\lambda (c0: C).((csuba g d1 c2) \to (or (ex2 C (\lambda 
(d2: C).(eq C c0 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c0 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a)))))))) (\lambda (H9: (csuba g d1 c2)).(or_introl (ex2 C 
(\lambda (d2: C).(eq C (CHead c2 (Bind Abst) u1) (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(eq C (CHead c2 (Bind Abst) u1) (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))) (ex_intro2 C (\lambda (d2: C).(eq C (CHead c2 (Bind Abst) u1) (CHead 
d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2)) c2 (refl_equal C 
(CHead c2 (Bind Abst) u1)) H9))) c H8)) u (sym_eq T u u1 H7))) k (sym_eq K k 
(Bind Abst) H6))) c1 (sym_eq C c1 d1 H5))) H4)) H3)) H2 H0))) | (csuba_abst 
c1 c2 H0 t a H1 u H2) \Rightarrow (\lambda (H3: (eq C (CHead c1 (Bind Abst) 
t) (CHead d1 (Bind Abst) u1))).(\lambda (H4: (eq C (CHead c2 (Bind Abbr) u) 
c)).((let H5 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda 
(_: C).T) with [(CSort _) \Rightarrow t | (CHead _ _ t0) \Rightarrow t0])) 
(CHead c1 (Bind Abst) t) (CHead d1 (Bind Abst) u1) H3) in ((let H6 \def 
(f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c1 | (CHead c0 _ _) \Rightarrow c0])) (CHead c1 (Bind 
Abst) t) (CHead d1 (Bind Abst) u1) H3) in (eq_ind C d1 (\lambda (c0: C).((eq 
T t u1) \to ((eq C (CHead c2 (Bind Abbr) u) c) \to ((csuba g c0 c2) \to 
((arity g c0 t (asucc g a)) \to ((arity g c2 u a) \to (or (ex2 C (\lambda 
(d2: C).(eq C c (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(arity 
g d1 u1 (asucc g a0))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a0: 
A).(arity g d2 u2 a0)))))))))))) (\lambda (H7: (eq T t u1)).(eq_ind T u1 
(\lambda (t0: T).((eq C (CHead c2 (Bind Abbr) u) c) \to ((csuba g d1 c2) \to 
((arity g d1 t0 (asucc g a)) \to ((arity g c2 u a) \to (or (ex2 C (\lambda 
(d2: C).(eq C c (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(arity 
g d1 u1 (asucc g a0))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a0: 
A).(arity g d2 u2 a0))))))))))) (\lambda (H8: (eq C (CHead c2 (Bind Abbr) u) 
c)).(eq_ind C (CHead c2 (Bind Abbr) u) (\lambda (c0: C).((csuba g d1 c2) \to 
((arity g d1 u1 (asucc g a)) \to ((arity g c2 u a) \to (or (ex2 C (\lambda 
(d2: C).(eq C c0 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C c0 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(arity 
g d1 u1 (asucc g a0))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a0: 
A).(arity g d2 u2 a0)))))))))) (\lambda (H9: (csuba g d1 c2)).(\lambda (H10: 
(arity g d1 u1 (asucc g a))).(\lambda (H11: (arity g c2 u a)).(or_intror (ex2 
C (\lambda (d2: C).(eq C (CHead c2 (Bind Abbr) u) (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(eq C (CHead c2 (Bind Abbr) u) (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(arity g d1 u1 (asucc g 
a0))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a0: A).(arity g d2 u2 
a0))))) (ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(eq C (CHead c2 (Bind Abbr) u) (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a0: A).(arity g d1 u1 (asucc g a0))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a0: A).(arity g d2 u2 a0)))) c2 u a 
(refl_equal C (CHead c2 (Bind Abbr) u)) H9 H10 H11))))) c H8)) t (sym_eq T t 
u1 H7))) c1 (sym_eq C c1 d1 H6))) H5)) H4 H0 H1 H2)))]) in (H0 (refl_equal C 
(CHead d1 (Bind Abst) u1)) (refl_equal C c))))))).

theorem csuba_gen_flat:
 \forall (g: G).(\forall (d1: C).(\forall (c: C).(\forall (u1: T).(\forall 
(f: F).((csuba g (CHead d1 (Flat f) u1) c) \to (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(eq C c (CHead d2 (Flat f) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d1 d2)))))))))
\def
 \lambda (g: G).(\lambda (d1: C).(\lambda (c: C).(\lambda (u1: T).(\lambda 
(f: F).(\lambda (H: (csuba g (CHead d1 (Flat f) u1) c)).(let H0 \def (match H 
in csuba return (\lambda (c0: C).(\lambda (c1: C).(\lambda (_: (csuba ? c0 
c1)).((eq C c0 (CHead d1 (Flat f) u1)) \to ((eq C c1 c) \to (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(eq C c (CHead d2 (Flat f) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d1 d2))))))))) with [(csuba_sort n) 
\Rightarrow (\lambda (H0: (eq C (CSort n) (CHead d1 (Flat f) u1))).(\lambda 
(H1: (eq C (CSort n) c)).((let H2 \def (eq_ind C (CSort n) (\lambda (e: 
C).(match e in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow 
True | (CHead _ _ _) \Rightarrow False])) I (CHead d1 (Flat f) u1) H0) in 
(False_ind ((eq C (CSort n) c) \to (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(eq C c (CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba 
g d1 d2))))) H2)) H1))) | (csuba_head c1 c2 H0 k u) \Rightarrow (\lambda (H1: 
(eq C (CHead c1 k u) (CHead d1 (Flat f) u1))).(\lambda (H2: (eq C (CHead c2 k 
u) c)).((let H3 \def (f_equal C T (\lambda (e: C).(match e in C return 
(\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow 
t])) (CHead c1 k u) (CHead d1 (Flat f) u1) H1) in ((let H4 \def (f_equal C K 
(\lambda (e: C).(match e in C return (\lambda (_: C).K) with [(CSort _) 
\Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) (CHead c1 k u) (CHead d1 
(Flat f) u1) H1) in ((let H5 \def (f_equal C C (\lambda (e: C).(match e in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow c1 | (CHead c0 _ _) 
\Rightarrow c0])) (CHead c1 k u) (CHead d1 (Flat f) u1) H1) in (eq_ind C d1 
(\lambda (c0: C).((eq K k (Flat f)) \to ((eq T u u1) \to ((eq C (CHead c2 k 
u) c) \to ((csuba g c0 c2) \to (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(eq C c (CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba 
g d1 d2))))))))) (\lambda (H6: (eq K k (Flat f))).(eq_ind K (Flat f) (\lambda 
(k0: K).((eq T u u1) \to ((eq C (CHead c2 k0 u) c) \to ((csuba g d1 c2) \to 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c (CHead d2 (Flat f) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d1 d2)))))))) (\lambda (H7: 
(eq T u u1)).(eq_ind T u1 (\lambda (t: T).((eq C (CHead c2 (Flat f) t) c) \to 
((csuba g d1 c2) \to (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c 
(CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d1 
d2))))))) (\lambda (H8: (eq C (CHead c2 (Flat f) u1) c)).(eq_ind C (CHead c2 
(Flat f) u1) (\lambda (c0: C).((csuba g d1 c2) \to (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(eq C c0 (CHead d2 (Flat f) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d1 d2)))))) (\lambda (H9: (csuba g d1 
c2)).(ex2_2_intro C T (\lambda (d2: C).(\lambda (u2: T).(eq C (CHead c2 (Flat 
f) u1) (CHead d2 (Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d1 
d2))) c2 u1 (refl_equal C (CHead c2 (Flat f) u1)) H9)) c H8)) u (sym_eq T u 
u1 H7))) k (sym_eq K k (Flat f) H6))) c1 (sym_eq C c1 d1 H5))) H4)) H3)) H2 
H0))) | (csuba_abst c1 c2 H0 t a H1 u H2) \Rightarrow (\lambda (H3: (eq C 
(CHead c1 (Bind Abst) t) (CHead d1 (Flat f) u1))).(\lambda (H4: (eq C (CHead 
c2 (Bind Abbr) u) c)).((let H5 \def (eq_ind C (CHead c1 (Bind Abst) t) 
(\lambda (e: C).(match e in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow 
False])])) I (CHead d1 (Flat f) u1) H3) in (False_ind ((eq C (CHead c2 (Bind 
Abbr) u) c) \to ((csuba g c1 c2) \to ((arity g c1 t (asucc g a)) \to ((arity 
g c2 u a) \to (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C c (CHead d2 
(Flat f) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d1 d2)))))))) H5)) 
H4 H0 H1 H2)))]) in (H0 (refl_equal C (CHead d1 (Flat f) u1)) (refl_equal C 
c)))))))).

theorem csuba_gen_bind:
 \forall (g: G).(\forall (b1: B).(\forall (e1: C).(\forall (c2: C).(\forall 
(v1: T).((csuba g (CHead e1 (Bind b1) v1) c2) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e1 e2))))))))))
\def
 \lambda (g: G).(\lambda (b1: B).(\lambda (e1: C).(\lambda (c2: C).(\lambda 
(v1: T).(\lambda (H: (csuba g (CHead e1 (Bind b1) v1) c2)).(let H0 \def 
(match H in csuba return (\lambda (c: C).(\lambda (c0: C).(\lambda (_: (csuba 
? c c0)).((eq C c (CHead e1 (Bind b1) v1)) \to ((eq C c0 c2) \to (ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind 
b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e1 
e2)))))))))) with [(csuba_sort n) \Rightarrow (\lambda (H0: (eq C (CSort n) 
(CHead e1 (Bind b1) v1))).(\lambda (H1: (eq C (CSort n) c2)).((let H2 \def 
(eq_ind C (CSort n) (\lambda (e: C).(match e in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow 
False])) I (CHead e1 (Bind b1) v1) H0) in (False_ind ((eq C (CSort n) c2) \to 
(ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 
(CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: 
T).(csuba g e1 e2)))))) H2)) H1))) | (csuba_head c1 c0 H0 k u) \Rightarrow 
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
(CHead c0 k u) c2) \to ((csuba g c c0) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e1 e2)))))))))) 
(\lambda (H6: (eq K k (Bind b1))).(eq_ind K (Bind b1) (\lambda (k0: K).((eq T 
u v1) \to ((eq C (CHead c0 k0 u) c2) \to ((csuba g e1 c0) \to (ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind 
b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e1 
e2))))))))) (\lambda (H7: (eq T u v1)).(eq_ind T v1 (\lambda (t: T).((eq C 
(CHead c0 (Bind b1) t) c2) \to ((csuba g e1 c0) \to (ex2_3 B C T (\lambda 
(b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) 
v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e1 
e2)))))))) (\lambda (H8: (eq C (CHead c0 (Bind b1) v1) c2)).(eq_ind C (CHead 
c0 (Bind b1) v1) (\lambda (c: C).((csuba g e1 c0) \to (ex2_3 B C T (\lambda 
(b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e1 e2))))))) 
(\lambda (H9: (csuba g e1 c0)).(let H10 \def (eq_ind_r C c2 (\lambda (c: 
C).(csuba g (CHead e1 (Bind b1) v1) c)) H (CHead c0 (Bind b1) v1) H8) in 
(ex2_3_intro B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C 
(CHead c0 (Bind b1) v1) (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda 
(e2: C).(\lambda (_: T).(csuba g e1 e2)))) b1 c0 v1 (refl_equal C (CHead c0 
(Bind b1) v1)) H9))) c2 H8)) u (sym_eq T u v1 H7))) k (sym_eq K k (Bind b1) 
H6))) c1 (sym_eq C c1 e1 H5))) H4)) H3)) H2 H0))) | (csuba_abst c1 c0 H0 t a 
H1 u H2) \Rightarrow (\lambda (H3: (eq C (CHead c1 (Bind Abst) t) (CHead e1 
(Bind b1) v1))).(\lambda (H4: (eq C (CHead c0 (Bind Abbr) u) c2)).((let H5 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow t | (CHead _ _ t0) \Rightarrow t0])) (CHead c1 
(Bind Abst) t) (CHead e1 (Bind b1) v1) H3) in ((let H6 \def (f_equal C B 
(\lambda (e: C).(match e in C return (\lambda (_: C).B) with [(CSort _) 
\Rightarrow Abst | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).B) with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow Abst])])) 
(CHead c1 (Bind Abst) t) (CHead e1 (Bind b1) v1) H3) in ((let H7 \def 
(f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) (CHead c1 (Bind 
Abst) t) (CHead e1 (Bind b1) v1) H3) in (eq_ind C e1 (\lambda (c: C).((eq B 
Abst b1) \to ((eq T t v1) \to ((eq C (CHead c0 (Bind Abbr) u) c2) \to ((csuba 
g c c0) \to ((arity g c t (asucc g a)) \to ((arity g c0 u a) \to (ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind 
b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e1 
e2)))))))))))) (\lambda (H8: (eq B Abst b1)).(eq_ind B Abst (\lambda (_: 
B).((eq T t v1) \to ((eq C (CHead c0 (Bind Abbr) u) c2) \to ((csuba g e1 c0) 
\to ((arity g e1 t (asucc g a)) \to ((arity g c0 u a) \to (ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind 
b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e1 
e2))))))))))) (\lambda (H9: (eq T t v1)).(eq_ind T v1 (\lambda (t0: T).((eq C 
(CHead c0 (Bind Abbr) u) c2) \to ((csuba g e1 c0) \to ((arity g e1 t0 (asucc 
g a)) \to ((arity g c0 u a) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: 
C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) v2))))) (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csuba g e1 e2)))))))))) (\lambda (H10: 
(eq C (CHead c0 (Bind Abbr) u) c2)).(eq_ind C (CHead c0 (Bind Abbr) u) 
(\lambda (c: C).((csuba g e1 c0) \to ((arity g e1 v1 (asucc g a)) \to ((arity 
g c0 u a) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: 
T).(eq C c (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csuba g e1 e2))))))))) (\lambda (H11: (csuba g e1 
c0)).(\lambda (_: (arity g e1 v1 (asucc g a))).(\lambda (_: (arity g c0 u 
a)).(let H14 \def (eq_ind_r C c2 (\lambda (c: C).(csuba g (CHead e1 (Bind b1) 
v1) c)) H (CHead c0 (Bind Abbr) u) H10) in (let H15 \def (eq_ind_r B b1 
(\lambda (b: B).(csuba g (CHead e1 (Bind b) v1) (CHead c0 (Bind Abbr) u))) 
H14 Abst H8) in (ex2_3_intro B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda 
(v2: T).(eq C (CHead c0 (Bind Abbr) u) (CHead e2 (Bind b2) v2))))) (\lambda 
(_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e1 e2)))) Abbr c0 u 
(refl_equal C (CHead c0 (Bind Abbr) u)) H11)))))) c2 H10)) t (sym_eq T t v1 
H9))) b1 H8)) c1 (sym_eq C c1 e1 H7))) H6)) H5)) H4 H0 H1 H2)))]) in (H0 
(refl_equal C (CHead e1 (Bind b1) v1)) (refl_equal C c2)))))))).

