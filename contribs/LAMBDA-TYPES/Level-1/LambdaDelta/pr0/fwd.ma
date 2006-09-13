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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr0/fwd".

include "pr0/props.ma".

theorem pr0_gen_sort:
 \forall (x: T).(\forall (n: nat).((pr0 (TSort n) x) \to (eq T x (TSort n))))
\def
 \lambda (x: T).(\lambda (n: nat).(\lambda (H: (pr0 (TSort n) x)).(let H0 
\def (match H in pr0 return (\lambda (t: T).(\lambda (t0: T).(\lambda (_: 
(pr0 t t0)).((eq T t (TSort n)) \to ((eq T t0 x) \to (eq T x (TSort n))))))) 
with [(pr0_refl t) \Rightarrow (\lambda (H0: (eq T t (TSort n))).(\lambda 
(H1: (eq T t x)).(eq_ind T (TSort n) (\lambda (t0: T).((eq T t0 x) \to (eq T 
x (TSort n)))) (\lambda (H2: (eq T (TSort n) x)).(eq_ind T (TSort n) (\lambda 
(t0: T).(eq T t0 (TSort n))) (refl_equal T (TSort n)) x H2)) t (sym_eq T t 
(TSort n) H0) H1))) | (pr0_comp u1 u2 H0 t1 t2 H1 k) \Rightarrow (\lambda 
(H2: (eq T (THead k u1 t1) (TSort n))).(\lambda (H3: (eq T (THead k u2 t2) 
x)).((let H4 \def (eq_ind T (THead k u1 t1) (\lambda (e: T).(match e in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) H2) in 
(False_ind ((eq T (THead k u2 t2) x) \to ((pr0 u1 u2) \to ((pr0 t1 t2) \to 
(eq T x (TSort n))))) H4)) H3 H0 H1))) | (pr0_beta u v1 v2 H0 t1 t2 H1) 
\Rightarrow (\lambda (H2: (eq T (THead (Flat Appl) v1 (THead (Bind Abst) u 
t1)) (TSort n))).(\lambda (H3: (eq T (THead (Bind Abbr) v2 t2) x)).((let H4 
\def (eq_ind T (THead (Flat Appl) v1 (THead (Bind Abst) u t1)) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(TSort n) H2) in (False_ind ((eq T (THead (Bind Abbr) v2 t2) x) \to ((pr0 v1 
v2) \to ((pr0 t1 t2) \to (eq T x (TSort n))))) H4)) H3 H0 H1))) | 
(pr0_upsilon b H0 v1 v2 H1 u1 u2 H2 t1 t2 H3) \Rightarrow (\lambda (H4: (eq T 
(THead (Flat Appl) v1 (THead (Bind b) u1 t1)) (TSort n))).(\lambda (H5: (eq T 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t2)) x)).((let H6 
\def (eq_ind T (THead (Flat Appl) v1 (THead (Bind b) u1 t1)) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(TSort n) H4) in (False_ind ((eq T (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t2)) x) \to ((not (eq B b Abst)) \to ((pr0 v1 v2) \to ((pr0 
u1 u2) \to ((pr0 t1 t2) \to (eq T x (TSort n))))))) H6)) H5 H0 H1 H2 H3))) | 
(pr0_delta u1 u2 H0 t1 t2 H1 w H2) \Rightarrow (\lambda (H3: (eq T (THead 
(Bind Abbr) u1 t1) (TSort n))).(\lambda (H4: (eq T (THead (Bind Abbr) u2 w) 
x)).((let H5 \def (eq_ind T (THead (Bind Abbr) u1 t1) (\lambda (e: T).(match 
e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) 
H3) in (False_ind ((eq T (THead (Bind Abbr) u2 w) x) \to ((pr0 u1 u2) \to 
((pr0 t1 t2) \to ((subst0 O u2 t2 w) \to (eq T x (TSort n)))))) H5)) H4 H0 H1 
H2))) | (pr0_zeta b H0 t1 t2 H1 u) \Rightarrow (\lambda (H2: (eq T (THead 
(Bind b) u (lift (S O) O t1)) (TSort n))).(\lambda (H3: (eq T t2 x)).((let H4 
\def (eq_ind T (THead (Bind b) u (lift (S O) O t1)) (\lambda (e: T).(match e 
in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef 
_) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) H2) in 
(False_ind ((eq T t2 x) \to ((not (eq B b Abst)) \to ((pr0 t1 t2) \to (eq T x 
(TSort n))))) H4)) H3 H0 H1))) | (pr0_epsilon t1 t2 H0 u) \Rightarrow 
(\lambda (H1: (eq T (THead (Flat Cast) u t1) (TSort n))).(\lambda (H2: (eq T 
t2 x)).((let H3 \def (eq_ind T (THead (Flat Cast) u t1) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(TSort n) H1) in (False_ind ((eq T t2 x) \to ((pr0 t1 t2) \to (eq T x (TSort 
n)))) H3)) H2 H0)))]) in (H0 (refl_equal T (TSort n)) (refl_equal T x))))).

theorem pr0_gen_lref:
 \forall (x: T).(\forall (n: nat).((pr0 (TLRef n) x) \to (eq T x (TLRef n))))
\def
 \lambda (x: T).(\lambda (n: nat).(\lambda (H: (pr0 (TLRef n) x)).(let H0 
\def (match H in pr0 return (\lambda (t: T).(\lambda (t0: T).(\lambda (_: 
(pr0 t t0)).((eq T t (TLRef n)) \to ((eq T t0 x) \to (eq T x (TLRef n))))))) 
with [(pr0_refl t) \Rightarrow (\lambda (H0: (eq T t (TLRef n))).(\lambda 
(H1: (eq T t x)).(eq_ind T (TLRef n) (\lambda (t0: T).((eq T t0 x) \to (eq T 
x (TLRef n)))) (\lambda (H2: (eq T (TLRef n) x)).(eq_ind T (TLRef n) (\lambda 
(t0: T).(eq T t0 (TLRef n))) (refl_equal T (TLRef n)) x H2)) t (sym_eq T t 
(TLRef n) H0) H1))) | (pr0_comp u1 u2 H0 t1 t2 H1 k) \Rightarrow (\lambda 
(H2: (eq T (THead k u1 t1) (TLRef n))).(\lambda (H3: (eq T (THead k u2 t2) 
x)).((let H4 \def (eq_ind T (THead k u1 t1) (\lambda (e: T).(match e in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n) H2) in 
(False_ind ((eq T (THead k u2 t2) x) \to ((pr0 u1 u2) \to ((pr0 t1 t2) \to 
(eq T x (TLRef n))))) H4)) H3 H0 H1))) | (pr0_beta u v1 v2 H0 t1 t2 H1) 
\Rightarrow (\lambda (H2: (eq T (THead (Flat Appl) v1 (THead (Bind Abst) u 
t1)) (TLRef n))).(\lambda (H3: (eq T (THead (Bind Abbr) v2 t2) x)).((let H4 
\def (eq_ind T (THead (Flat Appl) v1 (THead (Bind Abst) u t1)) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(TLRef n) H2) in (False_ind ((eq T (THead (Bind Abbr) v2 t2) x) \to ((pr0 v1 
v2) \to ((pr0 t1 t2) \to (eq T x (TLRef n))))) H4)) H3 H0 H1))) | 
(pr0_upsilon b H0 v1 v2 H1 u1 u2 H2 t1 t2 H3) \Rightarrow (\lambda (H4: (eq T 
(THead (Flat Appl) v1 (THead (Bind b) u1 t1)) (TLRef n))).(\lambda (H5: (eq T 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t2)) x)).((let H6 
\def (eq_ind T (THead (Flat Appl) v1 (THead (Bind b) u1 t1)) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(TLRef n) H4) in (False_ind ((eq T (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t2)) x) \to ((not (eq B b Abst)) \to ((pr0 v1 v2) \to ((pr0 
u1 u2) \to ((pr0 t1 t2) \to (eq T x (TLRef n))))))) H6)) H5 H0 H1 H2 H3))) | 
(pr0_delta u1 u2 H0 t1 t2 H1 w H2) \Rightarrow (\lambda (H3: (eq T (THead 
(Bind Abbr) u1 t1) (TLRef n))).(\lambda (H4: (eq T (THead (Bind Abbr) u2 w) 
x)).((let H5 \def (eq_ind T (THead (Bind Abbr) u1 t1) (\lambda (e: T).(match 
e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n) 
H3) in (False_ind ((eq T (THead (Bind Abbr) u2 w) x) \to ((pr0 u1 u2) \to 
((pr0 t1 t2) \to ((subst0 O u2 t2 w) \to (eq T x (TLRef n)))))) H5)) H4 H0 H1 
H2))) | (pr0_zeta b H0 t1 t2 H1 u) \Rightarrow (\lambda (H2: (eq T (THead 
(Bind b) u (lift (S O) O t1)) (TLRef n))).(\lambda (H3: (eq T t2 x)).((let H4 
\def (eq_ind T (THead (Bind b) u (lift (S O) O t1)) (\lambda (e: T).(match e 
in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef 
_) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n) H2) in 
(False_ind ((eq T t2 x) \to ((not (eq B b Abst)) \to ((pr0 t1 t2) \to (eq T x 
(TLRef n))))) H4)) H3 H0 H1))) | (pr0_epsilon t1 t2 H0 u) \Rightarrow 
(\lambda (H1: (eq T (THead (Flat Cast) u t1) (TLRef n))).(\lambda (H2: (eq T 
t2 x)).((let H3 \def (eq_ind T (THead (Flat Cast) u t1) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(TLRef n) H1) in (False_ind ((eq T t2 x) \to ((pr0 t1 t2) \to (eq T x (TLRef 
n)))) H3)) H2 H0)))]) in (H0 (refl_equal T (TLRef n)) (refl_equal T x))))).

theorem pr0_gen_abst:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Bind Abst) u1 
t1) x) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind 
Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr0 t1 t2)))))))
\def
 \lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (H: (pr0 (THead 
(Bind Abst) u1 t1) x)).(let H0 \def (match H in pr0 return (\lambda (t: 
T).(\lambda (t0: T).(\lambda (_: (pr0 t t0)).((eq T t (THead (Bind Abst) u1 
t1)) \to ((eq T t0 x) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T 
x (THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2))))))))) with [(pr0_refl t) 
\Rightarrow (\lambda (H0: (eq T t (THead (Bind Abst) u1 t1))).(\lambda (H1: 
(eq T t x)).(eq_ind T (THead (Bind Abst) u1 t1) (\lambda (t0: T).((eq T t0 x) 
\to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind Abst) 
u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr0 t1 t2)))))) (\lambda (H2: (eq T (THead (Bind Abst) 
u1 t1) x)).(eq_ind T (THead (Bind Abst) u1 t1) (\lambda (t0: T).(ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Bind Abst) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: 
T).(pr0 t1 t2))))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t2: T).(eq T 
(THead (Bind Abst) u1 t1) (THead (Bind Abst) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 
t2))) u1 t1 (refl_equal T (THead (Bind Abst) u1 t1)) (pr0_refl u1) (pr0_refl 
t1)) x H2)) t (sym_eq T t (THead (Bind Abst) u1 t1) H0) H1))) | (pr0_comp u0 
u2 H0 t0 t2 H1 k) \Rightarrow (\lambda (H2: (eq T (THead k u0 t0) (THead 
(Bind Abst) u1 t1))).(\lambda (H3: (eq T (THead k u2 t2) x)).((let H4 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t) 
\Rightarrow t])) (THead k u0 t0) (THead (Bind Abst) u1 t1) H2) in ((let H5 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead _ t _) 
\Rightarrow t])) (THead k u0 t0) (THead (Bind Abst) u1 t1) H2) in ((let H6 
\def (f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) 
with [(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | (THead k0 _ _) 
\Rightarrow k0])) (THead k u0 t0) (THead (Bind Abst) u1 t1) H2) in (eq_ind K 
(Bind Abst) (\lambda (k0: K).((eq T u0 u1) \to ((eq T t0 t1) \to ((eq T 
(THead k0 u2 t2) x) \to ((pr0 u0 u2) \to ((pr0 t0 t2) \to (ex3_2 T T (\lambda 
(u3: T).(\lambda (t3: T).(eq T x (THead (Bind Abst) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))))))))) (\lambda (H7: (eq T u0 u1)).(eq_ind T u1 (\lambda (t: T).((eq T 
t0 t1) \to ((eq T (THead (Bind Abst) u2 t2) x) \to ((pr0 t u2) \to ((pr0 t0 
t2) \to (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abst) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3))))))))) (\lambda (H8: (eq T t0 t1)).(eq_ind T 
t1 (\lambda (t: T).((eq T (THead (Bind Abst) u2 t2) x) \to ((pr0 u1 u2) \to 
((pr0 t t2) \to (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T x (THead 
(Bind Abst) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))))))) (\lambda (H9: (eq T (THead (Bind 
Abst) u2 t2) x)).(eq_ind T (THead (Bind Abst) u2 t2) (\lambda (t: T).((pr0 u1 
u2) \to ((pr0 t1 t2) \to (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t 
(THead (Bind Abst) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) 
(\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))))))) (\lambda (H10: (pr0 u1 
u2)).(\lambda (H11: (pr0 t1 t2)).(ex3_2_intro T T (\lambda (u3: T).(\lambda 
(t3: T).(eq T (THead (Bind Abst) u2 t2) (THead (Bind Abst) u3 t3)))) (\lambda 
(u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 
t1 t3))) u2 t2 (refl_equal T (THead (Bind Abst) u2 t2)) H10 H11))) x H9)) t0 
(sym_eq T t0 t1 H8))) u0 (sym_eq T u0 u1 H7))) k (sym_eq K k (Bind Abst) 
H6))) H5)) H4)) H3 H0 H1))) | (pr0_beta u v1 v2 H0 t0 t2 H1) \Rightarrow 
(\lambda (H2: (eq T (THead (Flat Appl) v1 (THead (Bind Abst) u t0)) (THead 
(Bind Abst) u1 t1))).(\lambda (H3: (eq T (THead (Bind Abbr) v2 t2) x)).((let 
H4 \def (eq_ind T (THead (Flat Appl) v1 (THead (Bind Abst) u t0)) (\lambda 
(e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K 
return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) I (THead (Bind Abst) u1 t1) H2) in (False_ind ((eq T 
(THead (Bind Abbr) v2 t2) x) \to ((pr0 v1 v2) \to ((pr0 t0 t2) \to (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abst) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))))))) H4)) H3 H0 H1))) | (pr0_upsilon b H0 v1 v2 H1 u0 u2 H2 
t0 t2 H3) \Rightarrow (\lambda (H4: (eq T (THead (Flat Appl) v1 (THead (Bind 
b) u0 t0)) (THead (Bind Abst) u1 t1))).(\lambda (H5: (eq T (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t2)) x)).((let H6 \def (eq_ind T (THead 
(Flat Appl) v1 (THead (Bind b) u0 t0)) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind Abst) u1 t1) H4) in (False_ind ((eq T (THead (Bind 
b) u2 (THead (Flat Appl) (lift (S O) O v2) t2)) x) \to ((not (eq B b Abst)) 
\to ((pr0 v1 v2) \to ((pr0 u0 u2) \to ((pr0 t0 t2) \to (ex3_2 T T (\lambda 
(u3: T).(\lambda (t3: T).(eq T x (THead (Bind Abst) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3))))))))) H6)) H5 H0 H1 H2 H3))) | (pr0_delta u0 u2 H0 t0 t2 H1 w H2) 
\Rightarrow (\lambda (H3: (eq T (THead (Bind Abbr) u0 t0) (THead (Bind Abst) 
u1 t1))).(\lambda (H4: (eq T (THead (Bind Abbr) u2 w) x)).((let H5 \def 
(eq_ind T (THead (Bind Abbr) u0 t0) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b) \Rightarrow (match b in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow True | Abst \Rightarrow False | Void 
\Rightarrow False]) | (Flat _) \Rightarrow False])])) I (THead (Bind Abst) u1 
t1) H3) in (False_ind ((eq T (THead (Bind Abbr) u2 w) x) \to ((pr0 u0 u2) \to 
((pr0 t0 t2) \to ((subst0 O u2 t2 w) \to (ex3_2 T T (\lambda (u3: T).(\lambda 
(t3: T).(eq T x (THead (Bind Abst) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))))))) H5)) H4 
H0 H1 H2))) | (pr0_zeta b H0 t0 t2 H1 u) \Rightarrow (\lambda (H2: (eq T 
(THead (Bind b) u (lift (S O) O t0)) (THead (Bind Abst) u1 t1))).(\lambda 
(H3: (eq T t2 x)).((let H4 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map (f: 
((nat \to nat))) (d: nat) (t: T) on t: T \def (match t with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t3) 
\Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t3))]) in 
lref_map) (\lambda (x0: nat).(plus x0 (S O))) O t0) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t: T) on t: T \def (match t 
with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match 
(blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 
t3) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t3))]) in 
lref_map) (\lambda (x0: nat).(plus x0 (S O))) O t0) | (THead _ _ t) 
\Rightarrow t])) (THead (Bind b) u (lift (S O) O t0)) (THead (Bind Abst) u1 
t1) H2) in ((let H5 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow u | (TLRef _) \Rightarrow u | 
(THead _ t _) \Rightarrow t])) (THead (Bind b) u (lift (S O) O t0)) (THead 
(Bind Abst) u1 t1) H2) in ((let H6 \def (f_equal T B (\lambda (e: T).(match e 
in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow b | (TLRef _) 
\Rightarrow b | (THead k _ _) \Rightarrow (match k in K return (\lambda (_: 
K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow b])])) (THead 
(Bind b) u (lift (S O) O t0)) (THead (Bind Abst) u1 t1) H2) in (eq_ind B Abst 
(\lambda (b0: B).((eq T u u1) \to ((eq T (lift (S O) O t0) t1) \to ((eq T t2 
x) \to ((not (eq B b0 Abst)) \to ((pr0 t0 t2) \to (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abst) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))))))))) (\lambda (H7: (eq T u u1)).(eq_ind T u1 (\lambda (_: T).((eq T 
(lift (S O) O t0) t1) \to ((eq T t2 x) \to ((not (eq B Abst Abst)) \to ((pr0 
t0 t2) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3))))))))) (\lambda (H8: (eq T (lift (S O) O t0) 
t1)).(eq_ind T (lift (S O) O t0) (\lambda (t: T).((eq T t2 x) \to ((not (eq B 
Abst Abst)) \to ((pr0 t0 t2) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 
u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t t3)))))))) (\lambda (H9: (eq 
T t2 x)).(eq_ind T x (\lambda (t: T).((not (eq B Abst Abst)) \to ((pr0 t0 t) 
\to (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abst) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 (lift (S O) O t0) t3))))))) (\lambda (H10: (not (eq 
B Abst Abst))).(\lambda (_: (pr0 t0 x)).(False_ind (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abst) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 (lift 
(S O) O t0) t3)))) (H10 (refl_equal B Abst))))) t2 (sym_eq T t2 x H9))) t1 
H8)) u (sym_eq T u u1 H7))) b (sym_eq B b Abst H6))) H5)) H4)) H3 H0 H1))) | 
(pr0_epsilon t0 t2 H0 u) \Rightarrow (\lambda (H1: (eq T (THead (Flat Cast) u 
t0) (THead (Bind Abst) u1 t1))).(\lambda (H2: (eq T t2 x)).((let H3 \def 
(eq_ind T (THead (Flat Cast) u t0) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind Abst) u1 t1) H1) in (False_ind ((eq T t2 x) \to 
((pr0 t0 t2) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead 
(Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))))) H3)) H2 H0)))]) in (H0 (refl_equal T 
(THead (Bind Abst) u1 t1)) (refl_equal T x)))))).

theorem pr0_gen_appl:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Flat Appl) u1 
t1) x) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Bind Abbr) u2 t2)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (v2: T).(\lambda (t2: T).(eq T x (THead (Bind b) 
v2 (THead (Flat Appl) (lift (S O) O u2) t2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t2: T).(pr0 z1 t2))))))))))))
\def
 \lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (H: (pr0 (THead 
(Flat Appl) u1 t1) x)).(let H0 \def (match H in pr0 return (\lambda (t: 
T).(\lambda (t0: T).(\lambda (_: (pr0 t t0)).((eq T t (THead (Flat Appl) u1 
t1)) \to ((eq T t0 x) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 
u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (v2: T).(\lambda (t2: T).(eq T x 
(THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O u2) t2))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(\lambda (_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 
v2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))))))))))) with [(pr0_refl 
t) \Rightarrow (\lambda (H0: (eq T t (THead (Flat Appl) u1 t1))).(\lambda 
(H1: (eq T t x)).(eq_ind T (THead (Flat Appl) u1 t1) (\lambda (t0: T).((eq T 
t0 x) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Bind Abbr) u2 t2)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (v2: T).(\lambda (t2: T).(eq T x (THead (Bind b) 
v2 (THead (Flat Appl) (lift (S O) O u2) t2))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t2: T).(pr0 z1 t2))))))))))) (\lambda (H2: (eq T (THead (Flat Appl) u1 t1) 
x)).(eq_ind T (THead (Flat Appl) u1 t1) (\lambda (t0: T).(or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Flat Appl) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: 
T).(pr0 t1 t2)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Bind 
Abbr) u2 t2)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t2: T).(pr0 z1 t2)))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (v2: T).(\lambda (t2: T).(eq T t0 (THead (Bind b) v2 (THead 
(Flat Appl) (lift (S O) O u2) t2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t2: T).(pr0 z1 t2)))))))))) (or3_intro0 (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T (THead (Flat Appl) u1 t1) (THead (Flat Appl) u2 t2)))) (\lambda 
(u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 
t1 t2)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t2: T).(eq T (THead (Flat Appl) 
u1 t1) (THead (Bind Abbr) u2 t2)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (v2: T).(\lambda (t2: T).(eq T (THead (Flat 
Appl) u1 t1) (THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O u2) 
t2))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda 
(y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 
y1 v2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))))) (ex3_2_intro T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T (THead (Flat Appl) u1 t1) (THead 
(Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2))) u1 t1 (refl_equal T (THead (Flat Appl) 
u1 t1)) (pr0_refl u1) (pr0_refl t1))) x H2)) t (sym_eq T t (THead (Flat Appl) 
u1 t1) H0) H1))) | (pr0_comp u0 u2 H0 t0 t2 H1 k) \Rightarrow (\lambda (H2: 
(eq T (THead k u0 t0) (THead (Flat Appl) u1 t1))).(\lambda (H3: (eq T (THead 
k u2 t2) x)).((let H4 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 
| (THead _ _ t) \Rightarrow t])) (THead k u0 t0) (THead (Flat Appl) u1 t1) 
H2) in ((let H5 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow u0 | (TLRef _) \Rightarrow u0 
| (THead _ t _) \Rightarrow t])) (THead k u0 t0) (THead (Flat Appl) u1 t1) 
H2) in ((let H6 \def (f_equal T K (\lambda (e: T).(match e in T return 
(\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | 
(THead k0 _ _) \Rightarrow k0])) (THead k u0 t0) (THead (Flat Appl) u1 t1) 
H2) in (eq_ind K (Flat Appl) (\lambda (k0: K).((eq T u0 u1) \to ((eq T t0 t1) 
\to ((eq T (THead k0 u2 t2) x) \to ((pr0 u0 u2) \to ((pr0 t0 t2) \to (or3 
(ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (v2: T).(\lambda (t3: T).(eq T x (THead (Bind b) 
v2 (THead (Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 
u1 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3))))))))))))))) (\lambda (H7: (eq T u0 u1)).(eq_ind T u1 
(\lambda (t: T).((eq T t0 t1) \to ((eq T (THead (Flat Appl) u2 t2) x) \to 
((pr0 t u2) \to ((pr0 t0 t2) \to (or3 (ex3_2 T T (\lambda (u3: T).(\lambda 
(t3: T).(eq T x (THead (Flat Appl) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T 
T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u3 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (v2: T).(\lambda (t3: T).(eq T x 
(THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: 
T).(\lambda (_: T).(pr0 u1 u3))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 
v2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))))))))))) (\lambda (H8: 
(eq T t0 t1)).(eq_ind T t1 (\lambda (t: T).((eq T (THead (Flat Appl) u2 t2) 
x) \to ((pr0 u1 u2) \to ((pr0 t t2) \to (or3 (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (v2: T).(\lambda (t3: T).(eq T x (THead (Bind b) v2 (THead 
(Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3))))))))))))) (\lambda (H9: (eq T (THead (Flat Appl) u2 t2) 
x)).(eq_ind T (THead (Flat Appl) u2 t2) (\lambda (t: T).((pr0 u1 u2) \to 
((pr0 t1 t2) \to (or3 (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t 
(THead (Flat Appl) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) 
(\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(t3: T).(eq T t (THead (Bind Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (v2: T).(\lambda (t3: T).(eq T t (THead (Bind b) 
v2 (THead (Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 
u1 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3)))))))))))) (\lambda (H10: (pr0 u1 u2)).(\lambda (H11: 
(pr0 t1 t2)).(or3_intro0 (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T 
(THead (Flat Appl) u2 t2) (THead (Flat Appl) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Flat Appl) 
u2 t2) (THead (Bind Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (v2: T).(\lambda (t3: T).(eq T (THead (Flat 
Appl) u2 t2) (THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O u3) 
t3))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 u3))))))) (\lambda (_: B).(\lambda 
(y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 
y1 v2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))))) (ex3_2_intro T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Flat Appl) u2 t2) (THead 
(Flat Appl) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3))) u2 t2 (refl_equal T (THead (Flat Appl) 
u2 t2)) H10 H11)))) x H9)) t0 (sym_eq T t0 t1 H8))) u0 (sym_eq T u0 u1 H7))) 
k (sym_eq K k (Flat Appl) H6))) H5)) H4)) H3 H0 H1))) | (pr0_beta u v1 v2 H0 
t0 t2 H1) \Rightarrow (\lambda (H2: (eq T (THead (Flat Appl) v1 (THead (Bind 
Abst) u t0)) (THead (Flat Appl) u1 t1))).(\lambda (H3: (eq T (THead (Bind 
Abbr) v2 t2) x)).((let H4 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow (THead (Bind Abst) u 
t0) | (TLRef _) \Rightarrow (THead (Bind Abst) u t0) | (THead _ _ t) 
\Rightarrow t])) (THead (Flat Appl) v1 (THead (Bind Abst) u t0)) (THead (Flat 
Appl) u1 t1) H2) in ((let H5 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow v1 | (TLRef _) 
\Rightarrow v1 | (THead _ t _) \Rightarrow t])) (THead (Flat Appl) v1 (THead 
(Bind Abst) u t0)) (THead (Flat Appl) u1 t1) H2) in (eq_ind T u1 (\lambda (t: 
T).((eq T (THead (Bind Abst) u t0) t1) \to ((eq T (THead (Bind Abbr) v2 t2) 
x) \to ((pr0 t v2) \to ((pr0 t0 t2) \to (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (v3: T).(\lambda (t3: T).(eq T x (THead (Bind b) v3 (THead 
(Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3)))))))))))))) (\lambda (H6: (eq T (THead (Bind Abst) u t0) 
t1)).(eq_ind T (THead (Bind Abst) u t0) (\lambda (t: T).((eq T (THead (Bind 
Abbr) v2 t2) x) \to ((pr0 u1 v2) \to ((pr0 t0 t2) \to (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(eq T t (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (v3: T).(\lambda (t3: T).(eq T x (THead (Bind b) v3 (THead 
(Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3))))))))))))) (\lambda (H7: (eq T (THead (Bind Abbr) v2 t2) 
x)).(eq_ind T (THead (Bind Abbr) v2 t2) (\lambda (t: T).((pr0 u1 v2) \to 
((pr0 t0 t2) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t 
(THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr0 (THead (Bind Abst) u t0) t3)))) (ex4_4 
T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq 
T (THead (Bind Abst) u t0) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind 
Abst) u t0) (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (v3: T).(\lambda (t3: T).(eq T t 
(THead (Bind b) v3 (THead (Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda 
(_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(\lambda (_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 
v3))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))))))))) (\lambda (H8: (pr0 
u1 v2)).(\lambda (H9: (pr0 t0 t2)).(or3_intro1 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) v2 t2) (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 (THead (Bind Abst) u t0) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind Abst) u t0) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) 
v2 t2) (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind Abst) u t0) (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (v3: T).(\lambda 
(t3: T).(eq T (THead (Bind Abbr) v2 t2) (THead (Bind b) v3 (THead (Flat Appl) 
(lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 
t3)))))))) (ex4_4_intro T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(eq T (THead (Bind Abst) u t0) (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind Abbr) v2 t2) (THead (Bind Abbr) u2 t3)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 
t3))))) u t0 v2 t2 (refl_equal T (THead (Bind Abst) u t0)) (refl_equal T 
(THead (Bind Abbr) v2 t2)) H8 H9)))) x H7)) t1 H6)) v1 (sym_eq T v1 u1 H5))) 
H4)) H3 H0 H1))) | (pr0_upsilon b H0 v1 v2 H1 u0 u2 H2 t0 t2 H3) \Rightarrow 
(\lambda (H4: (eq T (THead (Flat Appl) v1 (THead (Bind b) u0 t0)) (THead 
(Flat Appl) u1 t1))).(\lambda (H5: (eq T (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t2)) x)).((let H6 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow (THead 
(Bind b) u0 t0) | (TLRef _) \Rightarrow (THead (Bind b) u0 t0) | (THead _ _ 
t) \Rightarrow t])) (THead (Flat Appl) v1 (THead (Bind b) u0 t0)) (THead 
(Flat Appl) u1 t1) H4) in ((let H7 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow v1 | (TLRef _) 
\Rightarrow v1 | (THead _ t _) \Rightarrow t])) (THead (Flat Appl) v1 (THead 
(Bind b) u0 t0)) (THead (Flat Appl) u1 t1) H4) in (eq_ind T u1 (\lambda (t: 
T).((eq T (THead (Bind b) u0 t0) t1) \to ((eq T (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t2)) x) \to ((not (eq B b Abst)) \to ((pr0 t 
v2) \to ((pr0 u0 u2) \to ((pr0 t0 t2) \to (or3 (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b0: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (v3: T).(\lambda (t3: T).(eq T x (THead (Bind b0) v3 (THead 
(Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3)))))))))))))))) (\lambda (H8: (eq T (THead (Bind b) u0 t0) 
t1)).(eq_ind T (THead (Bind b) u0 t0) (\lambda (t: T).((eq T (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t2)) x) \to ((not (eq B b Abst)) \to 
((pr0 u1 v2) \to ((pr0 u0 u2) \to ((pr0 t0 t2) \to (or3 (ex3_2 T T (\lambda 
(u3: T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t 
t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b0: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t (THead (Bind 
b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (v3: T).(\lambda (t3: T).(eq T x (THead (Bind b0) v3 (THead 
(Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3))))))))))))))) (\lambda (H9: (eq T (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t2)) x)).(eq_ind T (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t2)) (\lambda (t: T).((not (eq B b 
Abst)) \to ((pr0 u1 v2) \to ((pr0 u0 u2) \to ((pr0 t0 t2) \to (or3 (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T t (THead (Flat Appl) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 (THead (Bind b) u0 t0) t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind b) u0 
t0) (THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u3 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) 
(ex6_6 B T T T T T (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b0 Abst)))))))) (\lambda 
(b0: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (THead (Bind b) u0 t0) (THead (Bind b0) y1 
z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (v3: T).(\lambda (t3: T).(eq T t (THead (Bind b0) v3 (THead (Flat 
Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 u3))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 
t3)))))))))))))) (\lambda (H10: (not (eq B b Abst))).(\lambda (H11: (pr0 u1 
v2)).(\lambda (H12: (pr0 u0 u2)).(\lambda (H13: (pr0 t0 t2)).(or3_intro2 
(ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t2)) (THead (Flat Appl) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 (THead 
(Bind b) u0 t0) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind b) u0 t0) (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(t3: T).(eq T (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t2)) 
(THead (Bind Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b0: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind b) 
u0 t0) (THead (Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (v3: T).(\lambda (t3: T).(eq T 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t2)) (THead (Bind b0) 
v3 (THead (Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 
u1 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3)))))))) (ex6_6_intro B T T T T T (\lambda (b0: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not 
(eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind b) u0 
t0) (THead (Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u3: T).(\lambda (v3: T).(\lambda (t3: T).(eq T (THead (Bind 
b) u2 (THead (Flat Appl) (lift (S O) O v2) t2)) (THead (Bind b0) v3 (THead 
(Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3))))))) b u0 t0 v2 u2 t2 H10 (refl_equal T (THead (Bind b) 
u0 t0)) (refl_equal T (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) 
t2))) H11 H12 H13)))))) x H9)) t1 H8)) v1 (sym_eq T v1 u1 H7))) H6)) H5 H0 H1 
H2 H3))) | (pr0_delta u0 u2 H0 t0 t2 H1 w H2) \Rightarrow (\lambda (H3: (eq T 
(THead (Bind Abbr) u0 t0) (THead (Flat Appl) u1 t1))).(\lambda (H4: (eq T 
(THead (Bind Abbr) u2 w) x)).((let H5 \def (eq_ind T (THead (Bind Abbr) u0 
t0) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat Appl) u1 
t1) H3) in (False_ind ((eq T (THead (Bind Abbr) u2 w) x) \to ((pr0 u0 u2) \to 
((pr0 t0 t2) \to ((subst0 O u2 t2 w) \to (or3 (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (v2: T).(\lambda (t3: T).(eq T x (THead (Bind b) v2 (THead 
(Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3))))))))))))) H5)) H4 H0 H1 H2))) | (pr0_zeta b H0 t0 t2 H1 
u) \Rightarrow (\lambda (H2: (eq T (THead (Bind b) u (lift (S O) O t0)) 
(THead (Flat Appl) u1 t1))).(\lambda (H3: (eq T t2 x)).((let H4 \def (eq_ind 
T (THead (Bind b) u (lift (S O) O t0)) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow 
False])])) I (THead (Flat Appl) u1 t1) H2) in (False_ind ((eq T t2 x) \to 
((not (eq B b Abst)) \to ((pr0 t0 t2) \to (or3 (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b0: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (v2: T).(\lambda (t3: T).(eq T x (THead (Bind b0) v2 (THead 
(Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3)))))))))))) H4)) H3 H0 H1))) | (pr0_epsilon t0 t2 H0 u) 
\Rightarrow (\lambda (H1: (eq T (THead (Flat Cast) u t0) (THead (Flat Appl) 
u1 t1))).(\lambda (H2: (eq T t2 x)).((let H3 \def (eq_ind T (THead (Flat 
Cast) u t0) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat f) \Rightarrow (match f in F return (\lambda (_: 
F).Prop) with [Appl \Rightarrow False | Cast \Rightarrow True])])])) I (THead 
(Flat Appl) u1 t1) H1) in (False_ind ((eq T t2 x) \to ((pr0 t0 t2) \to (or3 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Appl) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (v2: T).(\lambda (t3: T).(eq T x (THead (Bind b) 
v2 (THead (Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 
u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3))))))))))) H3)) H2 H0)))]) in (H0 (refl_equal T (THead 
(Flat Appl) u1 t1)) (refl_equal T x)))))).

theorem pr0_gen_cast:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Flat Cast) u1 
t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 x)))))
\def
 \lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (H: (pr0 (THead 
(Flat Cast) u1 t1) x)).(let H0 \def (match H in pr0 return (\lambda (t: 
T).(\lambda (t0: T).(\lambda (_: (pr0 t t0)).((eq T t (THead (Flat Cast) u1 
t1)) \to ((eq T t0 x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 
u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 x))))))) 
with [(pr0_refl t) \Rightarrow (\lambda (H0: (eq T t (THead (Flat Cast) u1 
t1))).(\lambda (H1: (eq T t x)).(eq_ind T (THead (Flat Cast) u1 t1) (\lambda 
(t0: T).((eq T t0 x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq 
T x (THead (Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 
u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 x)))) (\lambda 
(H2: (eq T (THead (Flat Cast) u1 t1) x)).(eq_ind T (THead (Flat Cast) u1 t1) 
(\lambda (t0: T).(or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T t0 
(THead (Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 t0))) (or_introl 
(ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T (THead (Flat Cast) u1 t1) 
(THead (Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (THead (Flat Cast) u1 
t1)) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t2: T).(eq T (THead (Flat 
Cast) u1 t1) (THead (Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2))) u1 t1 
(refl_equal T (THead (Flat Cast) u1 t1)) (pr0_refl u1) (pr0_refl t1))) x H2)) 
t (sym_eq T t (THead (Flat Cast) u1 t1) H0) H1))) | (pr0_comp u0 u2 H0 t0 t2 
H1 k) \Rightarrow (\lambda (H2: (eq T (THead k u0 t0) (THead (Flat Cast) u1 
t1))).(\lambda (H3: (eq T (THead k u2 t2) x)).((let H4 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t) \Rightarrow t])) 
(THead k u0 t0) (THead (Flat Cast) u1 t1) H2) in ((let H5 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead _ t _) \Rightarrow t])) 
(THead k u0 t0) (THead (Flat Cast) u1 t1) H2) in ((let H6 \def (f_equal T K 
(\lambda (e: T).(match e in T return (\lambda (_: T).K) with [(TSort _) 
\Rightarrow k | (TLRef _) \Rightarrow k | (THead k0 _ _) \Rightarrow k0])) 
(THead k u0 t0) (THead (Flat Cast) u1 t1) H2) in (eq_ind K (Flat Cast) 
(\lambda (k0: K).((eq T u0 u1) \to ((eq T t0 t1) \to ((eq T (THead k0 u2 t2) 
x) \to ((pr0 u0 u2) \to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 x)))))))) (\lambda (H7: (eq T u0 u1)).(eq_ind T u1 (\lambda 
(t: T).((eq T t0 t1) \to ((eq T (THead (Flat Cast) u2 t2) x) \to ((pr0 t u2) 
\to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T x 
(THead (Flat Cast) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) 
(\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 x))))))) (\lambda 
(H8: (eq T t0 t1)).(eq_ind T t1 (\lambda (t: T).((eq T (THead (Flat Cast) u2 
t2) x) \to ((pr0 u1 u2) \to ((pr0 t t2) \to (or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 x)))))) (\lambda (H9: (eq T (THead (Flat Cast) u2 t2) 
x)).(eq_ind T (THead (Flat Cast) u2 t2) (\lambda (t: T).((pr0 u1 u2) \to 
((pr0 t1 t2) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t 
(THead (Flat Cast) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) 
(\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 t))))) (\lambda (H10: 
(pr0 u1 u2)).(\lambda (H11: (pr0 t1 t2)).(or_introl (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T (THead (Flat Cast) u2 t2) (THead (Flat Cast) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (THead (Flat Cast) u2 t2)) 
(ex3_2_intro T T (\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Flat Cast) 
u2 t2) (THead (Flat Cast) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 
u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))) u2 t2 (refl_equal T 
(THead (Flat Cast) u2 t2)) H10 H11)))) x H9)) t0 (sym_eq T t0 t1 H8))) u0 
(sym_eq T u0 u1 H7))) k (sym_eq K k (Flat Cast) H6))) H5)) H4)) H3 H0 H1))) | 
(pr0_beta u v1 v2 H0 t0 t2 H1) \Rightarrow (\lambda (H2: (eq T (THead (Flat 
Appl) v1 (THead (Bind Abst) u t0)) (THead (Flat Cast) u1 t1))).(\lambda (H3: 
(eq T (THead (Bind Abbr) v2 t2) x)).((let H4 \def (eq_ind T (THead (Flat 
Appl) v1 (THead (Bind Abst) u t0)) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat f) \Rightarrow (match f 
in F return (\lambda (_: F).Prop) with [Appl \Rightarrow True | Cast 
\Rightarrow False])])])) I (THead (Flat Cast) u1 t1) H2) in (False_ind ((eq T 
(THead (Bind Abbr) v2 t2) x) \to ((pr0 v1 v2) \to ((pr0 t0 t2) \to (or (ex3_2 
T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))) (pr0 t1 x))))) H4)) H3 H0 H1))) | (pr0_upsilon b H0 v1 v2 
H1 u0 u2 H2 t0 t2 H3) \Rightarrow (\lambda (H4: (eq T (THead (Flat Appl) v1 
(THead (Bind b) u0 t0)) (THead (Flat Cast) u1 t1))).(\lambda (H5: (eq T 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t2)) x)).((let H6 
\def (eq_ind T (THead (Flat Appl) v1 (THead (Bind b) u0 t0)) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K 
return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat f) 
\Rightarrow (match f in F return (\lambda (_: F).Prop) with [Appl \Rightarrow 
True | Cast \Rightarrow False])])])) I (THead (Flat Cast) u1 t1) H4) in 
(False_ind ((eq T (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) 
t2)) x) \to ((not (eq B b Abst)) \to ((pr0 v1 v2) \to ((pr0 u0 u2) \to ((pr0 
t0 t2) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T x (THead 
(Flat Cast) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 x))))))) H6)) H5 H0 H1 H2 
H3))) | (pr0_delta u0 u2 H0 t0 t2 H1 w H2) \Rightarrow (\lambda (H3: (eq T 
(THead (Bind Abbr) u0 t0) (THead (Flat Cast) u1 t1))).(\lambda (H4: (eq T 
(THead (Bind Abbr) u2 w) x)).((let H5 \def (eq_ind T (THead (Bind Abbr) u0 
t0) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat Cast) u1 
t1) H3) in (False_ind ((eq T (THead (Bind Abbr) u2 w) x) \to ((pr0 u0 u2) \to 
((pr0 t0 t2) \to ((subst0 O u2 t2 w) \to (or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 x)))))) H5)) H4 H0 H1 H2))) | (pr0_zeta b H0 t0 t2 H1 u) 
\Rightarrow (\lambda (H2: (eq T (THead (Bind b) u (lift (S O) O t0)) (THead 
(Flat Cast) u1 t1))).(\lambda (H3: (eq T t2 x)).((let H4 \def (eq_ind T 
(THead (Bind b) u (lift (S O) O t0)) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow 
False])])) I (THead (Flat Cast) u1 t1) H2) in (False_ind ((eq T t2 x) \to 
((not (eq B b Abst)) \to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 x))))) H4)) H3 H0 H1))) | (pr0_epsilon t0 t2 H0 u) \Rightarrow 
(\lambda (H1: (eq T (THead (Flat Cast) u t0) (THead (Flat Cast) u1 
t1))).(\lambda (H2: (eq T t2 x)).((let H3 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | 
(TLRef _) \Rightarrow t0 | (THead _ _ t) \Rightarrow t])) (THead (Flat Cast) 
u t0) (THead (Flat Cast) u1 t1) H1) in ((let H4 \def (f_equal T T (\lambda 
(e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u 
| (TLRef _) \Rightarrow u | (THead _ t _) \Rightarrow t])) (THead (Flat Cast) 
u t0) (THead (Flat Cast) u1 t1) H1) in (eq_ind T u1 (\lambda (_: T).((eq T t0 
t1) \to ((eq T t2 x) \to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 x)))))) (\lambda (H5: (eq T t0 t1)).(eq_ind T t1 (\lambda (t: 
T).((eq T t2 x) \to ((pr0 t t2) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 
x))))) (\lambda (H6: (eq T t2 x)).(eq_ind T x (\lambda (t: T).((pr0 t1 t) \to 
(or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Flat Cast) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 x)))) (\lambda (H7: (pr0 t1 
x)).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead 
(Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 x) H7)) t2 (sym_eq T t2 x 
H6))) t0 (sym_eq T t0 t1 H5))) u (sym_eq T u u1 H4))) H3)) H2 H0)))]) in (H0 
(refl_equal T (THead (Flat Cast) u1 t1)) (refl_equal T x)))))).

theorem pr0_gen_abbr:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Bind Abbr) u1 
t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(u2: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda (y: T).(pr0 t1 y)) 
(\lambda (y: T).(subst0 O u2 y t2))))))) (pr0 t1 (lift (S O) O x))))))
\def
 \lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (H: (pr0 (THead 
(Bind Abbr) u1 t1) x)).(let H0 \def (match H in pr0 return (\lambda (t: 
T).(\lambda (t0: T).(\lambda (_: (pr0 t t0)).((eq T t (THead (Bind Abbr) u1 
t1)) \to ((eq T t0 x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 
u1 u2))) (\lambda (u2: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda 
(y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O u2 y t2))))))) (pr0 t1 (lift (S 
O) O x)))))))) with [(pr0_refl t) \Rightarrow (\lambda (H0: (eq T t (THead 
(Bind Abbr) u1 t1))).(\lambda (H1: (eq T t x)).(eq_ind T (THead (Bind Abbr) 
u1 t1) (\lambda (t0: T).((eq T t0 x) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t2: T).(or (pr0 
t1 t2) (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O u2 y 
t2))))))) (pr0 t1 (lift (S O) O x))))) (\lambda (H2: (eq T (THead (Bind Abbr) 
u1 t1) x)).(eq_ind T (THead (Bind Abbr) u1 t1) (\lambda (t0: T).(or (ex3_2 T 
T (\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Bind Abbr) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t2: 
T).(or (pr0 t1 t2) (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 
O u2 y t2))))))) (pr0 t1 (lift (S O) O t0)))) (or_introl (ex3_2 T T (\lambda 
(u2: T).(\lambda (t2: T).(eq T (THead (Bind Abbr) u1 t1) (THead (Bind Abbr) 
u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda (y: T).(pr0 t1 y)) 
(\lambda (y: T).(subst0 O u2 y t2))))))) (pr0 t1 (lift (S O) O (THead (Bind 
Abbr) u1 t1))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t2: T).(eq T 
(THead (Bind Abbr) u1 t1) (THead (Bind Abbr) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t2: T).(or (pr0 
t1 t2) (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O u2 y 
t2)))))) u1 t1 (refl_equal T (THead (Bind Abbr) u1 t1)) (pr0_refl u1) 
(or_introl (pr0 t1 t1) (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: 
T).(subst0 O u1 y t1))) (pr0_refl t1)))) x H2)) t (sym_eq T t (THead (Bind 
Abbr) u1 t1) H0) H1))) | (pr0_comp u0 u2 H0 t0 t2 H1 k) \Rightarrow (\lambda 
(H2: (eq T (THead k u0 t0) (THead (Bind Abbr) u1 t1))).(\lambda (H3: (eq T 
(THead k u2 t2) x)).((let H4 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | (TLRef _) 
\Rightarrow t0 | (THead _ _ t) \Rightarrow t])) (THead k u0 t0) (THead (Bind 
Abbr) u1 t1) H2) in ((let H5 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow u0 | (TLRef _) 
\Rightarrow u0 | (THead _ t _) \Rightarrow t])) (THead k u0 t0) (THead (Bind 
Abbr) u1 t1) H2) in ((let H6 \def (f_equal T K (\lambda (e: T).(match e in T 
return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k0 _ _) \Rightarrow k0])) (THead k u0 t0) (THead (Bind 
Abbr) u1 t1) H2) in (eq_ind K (Bind Abbr) (\lambda (k0: K).((eq T u0 u1) \to 
((eq T t0 t1) \to ((eq T (THead k0 u2 t2) x) \to ((pr0 u0 u2) \to ((pr0 t0 
t2) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y: T).(pr0 t1 y)) 
(\lambda (y: T).(subst0 O u3 y t3))))))) (pr0 t1 (lift (S O) O x))))))))) 
(\lambda (H7: (eq T u0 u1)).(eq_ind T u1 (\lambda (t: T).((eq T t0 t1) \to 
((eq T (THead (Bind Abbr) u2 t2) x) \to ((pr0 t u2) \to ((pr0 t0 t2) \to (or 
(ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y: T).(pr0 t1 y)) 
(\lambda (y: T).(subst0 O u3 y t3))))))) (pr0 t1 (lift (S O) O x)))))))) 
(\lambda (H8: (eq T t0 t1)).(eq_ind T t1 (\lambda (t: T).((eq T (THead (Bind 
Abbr) u2 t2) x) \to ((pr0 u1 u2) \to ((pr0 t t2) \to (or (ex3_2 T T (\lambda 
(u3: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: T).(or (pr0 
t1 t3) (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O u3 y 
t3))))))) (pr0 t1 (lift (S O) O x))))))) (\lambda (H9: (eq T (THead (Bind 
Abbr) u2 t2) x)).(eq_ind T (THead (Bind Abbr) u2 t2) (\lambda (t: T).((pr0 u1 
u2) \to ((pr0 t1 t2) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq 
T t (THead (Bind Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 
u3))) (\lambda (u3: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y: 
T).(pr0 t1 y)) (\lambda (y: T).(subst0 O u3 y t3))))))) (pr0 t1 (lift (S O) O 
t)))))) (\lambda (H10: (pr0 u1 u2)).(\lambda (H11: (pr0 t1 t2)).(or_introl 
(ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) u2 t2) 
(THead (Bind Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) 
(\lambda (u3: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y: T).(pr0 
t1 y)) (\lambda (y: T).(subst0 O u3 y t3))))))) (pr0 t1 (lift (S O) O (THead 
(Bind Abbr) u2 t2))) (ex3_2_intro T T (\lambda (u3: T).(\lambda (t3: T).(eq T 
(THead (Bind Abbr) u2 t2) (THead (Bind Abbr) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: T).(or (pr0 
t1 t3) (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O u3 y 
t3)))))) u2 t2 (refl_equal T (THead (Bind Abbr) u2 t2)) H10 (or_introl (pr0 
t1 t2) (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O u2 y 
t2))) H11))))) x H9)) t0 (sym_eq T t0 t1 H8))) u0 (sym_eq T u0 u1 H7))) k 
(sym_eq K k (Bind Abbr) H6))) H5)) H4)) H3 H0 H1))) | (pr0_beta u v1 v2 H0 t0 
t2 H1) \Rightarrow (\lambda (H2: (eq T (THead (Flat Appl) v1 (THead (Bind 
Abst) u t0)) (THead (Bind Abbr) u1 t1))).(\lambda (H3: (eq T (THead (Bind 
Abbr) v2 t2) x)).((let H4 \def (eq_ind T (THead (Flat Appl) v1 (THead (Bind 
Abst) u t0)) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind Abbr) u1 
t1) H2) in (False_ind ((eq T (THead (Bind Abbr) v2 t2) x) \to ((pr0 v1 v2) 
\to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x 
(THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (u2: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y: T).(pr0 
t1 y)) (\lambda (y: T).(subst0 O u2 y t3))))))) (pr0 t1 (lift (S O) O x)))))) 
H4)) H3 H0 H1))) | (pr0_upsilon b H0 v1 v2 H1 u0 u2 H2 t0 t2 H3) \Rightarrow 
(\lambda (H4: (eq T (THead (Flat Appl) v1 (THead (Bind b) u0 t0)) (THead 
(Bind Abbr) u1 t1))).(\lambda (H5: (eq T (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t2)) x)).((let H6 \def (eq_ind T (THead (Flat Appl) 
v1 (THead (Bind b) u0 t0)) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind 
Abbr) u1 t1) H4) in (False_ind ((eq T (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t2)) x) \to ((not (eq B b Abst)) \to ((pr0 v1 v2) \to ((pr0 
u0 u2) \to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 
u1 u3))) (\lambda (u3: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda 
(y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O u3 y t3))))))) (pr0 t1 (lift (S 
O) O x)))))))) H6)) H5 H0 H1 H2 H3))) | (pr0_delta u0 u2 H0 t0 t2 H1 w H2) 
\Rightarrow (\lambda (H3: (eq T (THead (Bind Abbr) u0 t0) (THead (Bind Abbr) 
u1 t1))).(\lambda (H4: (eq T (THead (Bind Abbr) u2 w) x)).((let H5 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t) 
\Rightarrow t])) (THead (Bind Abbr) u0 t0) (THead (Bind Abbr) u1 t1) H3) in 
((let H6 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead _ t 
_) \Rightarrow t])) (THead (Bind Abbr) u0 t0) (THead (Bind Abbr) u1 t1) H3) 
in (eq_ind T u1 (\lambda (t: T).((eq T t0 t1) \to ((eq T (THead (Bind Abbr) 
u2 w) x) \to ((pr0 t u2) \to ((pr0 t0 t2) \to ((subst0 O u2 t2 w) \to (or 
(ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y: T).(pr0 t1 y)) 
(\lambda (y: T).(subst0 O u3 y t3))))))) (pr0 t1 (lift (S O) O x))))))))) 
(\lambda (H7: (eq T t0 t1)).(eq_ind T t1 (\lambda (t: T).((eq T (THead (Bind 
Abbr) u2 w) x) \to ((pr0 u1 u2) \to ((pr0 t t2) \to ((subst0 O u2 t2 w) \to 
(or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) 
u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y: T).(pr0 t1 y)) 
(\lambda (y: T).(subst0 O u3 y t3))))))) (pr0 t1 (lift (S O) O x)))))))) 
(\lambda (H8: (eq T (THead (Bind Abbr) u2 w) x)).(eq_ind T (THead (Bind Abbr) 
u2 w) (\lambda (t: T).((pr0 u1 u2) \to ((pr0 t1 t2) \to ((subst0 O u2 t2 w) 
\to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t (THead (Bind 
Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y: T).(pr0 t1 y)) 
(\lambda (y: T).(subst0 O u3 y t3))))))) (pr0 t1 (lift (S O) O t))))))) 
(\lambda (H9: (pr0 u1 u2)).(\lambda (H10: (pr0 t1 t2)).(\lambda (H11: (subst0 
O u2 t2 w)).(or_introl (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T 
(THead (Bind Abbr) u2 w) (THead (Bind Abbr) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: T).(or (pr0 
t1 t3) (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O u3 y 
t3))))))) (pr0 t1 (lift (S O) O (THead (Bind Abbr) u2 w))) (ex3_2_intro T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) u2 w) (THead (Bind 
Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y: T).(pr0 t1 y)) 
(\lambda (y: T).(subst0 O u3 y t3)))))) u2 w (refl_equal T (THead (Bind Abbr) 
u2 w)) H9 (or_intror (pr0 t1 w) (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda 
(y: T).(subst0 O u2 y w))) (ex_intro2 T (\lambda (y: T).(pr0 t1 y)) (\lambda 
(y: T).(subst0 O u2 y w)) t2 H10 H11))))))) x H8)) t0 (sym_eq T t0 t1 H7))) 
u0 (sym_eq T u0 u1 H6))) H5)) H4 H0 H1 H2))) | (pr0_zeta b H0 t0 t2 H1 u) 
\Rightarrow (\lambda (H2: (eq T (THead (Bind b) u (lift (S O) O t0)) (THead 
(Bind Abbr) u1 t1))).(\lambda (H3: (eq T t2 x)).((let H4 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow ((let rec lref_map (f: ((nat \to nat))) (d: nat) (t: T) on t: T 
\def (match t with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow 
(TLRef (match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) 
| (THead k u0 t3) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t3))]) in lref_map) (\lambda (x0: nat).(plus x0 (S O))) O t0) | (TLRef _) 
\Rightarrow ((let rec lref_map (f: ((nat \to nat))) (d: nat) (t: T) on t: T 
\def (match t with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow 
(TLRef (match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) 
| (THead k u0 t3) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t3))]) in lref_map) (\lambda (x0: nat).(plus x0 (S O))) O t0) | (THead _ _ t) 
\Rightarrow t])) (THead (Bind b) u (lift (S O) O t0)) (THead (Bind Abbr) u1 
t1) H2) in ((let H5 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow u | (TLRef _) \Rightarrow u | 
(THead _ t _) \Rightarrow t])) (THead (Bind b) u (lift (S O) O t0)) (THead 
(Bind Abbr) u1 t1) H2) in ((let H6 \def (f_equal T B (\lambda (e: T).(match e 
in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow b | (TLRef _) 
\Rightarrow b | (THead k _ _) \Rightarrow (match k in K return (\lambda (_: 
K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow b])])) (THead 
(Bind b) u (lift (S O) O t0)) (THead (Bind Abbr) u1 t1) H2) in (eq_ind B Abbr 
(\lambda (b0: B).((eq T u u1) \to ((eq T (lift (S O) O t0) t1) \to ((eq T t2 
x) \to ((not (eq B b0 Abst)) \to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t3: T).(or (pr0 
t1 t3) (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O u2 y 
t3))))))) (pr0 t1 (lift (S O) O x))))))))) (\lambda (H7: (eq T u u1)).(eq_ind 
T u1 (\lambda (_: T).((eq T (lift (S O) O t0) t1) \to ((eq T t2 x) \to ((not 
(eq B Abbr Abst)) \to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t3: T).(or (pr0 
t1 t3) (ex2 T (\lambda (y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O u2 y 
t3))))))) (pr0 t1 (lift (S O) O x)))))))) (\lambda (H8: (eq T (lift (S O) O 
t0) t1)).(eq_ind T (lift (S O) O t0) (\lambda (t: T).((eq T t2 x) \to ((not 
(eq B Abbr Abst)) \to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t3: T).(or (pr0 t 
t3) (ex2 T (\lambda (y: T).(pr0 t y)) (\lambda (y: T).(subst0 O u2 y 
t3))))))) (pr0 t (lift (S O) O x))))))) (\lambda (H9: (eq T t2 x)).(eq_ind T 
x (\lambda (t: T).((not (eq B Abbr Abst)) \to ((pr0 t0 t) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t3: 
T).(or (pr0 (lift (S O) O t0) t3) (ex2 T (\lambda (y: T).(pr0 (lift (S O) O 
t0) y)) (\lambda (y: T).(subst0 O u2 y t3))))))) (pr0 (lift (S O) O t0) (lift 
(S O) O x)))))) (\lambda (_: (not (eq B Abbr Abst))).(\lambda (H11: (pr0 t0 
x)).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(u2: T).(\lambda (t3: T).(or (pr0 (lift (S O) O t0) t3) (ex2 T (\lambda (y: 
T).(pr0 (lift (S O) O t0) y)) (\lambda (y: T).(subst0 O u2 y t3))))))) (pr0 
(lift (S O) O t0) (lift (S O) O x)) (pr0_lift t0 x H11 (S O) O)))) t2 (sym_eq 
T t2 x H9))) t1 H8)) u (sym_eq T u u1 H7))) b (sym_eq B b Abbr H6))) H5)) 
H4)) H3 H0 H1))) | (pr0_epsilon t0 t2 H0 u) \Rightarrow (\lambda (H1: (eq T 
(THead (Flat Cast) u t0) (THead (Bind Abbr) u1 t1))).(\lambda (H2: (eq T t2 
x)).((let H3 \def (eq_ind T (THead (Flat Cast) u t0) (\lambda (e: T).(match e 
in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef 
_) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind Abbr) u1 t1) H1) in (False_ind ((eq T t2 x) \to 
((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x 
(THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (u2: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y: T).(pr0 
t1 y)) (\lambda (y: T).(subst0 O u2 y t3))))))) (pr0 t1 (lift (S O) O x))))) 
H3)) H2 H0)))]) in (H0 (refl_equal T (THead (Bind Abbr) u1 t1)) (refl_equal T 
x)))))).

theorem pr0_gen_void:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Bind Void) u1 
t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O x))))))
\def
 \lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (H: (pr0 (THead 
(Bind Void) u1 t1) x)).(let H0 \def (match H in pr0 return (\lambda (t: 
T).(\lambda (t0: T).(\lambda (_: (pr0 t t0)).((eq T t (THead (Bind Void) u1 
t1)) \to ((eq T t0 x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 
u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) 
O x)))))))) with [(pr0_refl t) \Rightarrow (\lambda (H0: (eq T t (THead (Bind 
Void) u1 t1))).(\lambda (H1: (eq T t x)).(eq_ind T (THead (Bind Void) u1 t1) 
(\lambda (t0: T).((eq T t0 x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 
(lift (S O) O x))))) (\lambda (H2: (eq T (THead (Bind Void) u1 t1) 
x)).(eq_ind T (THead (Bind Void) u1 t1) (\lambda (t0: T).(or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Bind Void) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: 
T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O t0)))) (or_introl (ex3_2 T T (\lambda 
(u2: T).(\lambda (t2: T).(eq T (THead (Bind Void) u1 t1) (THead (Bind Void) 
u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O (THead (Bind Void) 
u1 t1))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t2: T).(eq T (THead 
(Bind Void) u1 t1) (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2))) u1 t1 
(refl_equal T (THead (Bind Void) u1 t1)) (pr0_refl u1) (pr0_refl t1))) x H2)) 
t (sym_eq T t (THead (Bind Void) u1 t1) H0) H1))) | (pr0_comp u0 u2 H0 t0 t2 
H1 k) \Rightarrow (\lambda (H2: (eq T (THead k u0 t0) (THead (Bind Void) u1 
t1))).(\lambda (H3: (eq T (THead k u2 t2) x)).((let H4 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t) \Rightarrow t])) 
(THead k u0 t0) (THead (Bind Void) u1 t1) H2) in ((let H5 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead _ t _) \Rightarrow t])) 
(THead k u0 t0) (THead (Bind Void) u1 t1) H2) in ((let H6 \def (f_equal T K 
(\lambda (e: T).(match e in T return (\lambda (_: T).K) with [(TSort _) 
\Rightarrow k | (TLRef _) \Rightarrow k | (THead k0 _ _) \Rightarrow k0])) 
(THead k u0 t0) (THead (Bind Void) u1 t1) H2) in (eq_ind K (Bind Void) 
(\lambda (k0: K).((eq T u0 u1) \to ((eq T t0 t1) \to ((eq T (THead k0 u2 t2) 
x) \to ((pr0 u0 u2) \to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T x (THead (Bind Void) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 (lift (S O) O x))))))))) (\lambda (H7: (eq T u0 u1)).(eq_ind T 
u1 (\lambda (t: T).((eq T t0 t1) \to ((eq T (THead (Bind Void) u2 t2) x) \to 
((pr0 t u2) \to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda 
(t3: T).(eq T x (THead (Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 
(lift (S O) O x)))))))) (\lambda (H8: (eq T t0 t1)).(eq_ind T t1 (\lambda (t: 
T).((eq T (THead (Bind Void) u2 t2) x) \to ((pr0 u1 u2) \to ((pr0 t t2) \to 
(or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Bind Void) 
u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O x))))))) (\lambda 
(H9: (eq T (THead (Bind Void) u2 t2) x)).(eq_ind T (THead (Bind Void) u2 t2) 
(\lambda (t: T).((pr0 u1 u2) \to ((pr0 t1 t2) \to (or (ex3_2 T T (\lambda 
(u3: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 (lift (S O) O t)))))) (\lambda (H10: (pr0 u1 u2)).(\lambda 
(H11: (pr0 t1 t2)).(or_introl (ex3_2 T T (\lambda (u3: T).(\lambda (t3: 
T).(eq T (THead (Bind Void) u2 t2) (THead (Bind Void) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 (lift (S O) O (THead (Bind Void) u2 t2))) (ex3_2_intro T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind Void) u2 t2) (THead 
(Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3))) u2 t2 (refl_equal T (THead (Bind Void) 
u2 t2)) H10 H11)))) x H9)) t0 (sym_eq T t0 t1 H8))) u0 (sym_eq T u0 u1 H7))) 
k (sym_eq K k (Bind Void) H6))) H5)) H4)) H3 H0 H1))) | (pr0_beta u v1 v2 H0 
t0 t2 H1) \Rightarrow (\lambda (H2: (eq T (THead (Flat Appl) v1 (THead (Bind 
Abst) u t0)) (THead (Bind Void) u1 t1))).(\lambda (H3: (eq T (THead (Bind 
Abbr) v2 t2) x)).((let H4 \def (eq_ind T (THead (Flat Appl) v1 (THead (Bind 
Abst) u t0)) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind Void) u1 
t1) H2) in (False_ind ((eq T (THead (Bind Abbr) v2 t2) x) \to ((pr0 v1 v2) 
\to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T x 
(THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O x)))))) 
H4)) H3 H0 H1))) | (pr0_upsilon b H0 v1 v2 H1 u0 u2 H2 t0 t2 H3) \Rightarrow 
(\lambda (H4: (eq T (THead (Flat Appl) v1 (THead (Bind b) u0 t0)) (THead 
(Bind Void) u1 t1))).(\lambda (H5: (eq T (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t2)) x)).((let H6 \def (eq_ind T (THead (Flat Appl) 
v1 (THead (Bind b) u0 t0)) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind 
Void) u1 t1) H4) in (False_ind ((eq T (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t2)) x) \to ((not (eq B b Abst)) \to ((pr0 v1 v2) \to ((pr0 
u0 u2) \to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: 
T).(eq T x (THead (Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 
u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) 
O x)))))))) H6)) H5 H0 H1 H2 H3))) | (pr0_delta u0 u2 H0 t0 t2 H1 w H2) 
\Rightarrow (\lambda (H3: (eq T (THead (Bind Abbr) u0 t0) (THead (Bind Void) 
u1 t1))).(\lambda (H4: (eq T (THead (Bind Abbr) u2 w) x)).((let H5 \def 
(eq_ind T (THead (Bind Abbr) u0 t0) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b) \Rightarrow (match b in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow True | Abst \Rightarrow False | Void 
\Rightarrow False]) | (Flat _) \Rightarrow False])])) I (THead (Bind Void) u1 
t1) H3) in (False_ind ((eq T (THead (Bind Abbr) u2 w) x) \to ((pr0 u0 u2) \to 
((pr0 t0 t2) \to ((subst0 O u2 t2 w) \to (or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T x (THead (Bind Void) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 (lift (S O) O x))))))) H5)) H4 H0 H1 H2))) | (pr0_zeta b H0 t0 
t2 H1 u) \Rightarrow (\lambda (H2: (eq T (THead (Bind b) u (lift (S O) O t0)) 
(THead (Bind Void) u1 t1))).(\lambda (H3: (eq T t2 x)).((let H4 \def (f_equal 
T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow ((let rec lref_map (f: ((nat \to nat))) (d: nat) (t: T) on t: T 
\def (match t with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow 
(TLRef (match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) 
| (THead k u0 t3) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t3))]) in lref_map) (\lambda (x0: nat).(plus x0 (S O))) O t0) | (TLRef _) 
\Rightarrow ((let rec lref_map (f: ((nat \to nat))) (d: nat) (t: T) on t: T 
\def (match t with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow 
(TLRef (match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) 
| (THead k u0 t3) \Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) 
t3))]) in lref_map) (\lambda (x0: nat).(plus x0 (S O))) O t0) | (THead _ _ t) 
\Rightarrow t])) (THead (Bind b) u (lift (S O) O t0)) (THead (Bind Void) u1 
t1) H2) in ((let H5 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow u | (TLRef _) \Rightarrow u | 
(THead _ t _) \Rightarrow t])) (THead (Bind b) u (lift (S O) O t0)) (THead 
(Bind Void) u1 t1) H2) in ((let H6 \def (f_equal T B (\lambda (e: T).(match e 
in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow b | (TLRef _) 
\Rightarrow b | (THead k _ _) \Rightarrow (match k in K return (\lambda (_: 
K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow b])])) (THead 
(Bind b) u (lift (S O) O t0)) (THead (Bind Void) u1 t1) H2) in (eq_ind B Void 
(\lambda (b0: B).((eq T u u1) \to ((eq T (lift (S O) O t0) t1) \to ((eq T t2 
x) \to ((not (eq B b0 Abst)) \to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 (lift (S O) O x))))))))) (\lambda (H7: (eq T u u1)).(eq_ind T 
u1 (\lambda (_: T).((eq T (lift (S O) O t0) t1) \to ((eq T t2 x) \to ((not 
(eq B Void Abst)) \to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 (lift (S O) O x)))))))) (\lambda (H8: (eq T (lift (S O) O t0) 
t1)).(eq_ind T (lift (S O) O t0) (\lambda (t: T).((eq T t2 x) \to ((not (eq B 
Void Abst)) \to ((pr0 t0 t2) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T x (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t t3)))) (pr0 t (lift 
(S O) O x))))))) (\lambda (H9: (eq T t2 x)).(eq_ind T x (\lambda (t: T).((not 
(eq B Void Abst)) \to ((pr0 t0 t) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 (lift 
(S O) O t0) t3)))) (pr0 (lift (S O) O t0) (lift (S O) O x)))))) (\lambda (_: 
(not (eq B Void Abst))).(\lambda (H11: (pr0 t0 x)).(or_intror (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 (lift (S O) O t0) t3)))) (pr0 (lift (S O) O t0) (lift (S O) O x)) 
(pr0_lift t0 x H11 (S O) O)))) t2 (sym_eq T t2 x H9))) t1 H8)) u (sym_eq T u 
u1 H7))) b (sym_eq B b Void H6))) H5)) H4)) H3 H0 H1))) | (pr0_epsilon t0 t2 
H0 u) \Rightarrow (\lambda (H1: (eq T (THead (Flat Cast) u t0) (THead (Bind 
Void) u1 t1))).(\lambda (H2: (eq T t2 x)).((let H3 \def (eq_ind T (THead 
(Flat Cast) u t0) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ 
_) \Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind Void) u1 
t1) H1) in (False_ind ((eq T t2 x) \to ((pr0 t0 t2) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T x (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O x))))) H3)) H2 H0)))]) in (H0 
(refl_equal T (THead (Bind Void) u1 t1)) (refl_equal T x)))))).

theorem pr0_gen_lift:
 \forall (t1: T).(\forall (x: T).(\forall (h: nat).(\forall (d: nat).((pr0 
(lift h d t1) x) \to (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda 
(t2: T).(pr0 t1 t2)))))))
\def
 \lambda (t1: T).(\lambda (x: T).(\lambda (h: nat).(\lambda (d: nat).(\lambda 
(H: (pr0 (lift h d t1) x)).(insert_eq T (lift h d t1) (\lambda (t: T).(pr0 t 
x)) (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: T).(pr0 t1 
t2))) (\lambda (y: T).(\lambda (H0: (pr0 y x)).(unintro nat d (\lambda (n: 
nat).((eq T y (lift h n t1)) \to (ex2 T (\lambda (t2: T).(eq T x (lift h n 
t2))) (\lambda (t2: T).(pr0 t1 t2))))) (unintro T t1 (\lambda (t: T).(\forall 
(x0: nat).((eq T y (lift h x0 t)) \to (ex2 T (\lambda (t2: T).(eq T x (lift h 
x0 t2))) (\lambda (t2: T).(pr0 t t2)))))) (pr0_ind (\lambda (t: T).(\lambda 
(t0: T).(\forall (x0: T).(\forall (x1: nat).((eq T t (lift h x1 x0)) \to (ex2 
T (\lambda (t2: T).(eq T t0 (lift h x1 t2))) (\lambda (t2: T).(pr0 x0 
t2)))))))) (\lambda (t: T).(\lambda (x0: T).(\lambda (x1: nat).(\lambda (H1: 
(eq T t (lift h x1 x0))).(ex_intro2 T (\lambda (t2: T).(eq T t (lift h x1 
t2))) (\lambda (t2: T).(pr0 x0 t2)) x0 H1 (pr0_refl x0)))))) (\lambda (u1: 
T).(\lambda (u2: T).(\lambda (_: (pr0 u1 u2)).(\lambda (H2: ((\forall (x0: 
T).(\forall (x1: nat).((eq T u1 (lift h x1 x0)) \to (ex2 T (\lambda (t2: 
T).(eq T u2 (lift h x1 t2))) (\lambda (t2: T).(pr0 x0 t2)))))))).(\lambda 
(t2: T).(\lambda (t3: T).(\lambda (_: (pr0 t2 t3)).(\lambda (H4: ((\forall 
(x0: T).(\forall (x1: nat).((eq T t2 (lift h x1 x0)) \to (ex2 T (\lambda (t4: 
T).(eq T t3 (lift h x1 t4))) (\lambda (t4: T).(pr0 x0 t4)))))))).(\lambda (k: 
K).(\lambda (x0: T).(\lambda (x1: nat).(\lambda (H5: (eq T (THead k u1 t2) 
(lift h x1 x0))).(K_ind (\lambda (k0: K).((eq T (THead k0 u1 t2) (lift h x1 
x0)) \to (ex2 T (\lambda (t4: T).(eq T (THead k0 u2 t3) (lift h x1 t4))) 
(\lambda (t4: T).(pr0 x0 t4))))) (\lambda (b: B).(\lambda (H6: (eq T (THead 
(Bind b) u1 t2) (lift h x1 x0))).(ex3_2_ind T T (\lambda (y0: T).(\lambda (z: 
T).(eq T x0 (THead (Bind b) y0 z)))) (\lambda (y0: T).(\lambda (_: T).(eq T 
u1 (lift h x1 y0)))) (\lambda (_: T).(\lambda (z: T).(eq T t2 (lift h (S x1) 
z)))) (ex2 T (\lambda (t4: T).(eq T (THead (Bind b) u2 t3) (lift h x1 t4))) 
(\lambda (t4: T).(pr0 x0 t4))) (\lambda (x2: T).(\lambda (x3: T).(\lambda 
(H7: (eq T x0 (THead (Bind b) x2 x3))).(\lambda (H8: (eq T u1 (lift h x1 
x2))).(\lambda (H9: (eq T t2 (lift h (S x1) x3))).(eq_ind_r T (THead (Bind b) 
x2 x3) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind b) u2 t3) 
(lift h x1 t4))) (\lambda (t4: T).(pr0 t t4)))) (ex2_ind T (\lambda (t4: 
T).(eq T t3 (lift h (S x1) t4))) (\lambda (t4: T).(pr0 x3 t4)) (ex2 T 
(\lambda (t4: T).(eq T (THead (Bind b) u2 t3) (lift h x1 t4))) (\lambda (t4: 
T).(pr0 (THead (Bind b) x2 x3) t4))) (\lambda (x4: T).(\lambda (H_x: (eq T t3 
(lift h (S x1) x4))).(\lambda (H10: (pr0 x3 x4)).(eq_ind_r T (lift h (S x1) 
x4) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind b) u2 t) (lift 
h x1 t4))) (\lambda (t4: T).(pr0 (THead (Bind b) x2 x3) t4)))) (ex2_ind T 
(\lambda (t4: T).(eq T u2 (lift h x1 t4))) (\lambda (t4: T).(pr0 x2 t4)) (ex2 
T (\lambda (t4: T).(eq T (THead (Bind b) u2 (lift h (S x1) x4)) (lift h x1 
t4))) (\lambda (t4: T).(pr0 (THead (Bind b) x2 x3) t4))) (\lambda (x5: 
T).(\lambda (H_x0: (eq T u2 (lift h x1 x5))).(\lambda (H11: (pr0 x2 
x5)).(eq_ind_r T (lift h x1 x5) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T 
(THead (Bind b) t (lift h (S x1) x4)) (lift h x1 t4))) (\lambda (t4: T).(pr0 
(THead (Bind b) x2 x3) t4)))) (ex_intro2 T (\lambda (t4: T).(eq T (THead 
(Bind b) (lift h x1 x5) (lift h (S x1) x4)) (lift h x1 t4))) (\lambda (t4: 
T).(pr0 (THead (Bind b) x2 x3) t4)) (THead (Bind b) x5 x4) (sym_eq T (lift h 
x1 (THead (Bind b) x5 x4)) (THead (Bind b) (lift h x1 x5) (lift h (S x1) x4)) 
(lift_bind b x5 x4 h x1)) (pr0_comp x2 x5 H11 x3 x4 H10 (Bind b))) u2 
H_x0)))) (H2 x2 x1 H8)) t3 H_x)))) (H4 x3 (S x1) H9)) x0 H7)))))) 
(lift_gen_bind b u1 t2 x0 h x1 H6)))) (\lambda (f: F).(\lambda (H6: (eq T 
(THead (Flat f) u1 t2) (lift h x1 x0))).(ex3_2_ind T T (\lambda (y0: 
T).(\lambda (z: T).(eq T x0 (THead (Flat f) y0 z)))) (\lambda (y0: 
T).(\lambda (_: T).(eq T u1 (lift h x1 y0)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t2 (lift h x1 z)))) (ex2 T (\lambda (t4: T).(eq T (THead (Flat f) u2 
t3) (lift h x1 t4))) (\lambda (t4: T).(pr0 x0 t4))) (\lambda (x2: T).(\lambda 
(x3: T).(\lambda (H7: (eq T x0 (THead (Flat f) x2 x3))).(\lambda (H8: (eq T 
u1 (lift h x1 x2))).(\lambda (H9: (eq T t2 (lift h x1 x3))).(eq_ind_r T 
(THead (Flat f) x2 x3) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T (THead 
(Flat f) u2 t3) (lift h x1 t4))) (\lambda (t4: T).(pr0 t t4)))) (ex2_ind T 
(\lambda (t4: T).(eq T t3 (lift h x1 t4))) (\lambda (t4: T).(pr0 x3 t4)) (ex2 
T (\lambda (t4: T).(eq T (THead (Flat f) u2 t3) (lift h x1 t4))) (\lambda 
(t4: T).(pr0 (THead (Flat f) x2 x3) t4))) (\lambda (x4: T).(\lambda (H_x: (eq 
T t3 (lift h x1 x4))).(\lambda (H10: (pr0 x3 x4)).(eq_ind_r T (lift h x1 x4) 
(\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T (THead (Flat f) u2 t) (lift h 
x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat f) x2 x3) t4)))) (ex2_ind T 
(\lambda (t4: T).(eq T u2 (lift h x1 t4))) (\lambda (t4: T).(pr0 x2 t4)) (ex2 
T (\lambda (t4: T).(eq T (THead (Flat f) u2 (lift h x1 x4)) (lift h x1 t4))) 
(\lambda (t4: T).(pr0 (THead (Flat f) x2 x3) t4))) (\lambda (x5: T).(\lambda 
(H_x0: (eq T u2 (lift h x1 x5))).(\lambda (H11: (pr0 x2 x5)).(eq_ind_r T 
(lift h x1 x5) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T (THead (Flat f) 
t (lift h x1 x4)) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat f) x2 
x3) t4)))) (ex_intro2 T (\lambda (t4: T).(eq T (THead (Flat f) (lift h x1 x5) 
(lift h x1 x4)) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat f) x2 x3) 
t4)) (THead (Flat f) x5 x4) (sym_eq T (lift h x1 (THead (Flat f) x5 x4)) 
(THead (Flat f) (lift h x1 x5) (lift h x1 x4)) (lift_flat f x5 x4 h x1)) 
(pr0_comp x2 x5 H11 x3 x4 H10 (Flat f))) u2 H_x0)))) (H2 x2 x1 H8)) t3 
H_x)))) (H4 x3 x1 H9)) x0 H7)))))) (lift_gen_flat f u1 t2 x0 h x1 H6)))) k 
H5))))))))))))) (\lambda (u: T).(\lambda (v1: T).(\lambda (v2: T).(\lambda 
(_: (pr0 v1 v2)).(\lambda (H2: ((\forall (x0: T).(\forall (x1: nat).((eq T v1 
(lift h x1 x0)) \to (ex2 T (\lambda (t2: T).(eq T v2 (lift h x1 t2))) 
(\lambda (t2: T).(pr0 x0 t2)))))))).(\lambda (t2: T).(\lambda (t3: 
T).(\lambda (_: (pr0 t2 t3)).(\lambda (H4: ((\forall (x0: T).(\forall (x1: 
nat).((eq T t2 (lift h x1 x0)) \to (ex2 T (\lambda (t4: T).(eq T t3 (lift h 
x1 t4))) (\lambda (t4: T).(pr0 x0 t4)))))))).(\lambda (x0: T).(\lambda (x1: 
nat).(\lambda (H5: (eq T (THead (Flat Appl) v1 (THead (Bind Abst) u t2)) 
(lift h x1 x0))).(ex3_2_ind T T (\lambda (y0: T).(\lambda (z: T).(eq T x0 
(THead (Flat Appl) y0 z)))) (\lambda (y0: T).(\lambda (_: T).(eq T v1 (lift h 
x1 y0)))) (\lambda (_: T).(\lambda (z: T).(eq T (THead (Bind Abst) u t2) 
(lift h x1 z)))) (ex2 T (\lambda (t4: T).(eq T (THead (Bind Abbr) v2 t3) 
(lift h x1 t4))) (\lambda (t4: T).(pr0 x0 t4))) (\lambda (x2: T).(\lambda 
(x3: T).(\lambda (H6: (eq T x0 (THead (Flat Appl) x2 x3))).(\lambda (H7: (eq 
T v1 (lift h x1 x2))).(\lambda (H8: (eq T (THead (Bind Abst) u t2) (lift h x1 
x3))).(eq_ind_r T (THead (Flat Appl) x2 x3) (\lambda (t: T).(ex2 T (\lambda 
(t4: T).(eq T (THead (Bind Abbr) v2 t3) (lift h x1 t4))) (\lambda (t4: 
T).(pr0 t t4)))) (ex3_2_ind T T (\lambda (y0: T).(\lambda (z: T).(eq T x3 
(THead (Bind Abst) y0 z)))) (\lambda (y0: T).(\lambda (_: T).(eq T u (lift h 
x1 y0)))) (\lambda (_: T).(\lambda (z: T).(eq T t2 (lift h (S x1) z)))) (ex2 
T (\lambda (t4: T).(eq T (THead (Bind Abbr) v2 t3) (lift h x1 t4))) (\lambda 
(t4: T).(pr0 (THead (Flat Appl) x2 x3) t4))) (\lambda (x4: T).(\lambda (x5: 
T).(\lambda (H9: (eq T x3 (THead (Bind Abst) x4 x5))).(\lambda (_: (eq T u 
(lift h x1 x4))).(\lambda (H11: (eq T t2 (lift h (S x1) x5))).(eq_ind_r T 
(THead (Bind Abst) x4 x5) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T 
(THead (Bind Abbr) v2 t3) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat 
Appl) x2 t) t4)))) (ex2_ind T (\lambda (t4: T).(eq T t3 (lift h (S x1) t4))) 
(\lambda (t4: T).(pr0 x5 t4)) (ex2 T (\lambda (t4: T).(eq T (THead (Bind 
Abbr) v2 t3) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat Appl) x2 
(THead (Bind Abst) x4 x5)) t4))) (\lambda (x6: T).(\lambda (H_x: (eq T t3 
(lift h (S x1) x6))).(\lambda (H12: (pr0 x5 x6)).(eq_ind_r T (lift h (S x1) 
x6) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind Abbr) v2 t) 
(lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat Appl) x2 (THead (Bind 
Abst) x4 x5)) t4)))) (ex2_ind T (\lambda (t4: T).(eq T v2 (lift h x1 t4))) 
(\lambda (t4: T).(pr0 x2 t4)) (ex2 T (\lambda (t4: T).(eq T (THead (Bind 
Abbr) v2 (lift h (S x1) x6)) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead 
(Flat Appl) x2 (THead (Bind Abst) x4 x5)) t4))) (\lambda (x7: T).(\lambda 
(H_x0: (eq T v2 (lift h x1 x7))).(\lambda (H13: (pr0 x2 x7)).(eq_ind_r T 
(lift h x1 x7) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind 
Abbr) t (lift h (S x1) x6)) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead 
(Flat Appl) x2 (THead (Bind Abst) x4 x5)) t4)))) (ex_intro2 T (\lambda (t4: 
T).(eq T (THead (Bind Abbr) (lift h x1 x7) (lift h (S x1) x6)) (lift h x1 
t4))) (\lambda (t4: T).(pr0 (THead (Flat Appl) x2 (THead (Bind Abst) x4 x5)) 
t4)) (THead (Bind Abbr) x7 x6) (sym_eq T (lift h x1 (THead (Bind Abbr) x7 
x6)) (THead (Bind Abbr) (lift h x1 x7) (lift h (S x1) x6)) (lift_bind Abbr x7 
x6 h x1)) (pr0_beta x4 x2 x7 H13 x5 x6 H12)) v2 H_x0)))) (H2 x2 x1 H7)) t3 
H_x)))) (H4 x5 (S x1) H11)) x3 H9)))))) (lift_gen_bind Abst u t2 x3 h x1 H8)) 
x0 H6)))))) (lift_gen_flat Appl v1 (THead (Bind Abst) u t2) x0 h x1 
H5)))))))))))))) (\lambda (b: B).(\lambda (H1: (not (eq B b Abst))).(\lambda 
(v1: T).(\lambda (v2: T).(\lambda (_: (pr0 v1 v2)).(\lambda (H3: ((\forall 
(x0: T).(\forall (x1: nat).((eq T v1 (lift h x1 x0)) \to (ex2 T (\lambda (t2: 
T).(eq T v2 (lift h x1 t2))) (\lambda (t2: T).(pr0 x0 t2)))))))).(\lambda 
(u1: T).(\lambda (u2: T).(\lambda (_: (pr0 u1 u2)).(\lambda (H5: ((\forall 
(x0: T).(\forall (x1: nat).((eq T u1 (lift h x1 x0)) \to (ex2 T (\lambda (t2: 
T).(eq T u2 (lift h x1 t2))) (\lambda (t2: T).(pr0 x0 t2)))))))).(\lambda 
(t2: T).(\lambda (t3: T).(\lambda (_: (pr0 t2 t3)).(\lambda (H7: ((\forall 
(x0: T).(\forall (x1: nat).((eq T t2 (lift h x1 x0)) \to (ex2 T (\lambda (t4: 
T).(eq T t3 (lift h x1 t4))) (\lambda (t4: T).(pr0 x0 t4)))))))).(\lambda 
(x0: T).(\lambda (x1: nat).(\lambda (H8: (eq T (THead (Flat Appl) v1 (THead 
(Bind b) u1 t2)) (lift h x1 x0))).(ex3_2_ind T T (\lambda (y0: T).(\lambda 
(z: T).(eq T x0 (THead (Flat Appl) y0 z)))) (\lambda (y0: T).(\lambda (_: 
T).(eq T v1 (lift h x1 y0)))) (\lambda (_: T).(\lambda (z: T).(eq T (THead 
(Bind b) u1 t2) (lift h x1 z)))) (ex2 T (\lambda (t4: T).(eq T (THead (Bind 
b) u2 (THead (Flat Appl) (lift (S O) O v2) t3)) (lift h x1 t4))) (\lambda 
(t4: T).(pr0 x0 t4))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H9: (eq T 
x0 (THead (Flat Appl) x2 x3))).(\lambda (H10: (eq T v1 (lift h x1 
x2))).(\lambda (H11: (eq T (THead (Bind b) u1 t2) (lift h x1 x3))).(eq_ind_r 
T (THead (Flat Appl) x2 x3) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t3)) (lift h x1 t4))) 
(\lambda (t4: T).(pr0 t t4)))) (ex3_2_ind T T (\lambda (y0: T).(\lambda (z: 
T).(eq T x3 (THead (Bind b) y0 z)))) (\lambda (y0: T).(\lambda (_: T).(eq T 
u1 (lift h x1 y0)))) (\lambda (_: T).(\lambda (z: T).(eq T t2 (lift h (S x1) 
z)))) (ex2 T (\lambda (t4: T).(eq T (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t3)) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat 
Appl) x2 x3) t4))) (\lambda (x4: T).(\lambda (x5: T).(\lambda (H12: (eq T x3 
(THead (Bind b) x4 x5))).(\lambda (H13: (eq T u1 (lift h x1 x4))).(\lambda 
(H14: (eq T t2 (lift h (S x1) x5))).(eq_ind_r T (THead (Bind b) x4 x5) 
(\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t3)) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead 
(Flat Appl) x2 t) t4)))) (ex2_ind T (\lambda (t4: T).(eq T t3 (lift h (S x1) 
t4))) (\lambda (t4: T).(pr0 x5 t4)) (ex2 T (\lambda (t4: T).(eq T (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t3)) (lift h x1 t4))) 
(\lambda (t4: T).(pr0 (THead (Flat Appl) x2 (THead (Bind b) x4 x5)) t4))) 
(\lambda (x6: T).(\lambda (H_x: (eq T t3 (lift h (S x1) x6))).(\lambda (H15: 
(pr0 x5 x6)).(eq_ind_r T (lift h (S x1) x6) (\lambda (t: T).(ex2 T (\lambda 
(t4: T).(eq T (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t)) 
(lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat Appl) x2 (THead (Bind b) 
x4 x5)) t4)))) (ex2_ind T (\lambda (t4: T).(eq T u2 (lift h x1 t4))) (\lambda 
(t4: T).(pr0 x4 t4)) (ex2 T (\lambda (t4: T).(eq T (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) (lift h (S x1) x6))) (lift h x1 t4))) (\lambda 
(t4: T).(pr0 (THead (Flat Appl) x2 (THead (Bind b) x4 x5)) t4))) (\lambda 
(x7: T).(\lambda (H_x0: (eq T u2 (lift h x1 x7))).(\lambda (H16: (pr0 x4 
x7)).(eq_ind_r T (lift h x1 x7) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T 
(THead (Bind b) t (THead (Flat Appl) (lift (S O) O v2) (lift h (S x1) x6))) 
(lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat Appl) x2 (THead (Bind b) 
x4 x5)) t4)))) (ex2_ind T (\lambda (t4: T).(eq T v2 (lift h x1 t4))) (\lambda 
(t4: T).(pr0 x2 t4)) (ex2 T (\lambda (t4: T).(eq T (THead (Bind b) (lift h x1 
x7) (THead (Flat Appl) (lift (S O) O v2) (lift h (S x1) x6))) (lift h x1 
t4))) (\lambda (t4: T).(pr0 (THead (Flat Appl) x2 (THead (Bind b) x4 x5)) 
t4))) (\lambda (x8: T).(\lambda (H_x1: (eq T v2 (lift h x1 x8))).(\lambda 
(H17: (pr0 x2 x8)).(eq_ind_r T (lift h x1 x8) (\lambda (t: T).(ex2 T (\lambda 
(t4: T).(eq T (THead (Bind b) (lift h x1 x7) (THead (Flat Appl) (lift (S O) O 
t) (lift h (S x1) x6))) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat 
Appl) x2 (THead (Bind b) x4 x5)) t4)))) (eq_ind T (lift h (plus (S O) x1) 
(lift (S O) O x8)) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind 
b) (lift h x1 x7) (THead (Flat Appl) t (lift h (S x1) x6))) (lift h x1 t4))) 
(\lambda (t4: T).(pr0 (THead (Flat Appl) x2 (THead (Bind b) x4 x5)) t4)))) 
(eq_ind T (lift h (S x1) (THead (Flat Appl) (lift (S O) O x8) x6)) (\lambda 
(t: T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind b) (lift h x1 x7) t) (lift 
h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat Appl) x2 (THead (Bind b) x4 
x5)) t4)))) (ex_intro2 T (\lambda (t4: T).(eq T (THead (Bind b) (lift h x1 
x7) (lift h (S x1) (THead (Flat Appl) (lift (S O) O x8) x6))) (lift h x1 
t4))) (\lambda (t4: T).(pr0 (THead (Flat Appl) x2 (THead (Bind b) x4 x5)) 
t4)) (THead (Bind b) x7 (THead (Flat Appl) (lift (S O) O x8) x6)) (sym_eq T 
(lift h x1 (THead (Bind b) x7 (THead (Flat Appl) (lift (S O) O x8) x6))) 
(THead (Bind b) (lift h x1 x7) (lift h (S x1) (THead (Flat Appl) (lift (S O) 
O x8) x6))) (lift_bind b x7 (THead (Flat Appl) (lift (S O) O x8) x6) h x1)) 
(pr0_upsilon b H1 x2 x8 H17 x4 x7 H16 x5 x6 H15)) (THead (Flat Appl) (lift h 
(S x1) (lift (S O) O x8)) (lift h (S x1) x6)) (lift_flat Appl (lift (S O) O 
x8) x6 h (S x1))) (lift (S O) O (lift h x1 x8)) (lift_d x8 h (S O) x1 O 
(le_O_n x1))) v2 H_x1)))) (H3 x2 x1 H10)) u2 H_x0)))) (H5 x4 x1 H13)) t3 
H_x)))) (H7 x5 (S x1) H14)) x3 H12)))))) (lift_gen_bind b u1 t2 x3 h x1 H11)) 
x0 H9)))))) (lift_gen_flat Appl v1 (THead (Bind b) u1 t2) x0 h x1 
H8))))))))))))))))))) (\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (pr0 u1 
u2)).(\lambda (H2: ((\forall (x0: T).(\forall (x1: nat).((eq T u1 (lift h x1 
x0)) \to (ex2 T (\lambda (t2: T).(eq T u2 (lift h x1 t2))) (\lambda (t2: 
T).(pr0 x0 t2)))))))).(\lambda (t2: T).(\lambda (t3: T).(\lambda (_: (pr0 t2 
t3)).(\lambda (H4: ((\forall (x0: T).(\forall (x1: nat).((eq T t2 (lift h x1 
x0)) \to (ex2 T (\lambda (t4: T).(eq T t3 (lift h x1 t4))) (\lambda (t4: 
T).(pr0 x0 t4)))))))).(\lambda (w: T).(\lambda (H5: (subst0 O u2 t3 
w)).(\lambda (x0: T).(\lambda (x1: nat).(\lambda (H6: (eq T (THead (Bind 
Abbr) u1 t2) (lift h x1 x0))).(ex3_2_ind T T (\lambda (y0: T).(\lambda (z: 
T).(eq T x0 (THead (Bind Abbr) y0 z)))) (\lambda (y0: T).(\lambda (_: T).(eq 
T u1 (lift h x1 y0)))) (\lambda (_: T).(\lambda (z: T).(eq T t2 (lift h (S 
x1) z)))) (ex2 T (\lambda (t4: T).(eq T (THead (Bind Abbr) u2 w) (lift h x1 
t4))) (\lambda (t4: T).(pr0 x0 t4))) (\lambda (x2: T).(\lambda (x3: 
T).(\lambda (H7: (eq T x0 (THead (Bind Abbr) x2 x3))).(\lambda (H8: (eq T u1 
(lift h x1 x2))).(\lambda (H9: (eq T t2 (lift h (S x1) x3))).(eq_ind_r T 
(THead (Bind Abbr) x2 x3) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T 
(THead (Bind Abbr) u2 w) (lift h x1 t4))) (\lambda (t4: T).(pr0 t t4)))) 
(ex2_ind T (\lambda (t4: T).(eq T t3 (lift h (S x1) t4))) (\lambda (t4: 
T).(pr0 x3 t4)) (ex2 T (\lambda (t4: T).(eq T (THead (Bind Abbr) u2 w) (lift 
h x1 t4))) (\lambda (t4: T).(pr0 (THead (Bind Abbr) x2 x3) t4))) (\lambda 
(x4: T).(\lambda (H_x: (eq T t3 (lift h (S x1) x4))).(\lambda (H10: (pr0 x3 
x4)).(let H11 \def (eq_ind T t3 (\lambda (t: T).(subst0 O u2 t w)) H5 (lift h 
(S x1) x4) H_x) in (ex2_ind T (\lambda (t4: T).(eq T u2 (lift h x1 t4))) 
(\lambda (t4: T).(pr0 x2 t4)) (ex2 T (\lambda (t4: T).(eq T (THead (Bind 
Abbr) u2 w) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Bind Abbr) x2 x3) 
t4))) (\lambda (x5: T).(\lambda (H_x0: (eq T u2 (lift h x1 x5))).(\lambda 
(H12: (pr0 x2 x5)).(eq_ind_r T (lift h x1 x5) (\lambda (t: T).(ex2 T (\lambda 
(t4: T).(eq T (THead (Bind Abbr) t w) (lift h x1 t4))) (\lambda (t4: T).(pr0 
(THead (Bind Abbr) x2 x3) t4)))) (let H13 \def (eq_ind T u2 (\lambda (t: 
T).(subst0 O t (lift h (S x1) x4) w)) H11 (lift h x1 x5) H_x0) in (let H14 
\def (refl_equal nat (S (plus O x1))) in (let H15 \def (eq_ind nat (S x1) 
(\lambda (n: nat).(subst0 O (lift h x1 x5) (lift h n x4) w)) H13 (S (plus O 
x1)) H14) in (ex2_ind T (\lambda (t4: T).(eq T w (lift h (S (plus O x1)) 
t4))) (\lambda (t4: T).(subst0 O x5 x4 t4)) (ex2 T (\lambda (t4: T).(eq T 
(THead (Bind Abbr) (lift h x1 x5) w) (lift h x1 t4))) (\lambda (t4: T).(pr0 
(THead (Bind Abbr) x2 x3) t4))) (\lambda (x6: T).(\lambda (H16: (eq T w (lift 
h (S (plus O x1)) x6))).(\lambda (H17: (subst0 O x5 x4 x6)).(eq_ind_r T (lift 
h (S (plus O x1)) x6) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T (THead 
(Bind Abbr) (lift h x1 x5) t) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead 
(Bind Abbr) x2 x3) t4)))) (ex_intro2 T (\lambda (t4: T).(eq T (THead (Bind 
Abbr) (lift h x1 x5) (lift h (S (plus O x1)) x6)) (lift h x1 t4))) (\lambda 
(t4: T).(pr0 (THead (Bind Abbr) x2 x3) t4)) (THead (Bind Abbr) x5 x6) (sym_eq 
T (lift h x1 (THead (Bind Abbr) x5 x6)) (THead (Bind Abbr) (lift h x1 x5) 
(lift h (S (plus O x1)) x6)) (lift_bind Abbr x5 x6 h (plus O x1))) (pr0_delta 
x2 x5 H12 x3 x4 H10 x6 H17)) w H16)))) (subst0_gen_lift_lt x5 x4 w O h x1 
H15))))) u2 H_x0)))) (H2 x2 x1 H8)))))) (H4 x3 (S x1) H9)) x0 H7)))))) 
(lift_gen_bind Abbr u1 t2 x0 h x1 H6))))))))))))))) (\lambda (b: B).(\lambda 
(H1: (not (eq B b Abst))).(\lambda (t2: T).(\lambda (t3: T).(\lambda (_: (pr0 
t2 t3)).(\lambda (H3: ((\forall (x0: T).(\forall (x1: nat).((eq T t2 (lift h 
x1 x0)) \to (ex2 T (\lambda (t4: T).(eq T t3 (lift h x1 t4))) (\lambda (t4: 
T).(pr0 x0 t4)))))))).(\lambda (u: T).(\lambda (x0: T).(\lambda (x1: 
nat).(\lambda (H4: (eq T (THead (Bind b) u (lift (S O) O t2)) (lift h x1 
x0))).(ex3_2_ind T T (\lambda (y0: T).(\lambda (z: T).(eq T x0 (THead (Bind 
b) y0 z)))) (\lambda (y0: T).(\lambda (_: T).(eq T u (lift h x1 y0)))) 
(\lambda (_: T).(\lambda (z: T).(eq T (lift (S O) O t2) (lift h (S x1) z)))) 
(ex2 T (\lambda (t4: T).(eq T t3 (lift h x1 t4))) (\lambda (t4: T).(pr0 x0 
t4))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H5: (eq T x0 (THead (Bind 
b) x2 x3))).(\lambda (_: (eq T u (lift h x1 x2))).(\lambda (H7: (eq T (lift 
(S O) O t2) (lift h (S x1) x3))).(eq_ind_r T (THead (Bind b) x2 x3) (\lambda 
(t: T).(ex2 T (\lambda (t4: T).(eq T t3 (lift h x1 t4))) (\lambda (t4: 
T).(pr0 t t4)))) (let H8 \def (eq_ind_r nat (plus (S O) x1) (\lambda (n: 
nat).(eq nat (S x1) n)) (refl_equal nat (plus (S O) x1)) (plus x1 (S O)) 
(plus_comm x1 (S O))) in (let H9 \def (eq_ind nat (S x1) (\lambda (n: 
nat).(eq T (lift (S O) O t2) (lift h n x3))) H7 (plus x1 (S O)) H8) in 
(ex2_ind T (\lambda (t4: T).(eq T x3 (lift (S O) O t4))) (\lambda (t4: T).(eq 
T t2 (lift h x1 t4))) (ex2 T (\lambda (t4: T).(eq T t3 (lift h x1 t4))) 
(\lambda (t4: T).(pr0 (THead (Bind b) x2 x3) t4))) (\lambda (x4: T).(\lambda 
(H10: (eq T x3 (lift (S O) O x4))).(\lambda (H11: (eq T t2 (lift h x1 
x4))).(eq_ind_r T (lift (S O) O x4) (\lambda (t: T).(ex2 T (\lambda (t4: 
T).(eq T t3 (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Bind b) x2 t) 
t4)))) (ex2_ind T (\lambda (t4: T).(eq T t3 (lift h x1 t4))) (\lambda (t4: 
T).(pr0 x4 t4)) (ex2 T (\lambda (t4: T).(eq T t3 (lift h x1 t4))) (\lambda 
(t4: T).(pr0 (THead (Bind b) x2 (lift (S O) O x4)) t4))) (\lambda (x5: 
T).(\lambda (H_x: (eq T t3 (lift h x1 x5))).(\lambda (H12: (pr0 x4 
x5)).(eq_ind_r T (lift h x1 x5) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T 
t (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Bind b) x2 (lift (S O) O 
x4)) t4)))) (ex_intro2 T (\lambda (t4: T).(eq T (lift h x1 x5) (lift h x1 
t4))) (\lambda (t4: T).(pr0 (THead (Bind b) x2 (lift (S O) O x4)) t4)) x5 
(refl_equal T (lift h x1 x5)) (pr0_zeta b H1 x4 x5 H12 x2)) t3 H_x)))) (H3 x4 
x1 H11)) x3 H10)))) (lift_gen_lift t2 x3 (S O) h O x1 (le_O_n x1) H9)))) x0 
H5)))))) (lift_gen_bind b u (lift (S O) O t2) x0 h x1 H4)))))))))))) (\lambda 
(t2: T).(\lambda (t3: T).(\lambda (_: (pr0 t2 t3)).(\lambda (H2: ((\forall 
(x0: T).(\forall (x1: nat).((eq T t2 (lift h x1 x0)) \to (ex2 T (\lambda (t4: 
T).(eq T t3 (lift h x1 t4))) (\lambda (t4: T).(pr0 x0 t4)))))))).(\lambda (u: 
T).(\lambda (x0: T).(\lambda (x1: nat).(\lambda (H3: (eq T (THead (Flat Cast) 
u t2) (lift h x1 x0))).(ex3_2_ind T T (\lambda (y0: T).(\lambda (z: T).(eq T 
x0 (THead (Flat Cast) y0 z)))) (\lambda (y0: T).(\lambda (_: T).(eq T u (lift 
h x1 y0)))) (\lambda (_: T).(\lambda (z: T).(eq T t2 (lift h x1 z)))) (ex2 T 
(\lambda (t4: T).(eq T t3 (lift h x1 t4))) (\lambda (t4: T).(pr0 x0 t4))) 
(\lambda (x2: T).(\lambda (x3: T).(\lambda (H4: (eq T x0 (THead (Flat Cast) 
x2 x3))).(\lambda (_: (eq T u (lift h x1 x2))).(\lambda (H6: (eq T t2 (lift h 
x1 x3))).(eq_ind_r T (THead (Flat Cast) x2 x3) (\lambda (t: T).(ex2 T 
(\lambda (t4: T).(eq T t3 (lift h x1 t4))) (\lambda (t4: T).(pr0 t t4)))) 
(ex2_ind T (\lambda (t4: T).(eq T t3 (lift h x1 t4))) (\lambda (t4: T).(pr0 
x3 t4)) (ex2 T (\lambda (t4: T).(eq T t3 (lift h x1 t4))) (\lambda (t4: 
T).(pr0 (THead (Flat Cast) x2 x3) t4))) (\lambda (x4: T).(\lambda (H_x: (eq T 
t3 (lift h x1 x4))).(\lambda (H7: (pr0 x3 x4)).(eq_ind_r T (lift h x1 x4) 
(\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T t (lift h x1 t4))) (\lambda 
(t4: T).(pr0 (THead (Flat Cast) x2 x3) t4)))) (ex_intro2 T (\lambda (t4: 
T).(eq T (lift h x1 x4) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat 
Cast) x2 x3) t4)) x4 (refl_equal T (lift h x1 x4)) (pr0_epsilon x3 x4 H7 x2)) 
t3 H_x)))) (H2 x3 x1 H6)) x0 H4)))))) (lift_gen_flat Cast u t2 x0 h x1 
H3)))))))))) y x H0))))) H))))).

