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

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/clear/fwd".

include "clear/defs.ma".

theorem clear_gen_sort:
 \forall (x: C).(\forall (n: nat).((clear (CSort n) x) \to (\forall (P: 
Prop).P)))
\def
 \lambda (x: C).(\lambda (n: nat).(\lambda (H: (clear (CSort n) x)).(\lambda 
(P: Prop).(let H0 \def (match H in clear return (\lambda (c: C).(\lambda (c0: 
C).(\lambda (_: (clear c c0)).((eq C c (CSort n)) \to ((eq C c0 x) \to P))))) 
with [(clear_bind b e u) \Rightarrow (\lambda (H0: (eq C (CHead e (Bind b) u) 
(CSort n))).(\lambda (H1: (eq C (CHead e (Bind b) u) x)).((let H2 \def 
(eq_ind C (CHead e (Bind b) u) (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ _ _) 
\Rightarrow True])) I (CSort n) H0) in (False_ind ((eq C (CHead e (Bind b) u) 
x) \to P) H2)) H1))) | (clear_flat e c H0 f u) \Rightarrow (\lambda (H1: (eq 
C (CHead e (Flat f) u) (CSort n))).(\lambda (H2: (eq C c x)).((let H3 \def 
(eq_ind C (CHead e (Flat f) u) (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ _ _) 
\Rightarrow True])) I (CSort n) H1) in (False_ind ((eq C c x) \to ((clear e 
c) \to P)) H3)) H2 H0)))]) in (H0 (refl_equal C (CSort n)) (refl_equal C 
x)))))).

theorem clear_gen_bind:
 \forall (b: B).(\forall (e: C).(\forall (x: C).(\forall (u: T).((clear 
(CHead e (Bind b) u) x) \to (eq C x (CHead e (Bind b) u))))))
\def
 \lambda (b: B).(\lambda (e: C).(\lambda (x: C).(\lambda (u: T).(\lambda (H: 
(clear (CHead e (Bind b) u) x)).(let H0 \def (match H in clear return 
(\lambda (c: C).(\lambda (c0: C).(\lambda (_: (clear c c0)).((eq C c (CHead e 
(Bind b) u)) \to ((eq C c0 x) \to (eq C x (CHead e (Bind b) u))))))) with 
[(clear_bind b0 e0 u0) \Rightarrow (\lambda (H0: (eq C (CHead e0 (Bind b0) 
u0) (CHead e (Bind b) u))).(\lambda (H1: (eq C (CHead e0 (Bind b0) u0) 
x)).((let H2 \def (f_equal C T (\lambda (e1: C).(match e1 in C return 
(\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | (CHead _ _ t) \Rightarrow 
t])) (CHead e0 (Bind b0) u0) (CHead e (Bind b) u) H0) in ((let H3 \def 
(f_equal C B (\lambda (e1: C).(match e1 in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow b0 | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow 
b0])])) (CHead e0 (Bind b0) u0) (CHead e (Bind b) u) H0) in ((let H4 \def 
(f_equal C C (\lambda (e1: C).(match e1 in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow e0 | (CHead c _ _) \Rightarrow c])) (CHead e0 (Bind 
b0) u0) (CHead e (Bind b) u) H0) in (eq_ind C e (\lambda (c: C).((eq B b0 b) 
\to ((eq T u0 u) \to ((eq C (CHead c (Bind b0) u0) x) \to (eq C x (CHead e 
(Bind b) u)))))) (\lambda (H5: (eq B b0 b)).(eq_ind B b (\lambda (b1: B).((eq 
T u0 u) \to ((eq C (CHead e (Bind b1) u0) x) \to (eq C x (CHead e (Bind b) 
u))))) (\lambda (H6: (eq T u0 u)).(eq_ind T u (\lambda (t: T).((eq C (CHead e 
(Bind b) t) x) \to (eq C x (CHead e (Bind b) u)))) (\lambda (H7: (eq C (CHead 
e (Bind b) u) x)).(eq_ind C (CHead e (Bind b) u) (\lambda (c: C).(eq C c 
(CHead e (Bind b) u))) (refl_equal C (CHead e (Bind b) u)) x H7)) u0 (sym_eq 
T u0 u H6))) b0 (sym_eq B b0 b H5))) e0 (sym_eq C e0 e H4))) H3)) H2)) H1))) 
| (clear_flat e0 c H0 f u0) \Rightarrow (\lambda (H1: (eq C (CHead e0 (Flat 
f) u0) (CHead e (Bind b) u))).(\lambda (H2: (eq C c x)).((let H3 \def (eq_ind 
C (CHead e0 (Flat f) u0) (\lambda (e1: C).(match e1 in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match 
k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat 
_) \Rightarrow True])])) I (CHead e (Bind b) u) H1) in (False_ind ((eq C c x) 
\to ((clear e0 c) \to (eq C x (CHead e (Bind b) u)))) H3)) H2 H0)))]) in (H0 
(refl_equal C (CHead e (Bind b) u)) (refl_equal C x))))))).

theorem clear_gen_flat:
 \forall (f: F).(\forall (e: C).(\forall (x: C).(\forall (u: T).((clear 
(CHead e (Flat f) u) x) \to (clear e x)))))
\def
 \lambda (f: F).(\lambda (e: C).(\lambda (x: C).(\lambda (u: T).(\lambda (H: 
(clear (CHead e (Flat f) u) x)).(let H0 \def (match H in clear return 
(\lambda (c: C).(\lambda (c0: C).(\lambda (_: (clear c c0)).((eq C c (CHead e 
(Flat f) u)) \to ((eq C c0 x) \to (clear e x)))))) with [(clear_bind b e0 u0) 
\Rightarrow (\lambda (H0: (eq C (CHead e0 (Bind b) u0) (CHead e (Flat f) 
u))).(\lambda (H1: (eq C (CHead e0 (Bind b) u0) x)).((let H2 \def (eq_ind C 
(CHead e0 (Bind b) u0) (\lambda (e1: C).(match e1 in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match 
k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | (Flat 
_) \Rightarrow False])])) I (CHead e (Flat f) u) H0) in (False_ind ((eq C 
(CHead e0 (Bind b) u0) x) \to (clear e x)) H2)) H1))) | (clear_flat e0 c H0 
f0 u0) \Rightarrow (\lambda (H1: (eq C (CHead e0 (Flat f0) u0) (CHead e (Flat 
f) u))).(\lambda (H2: (eq C c x)).((let H3 \def (f_equal C T (\lambda (e1: 
C).(match e1 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | 
(CHead _ _ t) \Rightarrow t])) (CHead e0 (Flat f0) u0) (CHead e (Flat f) u) 
H1) in ((let H4 \def (f_equal C F (\lambda (e1: C).(match e1 in C return 
(\lambda (_: C).F) with [(CSort _) \Rightarrow f0 | (CHead _ k _) \Rightarrow 
(match k in K return (\lambda (_: K).F) with [(Bind _) \Rightarrow f0 | (Flat 
f1) \Rightarrow f1])])) (CHead e0 (Flat f0) u0) (CHead e (Flat f) u) H1) in 
((let H5 \def (f_equal C C (\lambda (e1: C).(match e1 in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow e0 | (CHead c0 _ _) \Rightarrow c0])) 
(CHead e0 (Flat f0) u0) (CHead e (Flat f) u) H1) in (eq_ind C e (\lambda (c0: 
C).((eq F f0 f) \to ((eq T u0 u) \to ((eq C c x) \to ((clear c0 c) \to (clear 
e x)))))) (\lambda (H6: (eq F f0 f)).(eq_ind F f (\lambda (_: F).((eq T u0 u) 
\to ((eq C c x) \to ((clear e c) \to (clear e x))))) (\lambda (H7: (eq T u0 
u)).(eq_ind T u (\lambda (_: T).((eq C c x) \to ((clear e c) \to (clear e 
x)))) (\lambda (H8: (eq C c x)).(eq_ind C x (\lambda (c0: C).((clear e c0) 
\to (clear e x))) (\lambda (H9: (clear e x)).H9) c (sym_eq C c x H8))) u0 
(sym_eq T u0 u H7))) f0 (sym_eq F f0 f H6))) e0 (sym_eq C e0 e H5))) H4)) 
H3)) H2 H0)))]) in (H0 (refl_equal C (CHead e (Flat f) u)) (refl_equal C 
x))))))).

theorem clear_gen_flat_r:
 \forall (f: F).(\forall (x: C).(\forall (e: C).(\forall (u: T).((clear x 
(CHead e (Flat f) u)) \to (\forall (P: Prop).P)))))
\def
 \lambda (f: F).(\lambda (x: C).(\lambda (e: C).(\lambda (u: T).(\lambda (H: 
(clear x (CHead e (Flat f) u))).(\lambda (P: Prop).(insert_eq C (CHead e 
(Flat f) u) (\lambda (c: C).(clear x c)) P (\lambda (y: C).(\lambda (H0: 
(clear x y)).(clear_ind (\lambda (_: C).(\lambda (c0: C).((eq C c0 (CHead e 
(Flat f) u)) \to P))) (\lambda (b: B).(\lambda (e0: C).(\lambda (u0: 
T).(\lambda (H1: (eq C (CHead e0 (Bind b) u0) (CHead e (Flat f) u))).(let H2 
\def (eq_ind C (CHead e0 (Bind b) u0) (\lambda (ee: C).(match ee in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow True | (Flat _) \Rightarrow False])])) I (CHead e (Flat f) u) H1) 
in (False_ind P H2)))))) (\lambda (e0: C).(\lambda (c: C).(\lambda (H1: 
(clear e0 c)).(\lambda (H2: (((eq C c (CHead e (Flat f) u)) \to P))).(\lambda 
(_: F).(\lambda (_: T).(\lambda (H3: (eq C c (CHead e (Flat f) u))).(let H4 
\def (eq_ind C c (\lambda (c0: C).((eq C c0 (CHead e (Flat f) u)) \to P)) H2 
(CHead e (Flat f) u) H3) in (let H5 \def (eq_ind C c (\lambda (c0: C).(clear 
e0 c0)) H1 (CHead e (Flat f) u) H3) in (H4 (refl_equal C (CHead e (Flat f) 
u)))))))))))) x y H0))) H)))))).

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

