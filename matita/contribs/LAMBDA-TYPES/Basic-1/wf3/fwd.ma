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

include "Basic-1/wf3/defs.ma".

theorem wf3_gen_sort1:
 \forall (g: G).(\forall (x: C).(\forall (m: nat).((wf3 g (CSort m) x) \to 
(eq C x (CSort m)))))
\def
 \lambda (g: G).(\lambda (x: C).(\lambda (m: nat).(\lambda (H: (wf3 g (CSort 
m) x)).(insert_eq C (CSort m) (\lambda (c: C).(wf3 g c x)) (\lambda (c: 
C).(eq C x c)) (\lambda (y: C).(\lambda (H0: (wf3 g y x)).(wf3_ind g (\lambda 
(c: C).(\lambda (c0: C).((eq C c (CSort m)) \to (eq C c0 c)))) (\lambda (m0: 
nat).(\lambda (H1: (eq C (CSort m0) (CSort m))).(let H2 \def (f_equal C nat 
(\lambda (e: C).(match e in C return (\lambda (_: C).nat) with [(CSort n) 
\Rightarrow n | (CHead _ _ _) \Rightarrow m0])) (CSort m0) (CSort m) H1) in 
(eq_ind_r nat m (\lambda (n: nat).(eq C (CSort n) (CSort n))) (refl_equal C 
(CSort m)) m0 H2)))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (_: (wf3 g c1 
c2)).(\lambda (_: (((eq C c1 (CSort m)) \to (eq C c2 c1)))).(\lambda (u: 
T).(\lambda (t: T).(\lambda (_: (ty3 g c1 u t)).(\lambda (b: B).(\lambda (H4: 
(eq C (CHead c1 (Bind b) u) (CSort m))).(let H5 \def (eq_ind C (CHead c1 
(Bind b) u) (\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with 
[(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow True])) I (CSort m) 
H4) in (False_ind (eq C (CHead c2 (Bind b) u) (CHead c1 (Bind b) u)) 
H5))))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (_: (wf3 g c1 
c2)).(\lambda (_: (((eq C c1 (CSort m)) \to (eq C c2 c1)))).(\lambda (u: 
T).(\lambda (_: ((\forall (t: T).((ty3 g c1 u t) \to False)))).(\lambda (b: 
B).(\lambda (H4: (eq C (CHead c1 (Bind b) u) (CSort m))).(let H5 \def (eq_ind 
C (CHead c1 (Bind b) u) (\lambda (ee: C).(match ee in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow 
True])) I (CSort m) H4) in (False_ind (eq C (CHead c2 (Bind Void) (TSort O)) 
(CHead c1 (Bind b) u)) H5)))))))))) (\lambda (c1: C).(\lambda (c2: 
C).(\lambda (_: (wf3 g c1 c2)).(\lambda (_: (((eq C c1 (CSort m)) \to (eq C 
c2 c1)))).(\lambda (u: T).(\lambda (f: F).(\lambda (H3: (eq C (CHead c1 (Flat 
f) u) (CSort m))).(let H4 \def (eq_ind C (CHead c1 (Flat f) u) (\lambda (ee: 
C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow 
False | (CHead _ _ _) \Rightarrow True])) I (CSort m) H3) in (False_ind (eq C 
c2 (CHead c1 (Flat f) u)) H4))))))))) y x H0))) H)))).
(* COMMENTS
Initial nodes: 523
END *)

theorem wf3_gen_bind1:
 \forall (g: G).(\forall (c1: C).(\forall (x: C).(\forall (v: T).(\forall (b: 
B).((wf3 g (CHead c1 (Bind b) v) x) \to (or (ex3_2 C T (\lambda (c2: 
C).(\lambda (_: T).(eq C x (CHead c2 (Bind b) v)))) (\lambda (c2: C).(\lambda 
(_: T).(wf3 g c1 c2))) (\lambda (_: C).(\lambda (w: T).(ty3 g c1 v w)))) (ex3 
C (\lambda (c2: C).(eq C x (CHead c2 (Bind Void) (TSort O)))) (\lambda (c2: 
C).(wf3 g c1 c2)) (\lambda (_: C).(\forall (w: T).((ty3 g c1 v w) \to 
False))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (x: C).(\lambda (v: T).(\lambda (b: 
B).(\lambda (H: (wf3 g (CHead c1 (Bind b) v) x)).(insert_eq C (CHead c1 (Bind 
b) v) (\lambda (c: C).(wf3 g c x)) (\lambda (_: C).(or (ex3_2 C T (\lambda 
(c2: C).(\lambda (_: T).(eq C x (CHead c2 (Bind b) v)))) (\lambda (c2: 
C).(\lambda (_: T).(wf3 g c1 c2))) (\lambda (_: C).(\lambda (w: T).(ty3 g c1 
v w)))) (ex3 C (\lambda (c2: C).(eq C x (CHead c2 (Bind Void) (TSort O)))) 
(\lambda (c2: C).(wf3 g c1 c2)) (\lambda (_: C).(\forall (w: T).((ty3 g c1 v 
w) \to False)))))) (\lambda (y: C).(\lambda (H0: (wf3 g y x)).(wf3_ind g 
(\lambda (c: C).(\lambda (c0: C).((eq C c (CHead c1 (Bind b) v)) \to (or 
(ex3_2 C T (\lambda (c2: C).(\lambda (_: T).(eq C c0 (CHead c2 (Bind b) v)))) 
(\lambda (c2: C).(\lambda (_: T).(wf3 g c1 c2))) (\lambda (_: C).(\lambda (w: 
T).(ty3 g c1 v w)))) (ex3 C (\lambda (c2: C).(eq C c0 (CHead c2 (Bind Void) 
(TSort O)))) (\lambda (c2: C).(wf3 g c1 c2)) (\lambda (_: C).(\forall (w: 
T).((ty3 g c1 v w) \to False)))))))) (\lambda (m: nat).(\lambda (H1: (eq C 
(CSort m) (CHead c1 (Bind b) v))).(let H2 \def (eq_ind C (CSort m) (\lambda 
(ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow True | (CHead _ _ _) \Rightarrow False])) I (CHead c1 (Bind b) v) 
H1) in (False_ind (or (ex3_2 C T (\lambda (c2: C).(\lambda (_: T).(eq C 
(CSort m) (CHead c2 (Bind b) v)))) (\lambda (c2: C).(\lambda (_: T).(wf3 g c1 
c2))) (\lambda (_: C).(\lambda (w: T).(ty3 g c1 v w)))) (ex3 C (\lambda (c2: 
C).(eq C (CSort m) (CHead c2 (Bind Void) (TSort O)))) (\lambda (c2: C).(wf3 g 
c1 c2)) (\lambda (_: C).(\forall (w: T).((ty3 g c1 v w) \to False))))) H2)))) 
(\lambda (c0: C).(\lambda (c2: C).(\lambda (H1: (wf3 g c0 c2)).(\lambda (H2: 
(((eq C c0 (CHead c1 (Bind b) v)) \to (or (ex3_2 C T (\lambda (c3: 
C).(\lambda (_: T).(eq C c2 (CHead c3 (Bind b) v)))) (\lambda (c3: 
C).(\lambda (_: T).(wf3 g c1 c3))) (\lambda (_: C).(\lambda (w: T).(ty3 g c1 
v w)))) (ex3 C (\lambda (c3: C).(eq C c2 (CHead c3 (Bind Void) (TSort O)))) 
(\lambda (c3: C).(wf3 g c1 c3)) (\lambda (_: C).(\forall (w: T).((ty3 g c1 v 
w) \to False)))))))).(\lambda (u: T).(\lambda (t: T).(\lambda (H3: (ty3 g c0 
u t)).(\lambda (b0: B).(\lambda (H4: (eq C (CHead c0 (Bind b0) u) (CHead c1 
(Bind b) v))).(let H5 \def (f_equal C C (\lambda (e: C).(match e in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow 
c])) (CHead c0 (Bind b0) u) (CHead c1 (Bind b) v) H4) in ((let H6 \def 
(f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow b0 | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow 
b0])])) (CHead c0 (Bind b0) u) (CHead c1 (Bind b) v) H4) in ((let H7 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) (CHead c0 (Bind 
b0) u) (CHead c1 (Bind b) v) H4) in (\lambda (H8: (eq B b0 b)).(\lambda (H9: 
(eq C c0 c1)).(eq_ind_r B b (\lambda (b1: B).(or (ex3_2 C T (\lambda (c3: 
C).(\lambda (_: T).(eq C (CHead c2 (Bind b1) u) (CHead c3 (Bind b) v)))) 
(\lambda (c3: C).(\lambda (_: T).(wf3 g c1 c3))) (\lambda (_: C).(\lambda (w: 
T).(ty3 g c1 v w)))) (ex3 C (\lambda (c3: C).(eq C (CHead c2 (Bind b1) u) 
(CHead c3 (Bind Void) (TSort O)))) (\lambda (c3: C).(wf3 g c1 c3)) (\lambda 
(_: C).(\forall (w: T).((ty3 g c1 v w) \to False)))))) (let H10 \def (eq_ind 
T u (\lambda (t0: T).(ty3 g c0 t0 t)) H3 v H7) in (eq_ind_r T v (\lambda (t0: 
T).(or (ex3_2 C T (\lambda (c3: C).(\lambda (_: T).(eq C (CHead c2 (Bind b) 
t0) (CHead c3 (Bind b) v)))) (\lambda (c3: C).(\lambda (_: T).(wf3 g c1 c3))) 
(\lambda (_: C).(\lambda (w: T).(ty3 g c1 v w)))) (ex3 C (\lambda (c3: C).(eq 
C (CHead c2 (Bind b) t0) (CHead c3 (Bind Void) (TSort O)))) (\lambda (c3: 
C).(wf3 g c1 c3)) (\lambda (_: C).(\forall (w: T).((ty3 g c1 v w) \to 
False)))))) (let H11 \def (eq_ind C c0 (\lambda (c: C).(ty3 g c v t)) H10 c1 
H9) in (let H12 \def (eq_ind C c0 (\lambda (c: C).((eq C c (CHead c1 (Bind b) 
v)) \to (or (ex3_2 C T (\lambda (c3: C).(\lambda (_: T).(eq C c2 (CHead c3 
(Bind b) v)))) (\lambda (c3: C).(\lambda (_: T).(wf3 g c1 c3))) (\lambda (_: 
C).(\lambda (w: T).(ty3 g c1 v w)))) (ex3 C (\lambda (c3: C).(eq C c2 (CHead 
c3 (Bind Void) (TSort O)))) (\lambda (c3: C).(wf3 g c1 c3)) (\lambda (_: 
C).(\forall (w: T).((ty3 g c1 v w) \to False))))))) H2 c1 H9) in (let H13 
\def (eq_ind C c0 (\lambda (c: C).(wf3 g c c2)) H1 c1 H9) in (or_introl 
(ex3_2 C T (\lambda (c3: C).(\lambda (_: T).(eq C (CHead c2 (Bind b) v) 
(CHead c3 (Bind b) v)))) (\lambda (c3: C).(\lambda (_: T).(wf3 g c1 c3))) 
(\lambda (_: C).(\lambda (w: T).(ty3 g c1 v w)))) (ex3 C (\lambda (c3: C).(eq 
C (CHead c2 (Bind b) v) (CHead c3 (Bind Void) (TSort O)))) (\lambda (c3: 
C).(wf3 g c1 c3)) (\lambda (_: C).(\forall (w: T).((ty3 g c1 v w) \to 
False)))) (ex3_2_intro C T (\lambda (c3: C).(\lambda (_: T).(eq C (CHead c2 
(Bind b) v) (CHead c3 (Bind b) v)))) (\lambda (c3: C).(\lambda (_: T).(wf3 g 
c1 c3))) (\lambda (_: C).(\lambda (w: T).(ty3 g c1 v w))) c2 t (refl_equal C 
(CHead c2 (Bind b) v)) H13 H11))))) u H7)) b0 H8)))) H6)) H5))))))))))) 
(\lambda (c0: C).(\lambda (c2: C).(\lambda (H1: (wf3 g c0 c2)).(\lambda (H2: 
(((eq C c0 (CHead c1 (Bind b) v)) \to (or (ex3_2 C T (\lambda (c3: 
C).(\lambda (_: T).(eq C c2 (CHead c3 (Bind b) v)))) (\lambda (c3: 
C).(\lambda (_: T).(wf3 g c1 c3))) (\lambda (_: C).(\lambda (w: T).(ty3 g c1 
v w)))) (ex3 C (\lambda (c3: C).(eq C c2 (CHead c3 (Bind Void) (TSort O)))) 
(\lambda (c3: C).(wf3 g c1 c3)) (\lambda (_: C).(\forall (w: T).((ty3 g c1 v 
w) \to False)))))))).(\lambda (u: T).(\lambda (H3: ((\forall (t: T).((ty3 g 
c0 u t) \to False)))).(\lambda (b0: B).(\lambda (H4: (eq C (CHead c0 (Bind 
b0) u) (CHead c1 (Bind b) v))).(let H5 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | 
(CHead c _ _) \Rightarrow c])) (CHead c0 (Bind b0) u) (CHead c1 (Bind b) v) 
H4) in ((let H6 \def (f_equal C B (\lambda (e: C).(match e in C return 
(\lambda (_: C).B) with [(CSort _) \Rightarrow b0 | (CHead _ k _) \Rightarrow 
(match k in K return (\lambda (_: K).B) with [(Bind b1) \Rightarrow b1 | 
(Flat _) \Rightarrow b0])])) (CHead c0 (Bind b0) u) (CHead c1 (Bind b) v) H4) 
in ((let H7 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda 
(_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) 
(CHead c0 (Bind b0) u) (CHead c1 (Bind b) v) H4) in (\lambda (_: (eq B b0 
b)).(\lambda (H9: (eq C c0 c1)).(let H10 \def (eq_ind T u (\lambda (t: 
T).(\forall (t0: T).((ty3 g c0 t t0) \to False))) H3 v H7) in (let H11 \def 
(eq_ind C c0 (\lambda (c: C).(\forall (t: T).((ty3 g c v t) \to False))) H10 
c1 H9) in (let H12 \def (eq_ind C c0 (\lambda (c: C).((eq C c (CHead c1 (Bind 
b) v)) \to (or (ex3_2 C T (\lambda (c3: C).(\lambda (_: T).(eq C c2 (CHead c3 
(Bind b) v)))) (\lambda (c3: C).(\lambda (_: T).(wf3 g c1 c3))) (\lambda (_: 
C).(\lambda (w: T).(ty3 g c1 v w)))) (ex3 C (\lambda (c3: C).(eq C c2 (CHead 
c3 (Bind Void) (TSort O)))) (\lambda (c3: C).(wf3 g c1 c3)) (\lambda (_: 
C).(\forall (w: T).((ty3 g c1 v w) \to False))))))) H2 c1 H9) in (let H13 
\def (eq_ind C c0 (\lambda (c: C).(wf3 g c c2)) H1 c1 H9) in (or_intror 
(ex3_2 C T (\lambda (c3: C).(\lambda (_: T).(eq C (CHead c2 (Bind Void) 
(TSort O)) (CHead c3 (Bind b) v)))) (\lambda (c3: C).(\lambda (_: T).(wf3 g 
c1 c3))) (\lambda (_: C).(\lambda (w: T).(ty3 g c1 v w)))) (ex3 C (\lambda 
(c3: C).(eq C (CHead c2 (Bind Void) (TSort O)) (CHead c3 (Bind Void) (TSort 
O)))) (\lambda (c3: C).(wf3 g c1 c3)) (\lambda (_: C).(\forall (w: T).((ty3 g 
c1 v w) \to False)))) (ex3_intro C (\lambda (c3: C).(eq C (CHead c2 (Bind 
Void) (TSort O)) (CHead c3 (Bind Void) (TSort O)))) (\lambda (c3: C).(wf3 g 
c1 c3)) (\lambda (_: C).(\forall (w: T).((ty3 g c1 v w) \to False))) c2 
(refl_equal C (CHead c2 (Bind Void) (TSort O))) H13 H11))))))))) H6)) 
H5)))))))))) (\lambda (c0: C).(\lambda (c2: C).(\lambda (_: (wf3 g c0 
c2)).(\lambda (_: (((eq C c0 (CHead c1 (Bind b) v)) \to (or (ex3_2 C T 
(\lambda (c3: C).(\lambda (_: T).(eq C c2 (CHead c3 (Bind b) v)))) (\lambda 
(c3: C).(\lambda (_: T).(wf3 g c1 c3))) (\lambda (_: C).(\lambda (w: T).(ty3 
g c1 v w)))) (ex3 C (\lambda (c3: C).(eq C c2 (CHead c3 (Bind Void) (TSort 
O)))) (\lambda (c3: C).(wf3 g c1 c3)) (\lambda (_: C).(\forall (w: T).((ty3 g 
c1 v w) \to False)))))))).(\lambda (u: T).(\lambda (f: F).(\lambda (H3: (eq C 
(CHead c0 (Flat f) u) (CHead c1 (Bind b) v))).(let H4 \def (eq_ind C (CHead 
c0 (Flat f) u) (\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) 
with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match k in K 
return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) I (CHead c1 (Bind b) v) H3) in (False_ind (or (ex3_2 C 
T (\lambda (c3: C).(\lambda (_: T).(eq C c2 (CHead c3 (Bind b) v)))) (\lambda 
(c3: C).(\lambda (_: T).(wf3 g c1 c3))) (\lambda (_: C).(\lambda (w: T).(ty3 
g c1 v w)))) (ex3 C (\lambda (c3: C).(eq C c2 (CHead c3 (Bind Void) (TSort 
O)))) (\lambda (c3: C).(wf3 g c1 c3)) (\lambda (_: C).(\forall (w: T).((ty3 g 
c1 v w) \to False))))) H4))))))))) y x H0))) H)))))).
(* COMMENTS
Initial nodes: 2507
END *)

theorem wf3_gen_flat1:
 \forall (g: G).(\forall (c1: C).(\forall (x: C).(\forall (v: T).(\forall (f: 
F).((wf3 g (CHead c1 (Flat f) v) x) \to (wf3 g c1 x))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (x: C).(\lambda (v: T).(\lambda (f: 
F).(\lambda (H: (wf3 g (CHead c1 (Flat f) v) x)).(insert_eq C (CHead c1 (Flat 
f) v) (\lambda (c: C).(wf3 g c x)) (\lambda (_: C).(wf3 g c1 x)) (\lambda (y: 
C).(\lambda (H0: (wf3 g y x)).(wf3_ind g (\lambda (c: C).(\lambda (c0: 
C).((eq C c (CHead c1 (Flat f) v)) \to (wf3 g c1 c0)))) (\lambda (m: 
nat).(\lambda (H1: (eq C (CSort m) (CHead c1 (Flat f) v))).(let H2 \def 
(eq_ind C (CSort m) (\lambda (ee: C).(match ee in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow 
False])) I (CHead c1 (Flat f) v) H1) in (False_ind (wf3 g c1 (CSort m)) 
H2)))) (\lambda (c0: C).(\lambda (c2: C).(\lambda (_: (wf3 g c0 c2)).(\lambda 
(_: (((eq C c0 (CHead c1 (Flat f) v)) \to (wf3 g c1 c2)))).(\lambda (u: 
T).(\lambda (t: T).(\lambda (_: (ty3 g c0 u t)).(\lambda (b: B).(\lambda (H4: 
(eq C (CHead c0 (Bind b) u) (CHead c1 (Flat f) v))).(let H5 \def (eq_ind C 
(CHead c0 (Bind b) u) (\lambda (ee: C).(match ee in C return (\lambda (_: 
C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match 
k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | (Flat 
_) \Rightarrow False])])) I (CHead c1 (Flat f) v) H4) in (False_ind (wf3 g c1 
(CHead c2 (Bind b) u)) H5))))))))))) (\lambda (c0: C).(\lambda (c2: 
C).(\lambda (_: (wf3 g c0 c2)).(\lambda (_: (((eq C c0 (CHead c1 (Flat f) v)) 
\to (wf3 g c1 c2)))).(\lambda (u: T).(\lambda (_: ((\forall (t: T).((ty3 g c0 
u t) \to False)))).(\lambda (b: B).(\lambda (H4: (eq C (CHead c0 (Bind b) u) 
(CHead c1 (Flat f) v))).(let H5 \def (eq_ind C (CHead c0 (Bind b) u) (\lambda 
(ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow 
False])])) I (CHead c1 (Flat f) v) H4) in (False_ind (wf3 g c1 (CHead c2 
(Bind Void) (TSort O))) H5)))))))))) (\lambda (c0: C).(\lambda (c2: 
C).(\lambda (H1: (wf3 g c0 c2)).(\lambda (H2: (((eq C c0 (CHead c1 (Flat f) 
v)) \to (wf3 g c1 c2)))).(\lambda (u: T).(\lambda (f0: F).(\lambda (H3: (eq C 
(CHead c0 (Flat f0) u) (CHead c1 (Flat f) v))).(let H4 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead c0 (Flat f0) u) (CHead 
c1 (Flat f) v) H3) in ((let H5 \def (f_equal C F (\lambda (e: C).(match e in 
C return (\lambda (_: C).F) with [(CSort _) \Rightarrow f0 | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).F) with [(Bind _) 
\Rightarrow f0 | (Flat f1) \Rightarrow f1])])) (CHead c0 (Flat f0) u) (CHead 
c1 (Flat f) v) H3) in ((let H6 \def (f_equal C T (\lambda (e: C).(match e in 
C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t) 
\Rightarrow t])) (CHead c0 (Flat f0) u) (CHead c1 (Flat f) v) H3) in (\lambda 
(_: (eq F f0 f)).(\lambda (H8: (eq C c0 c1)).(let H9 \def (eq_ind C c0 
(\lambda (c: C).((eq C c (CHead c1 (Flat f) v)) \to (wf3 g c1 c2))) H2 c1 H8) 
in (let H10 \def (eq_ind C c0 (\lambda (c: C).(wf3 g c c2)) H1 c1 H8) in 
H10))))) H5)) H4))))))))) y x H0))) H)))))).
(* COMMENTS
Initial nodes: 737
END *)

theorem wf3_gen_head2:
 \forall (g: G).(\forall (x: C).(\forall (c: C).(\forall (v: T).(\forall (k: 
K).((wf3 g x (CHead c k v)) \to (ex B (\lambda (b: B).(eq K k (Bind b)))))))))
\def
 \lambda (g: G).(\lambda (x: C).(\lambda (c: C).(\lambda (v: T).(\lambda (k: 
K).(\lambda (H: (wf3 g x (CHead c k v))).(insert_eq C (CHead c k v) (\lambda 
(c0: C).(wf3 g x c0)) (\lambda (_: C).(ex B (\lambda (b: B).(eq K k (Bind 
b))))) (\lambda (y: C).(\lambda (H0: (wf3 g x y)).(wf3_ind g (\lambda (_: 
C).(\lambda (c1: C).((eq C c1 (CHead c k v)) \to (ex B (\lambda (b: B).(eq K 
k (Bind b))))))) (\lambda (m: nat).(\lambda (H1: (eq C (CSort m) (CHead c k 
v))).(let H2 \def (eq_ind C (CSort m) (\lambda (ee: C).(match ee in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) 
\Rightarrow False])) I (CHead c k v) H1) in (False_ind (ex B (\lambda (b: 
B).(eq K k (Bind b)))) H2)))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (H1: 
(wf3 g c1 c2)).(\lambda (H2: (((eq C c2 (CHead c k v)) \to (ex B (\lambda (b: 
B).(eq K k (Bind b))))))).(\lambda (u: T).(\lambda (t: T).(\lambda (H3: (ty3 
g c1 u t)).(\lambda (b: B).(\lambda (H4: (eq C (CHead c2 (Bind b) u) (CHead c 
k v))).(let H5 \def (f_equal C C (\lambda (e: C).(match e in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow c2 | (CHead c0 _ _) 
\Rightarrow c0])) (CHead c2 (Bind b) u) (CHead c k v) H4) in ((let H6 \def 
(f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) with 
[(CSort _) \Rightarrow (Bind b) | (CHead _ k0 _) \Rightarrow k0])) (CHead c2 
(Bind b) u) (CHead c k v) H4) in ((let H7 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | 
(CHead _ _ t0) \Rightarrow t0])) (CHead c2 (Bind b) u) (CHead c k v) H4) in 
(\lambda (H8: (eq K (Bind b) k)).(\lambda (H9: (eq C c2 c)).(let H10 \def 
(eq_ind T u (\lambda (t0: T).(ty3 g c1 t0 t)) H3 v H7) in (let H11 \def 
(eq_ind C c2 (\lambda (c0: C).((eq C c0 (CHead c k v)) \to (ex B (\lambda 
(b0: B).(eq K k (Bind b0)))))) H2 c H9) in (let H12 \def (eq_ind C c2 
(\lambda (c0: C).(wf3 g c1 c0)) H1 c H9) in (let H13 \def (eq_ind_r K k 
(\lambda (k0: K).((eq C c (CHead c k0 v)) \to (ex B (\lambda (b0: B).(eq K k0 
(Bind b0)))))) H11 (Bind b) H8) in (eq_ind K (Bind b) (\lambda (k0: K).(ex B 
(\lambda (b0: B).(eq K k0 (Bind b0))))) (ex_intro B (\lambda (b0: B).(eq K 
(Bind b) (Bind b0))) b (refl_equal K (Bind b))) k H8)))))))) H6)) 
H5))))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (H1: (wf3 g c1 
c2)).(\lambda (H2: (((eq C c2 (CHead c k v)) \to (ex B (\lambda (b: B).(eq K 
k (Bind b))))))).(\lambda (u: T).(\lambda (_: ((\forall (t: T).((ty3 g c1 u 
t) \to False)))).(\lambda (_: B).(\lambda (H4: (eq C (CHead c2 (Bind Void) 
(TSort O)) (CHead c k v))).(let H5 \def (f_equal C C (\lambda (e: C).(match e 
in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c2 | (CHead c0 _ 
_) \Rightarrow c0])) (CHead c2 (Bind Void) (TSort O)) (CHead c k v) H4) in 
((let H6 \def (f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: 
C).K) with [(CSort _) \Rightarrow (Bind Void) | (CHead _ k0 _) \Rightarrow 
k0])) (CHead c2 (Bind Void) (TSort O)) (CHead c k v) H4) in ((let H7 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow (TSort O) | (CHead _ _ t) \Rightarrow t])) (CHead c2 
(Bind Void) (TSort O)) (CHead c k v) H4) in (\lambda (H8: (eq K (Bind Void) 
k)).(\lambda (H9: (eq C c2 c)).(let H10 \def (eq_ind C c2 (\lambda (c0: 
C).((eq C c0 (CHead c k v)) \to (ex B (\lambda (b0: B).(eq K k (Bind b0)))))) 
H2 c H9) in (let H11 \def (eq_ind C c2 (\lambda (c0: C).(wf3 g c1 c0)) H1 c 
H9) in (let H12 \def (eq_ind_r K k (\lambda (k0: K).((eq C c (CHead c k0 v)) 
\to (ex B (\lambda (b0: B).(eq K k0 (Bind b0)))))) H10 (Bind Void) H8) in 
(eq_ind K (Bind Void) (\lambda (k0: K).(ex B (\lambda (b0: B).(eq K k0 (Bind 
b0))))) (let H13 \def (eq_ind_r T v (\lambda (t: T).((eq C c (CHead c (Bind 
Void) t)) \to (ex B (\lambda (b0: B).(eq K (Bind Void) (Bind b0)))))) H12 
(TSort O) H7) in (ex_intro B (\lambda (b0: B).(eq K (Bind Void) (Bind b0))) 
Void (refl_equal K (Bind Void)))) k H8))))))) H6)) H5)))))))))) (\lambda (c1: 
C).(\lambda (c2: C).(\lambda (H1: (wf3 g c1 c2)).(\lambda (H2: (((eq C c2 
(CHead c k v)) \to (ex B (\lambda (b: B).(eq K k (Bind b))))))).(\lambda (_: 
T).(\lambda (_: F).(\lambda (H3: (eq C c2 (CHead c k v))).(let H4 \def 
(f_equal C C (\lambda (e: C).e) c2 (CHead c k v) H3) in (let H5 \def (eq_ind 
C c2 (\lambda (c0: C).((eq C c0 (CHead c k v)) \to (ex B (\lambda (b: B).(eq 
K k (Bind b)))))) H2 (CHead c k v) H4) in (let H6 \def (eq_ind C c2 (\lambda 
(c0: C).(wf3 g c1 c0)) H1 (CHead c k v) H4) in (H5 (refl_equal C (CHead c k 
v))))))))))))) x y H0))) H)))))).
(* COMMENTS
Initial nodes: 1225
END *)

