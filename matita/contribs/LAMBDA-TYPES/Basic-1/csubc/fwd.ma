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

include "Basic-1/csubc/defs.ma".

theorem csubc_gen_sort_l:
 \forall (g: G).(\forall (x: C).(\forall (n: nat).((csubc g (CSort n) x) \to 
(eq C x (CSort n)))))
\def
 \lambda (g: G).(\lambda (x: C).(\lambda (n: nat).(\lambda (H: (csubc g 
(CSort n) x)).(insert_eq C (CSort n) (\lambda (c: C).(csubc g c x)) (\lambda 
(c: C).(eq C x c)) (\lambda (y: C).(\lambda (H0: (csubc g y x)).(csubc_ind g 
(\lambda (c: C).(\lambda (c0: C).((eq C c (CSort n)) \to (eq C c0 c)))) 
(\lambda (n0: nat).(\lambda (H1: (eq C (CSort n0) (CSort n))).(let H2 \def 
(f_equal C nat (\lambda (e: C).(match e in C return (\lambda (_: C).nat) with 
[(CSort n1) \Rightarrow n1 | (CHead _ _ _) \Rightarrow n0])) (CSort n0) 
(CSort n) H1) in (eq_ind_r nat n (\lambda (n1: nat).(eq C (CSort n1) (CSort 
n1))) (refl_equal C (CSort n)) n0 H2)))) (\lambda (c1: C).(\lambda (c2: 
C).(\lambda (_: (csubc g c1 c2)).(\lambda (_: (((eq C c1 (CSort n)) \to (eq C 
c2 c1)))).(\lambda (k: K).(\lambda (v: T).(\lambda (H3: (eq C (CHead c1 k v) 
(CSort n))).(let H4 \def (eq_ind C (CHead c1 k v) (\lambda (ee: C).(match ee 
in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead 
_ _ _) \Rightarrow True])) I (CSort n) H3) in (False_ind (eq C (CHead c2 k v) 
(CHead c1 k v)) H4))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (_: 
(csubc g c1 c2)).(\lambda (_: (((eq C c1 (CSort n)) \to (eq C c2 
c1)))).(\lambda (b: B).(\lambda (_: (not (eq B b Void))).(\lambda (u1: 
T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead c1 (Bind Void) u1) (CSort 
n))).(let H5 \def (eq_ind C (CHead c1 (Bind Void) u1) (\lambda (ee: C).(match 
ee in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | 
(CHead _ _ _) \Rightarrow True])) I (CSort n) H4) in (False_ind (eq C (CHead 
c2 (Bind b) u2) (CHead c1 (Bind Void) u1)) H5))))))))))) (\lambda (c1: 
C).(\lambda (c2: C).(\lambda (_: (csubc g c1 c2)).(\lambda (_: (((eq C c1 
(CSort n)) \to (eq C c2 c1)))).(\lambda (v: T).(\lambda (a: A).(\lambda (_: 
(sc3 g (asucc g a) c1 v)).(\lambda (w: T).(\lambda (_: (sc3 g a c2 
w)).(\lambda (H5: (eq C (CHead c1 (Bind Abst) v) (CSort n))).(let H6 \def 
(eq_ind C (CHead c1 (Bind Abst) v) (\lambda (ee: C).(match ee in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ _ _) 
\Rightarrow True])) I (CSort n) H5) in (False_ind (eq C (CHead c2 (Bind Abbr) 
w) (CHead c1 (Bind Abst) v)) H6)))))))))))) y x H0))) H)))).
(* COMMENTS
Initial nodes: 533
END *)

theorem csubc_gen_head_l:
 \forall (g: G).(\forall (c1: C).(\forall (x: C).(\forall (v: T).(\forall (k: 
K).((csubc g (CHead c1 k v) x) \to (or3 (ex2 C (\lambda (c2: C).(eq C x 
(CHead c2 k v))) (\lambda (c2: C).(csubc g c1 c2))) (ex5_3 C T A (\lambda (_: 
C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abst))))) (\lambda (c2: 
C).(\lambda (w: T).(\lambda (_: A).(eq C x (CHead c2 (Bind Abbr) w))))) 
(\lambda (c2: C).(\lambda (_: T).(\lambda (_: A).(csubc g c1 c2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g a) c1 v)))) (\lambda 
(c2: C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c2 w))))) (ex4_3 B C T 
(\lambda (b: B).(\lambda (c2: C).(\lambda (v2: T).(eq C x (CHead c2 (Bind b) 
v2))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind 
Void))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b 
Void))))) (\lambda (_: B).(\lambda (c2: C).(\lambda (_: T).(csubc g c1 
c2)))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (x: C).(\lambda (v: T).(\lambda (k: 
K).(\lambda (H: (csubc g (CHead c1 k v) x)).(insert_eq C (CHead c1 k v) 
(\lambda (c: C).(csubc g c x)) (\lambda (_: C).(or3 (ex2 C (\lambda (c2: 
C).(eq C x (CHead c2 k v))) (\lambda (c2: C).(csubc g c1 c2))) (ex5_3 C T A 
(\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abst))))) 
(\lambda (c2: C).(\lambda (w: T).(\lambda (_: A).(eq C x (CHead c2 (Bind 
Abbr) w))))) (\lambda (c2: C).(\lambda (_: T).(\lambda (_: A).(csubc g c1 
c2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g a) c1 
v)))) (\lambda (c2: C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c2 w))))) 
(ex4_3 B C T (\lambda (b: B).(\lambda (c2: C).(\lambda (v2: T).(eq C x (CHead 
c2 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(eq K k 
(Bind Void))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b 
Void))))) (\lambda (_: B).(\lambda (c2: C).(\lambda (_: T).(csubc g c1 
c2))))))) (\lambda (y: C).(\lambda (H0: (csubc g y x)).(csubc_ind g (\lambda 
(c: C).(\lambda (c0: C).((eq C c (CHead c1 k v)) \to (or3 (ex2 C (\lambda 
(c2: C).(eq C c0 (CHead c2 k v))) (\lambda (c2: C).(csubc g c1 c2))) (ex5_3 C 
T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abst))))) 
(\lambda (c2: C).(\lambda (w: T).(\lambda (_: A).(eq C c0 (CHead c2 (Bind 
Abbr) w))))) (\lambda (c2: C).(\lambda (_: T).(\lambda (_: A).(csubc g c1 
c2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g a) c1 
v)))) (\lambda (c2: C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c2 w))))) 
(ex4_3 B C T (\lambda (b: B).(\lambda (c2: C).(\lambda (v2: T).(eq C c0 
(CHead c2 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
T).(eq K k (Bind Void))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: 
T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c2: C).(\lambda (_: 
T).(csubc g c1 c2))))))))) (\lambda (n: nat).(\lambda (H1: (eq C (CSort n) 
(CHead c1 k v))).(let H2 \def (eq_ind C (CSort n) (\lambda (ee: C).(match ee 
in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow True | (CHead _ 
_ _) \Rightarrow False])) I (CHead c1 k v) H1) in (False_ind (or3 (ex2 C 
(\lambda (c2: C).(eq C (CSort n) (CHead c2 k v))) (\lambda (c2: C).(csubc g 
c1 c2))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k 
(Bind Abst))))) (\lambda (c2: C).(\lambda (w: T).(\lambda (_: A).(eq C (CSort 
n) (CHead c2 (Bind Abbr) w))))) (\lambda (c2: C).(\lambda (_: T).(\lambda (_: 
A).(csubc g c1 c2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g 
(asucc g a) c1 v)))) (\lambda (c2: C).(\lambda (w: T).(\lambda (a: A).(sc3 g 
a c2 w))))) (ex4_3 B C T (\lambda (b: B).(\lambda (c2: C).(\lambda (v2: 
T).(eq C (CSort n) (CHead c2 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: T).(eq K k (Bind Void))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c2: 
C).(\lambda (_: T).(csubc g c1 c2)))))) H2)))) (\lambda (c0: C).(\lambda (c2: 
C).(\lambda (H1: (csubc g c0 c2)).(\lambda (H2: (((eq C c0 (CHead c1 k v)) 
\to (or3 (ex2 C (\lambda (c3: C).(eq C c2 (CHead c3 k v))) (\lambda (c3: 
C).(csubc g c1 c3))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda 
(_: A).(eq K k (Bind Abst))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (_: 
A).(eq C c2 (CHead c3 (Bind Abbr) w))))) (\lambda (c3: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g c1 c3)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(sc3 g (asucc g a) c1 v)))) (\lambda (c3: C).(\lambda (w: 
T).(\lambda (a: A).(sc3 g a c3 w))))) (ex4_3 B C T (\lambda (b: B).(\lambda 
(c3: C).(\lambda (v2: T).(eq C c2 (CHead c3 (Bind b) v2))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind Void))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: 
B).(\lambda (c3: C).(\lambda (_: T).(csubc g c1 c3))))))))).(\lambda (k0: 
K).(\lambda (v0: T).(\lambda (H3: (eq C (CHead c0 k0 v0) (CHead c1 k 
v))).(let H4 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) 
(CHead c0 k0 v0) (CHead c1 k v) H3) in ((let H5 \def (f_equal C K (\lambda 
(e: C).(match e in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k0 
| (CHead _ k1 _) \Rightarrow k1])) (CHead c0 k0 v0) (CHead c1 k v) H3) in 
((let H6 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: 
C).T) with [(CSort _) \Rightarrow v0 | (CHead _ _ t) \Rightarrow t])) (CHead 
c0 k0 v0) (CHead c1 k v) H3) in (\lambda (H7: (eq K k0 k)).(\lambda (H8: (eq 
C c0 c1)).(eq_ind_r T v (\lambda (t: T).(or3 (ex2 C (\lambda (c3: C).(eq C 
(CHead c2 k0 t) (CHead c3 k v))) (\lambda (c3: C).(csubc g c1 c3))) (ex5_3 C 
T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abst))))) 
(\lambda (c3: C).(\lambda (w: T).(\lambda (_: A).(eq C (CHead c2 k0 t) (CHead 
c3 (Bind Abbr) w))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc 
g c1 c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g 
a) c1 v)))) (\lambda (c3: C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 
w))))) (ex4_3 B C T (\lambda (b: B).(\lambda (c3: C).(\lambda (v2: T).(eq C 
(CHead c2 k0 t) (CHead c3 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: T).(eq K k (Bind Void))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g c1 c3))))))) (eq_ind_r K k (\lambda (k1: K).(or3 
(ex2 C (\lambda (c3: C).(eq C (CHead c2 k1 v) (CHead c3 k v))) (\lambda (c3: 
C).(csubc g c1 c3))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda 
(_: A).(eq K k (Bind Abst))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (_: 
A).(eq C (CHead c2 k1 v) (CHead c3 (Bind Abbr) w))))) (\lambda (c3: 
C).(\lambda (_: T).(\lambda (_: A).(csubc g c1 c3)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g a) c1 v)))) (\lambda (c3: 
C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 w))))) (ex4_3 B C T (\lambda 
(b: B).(\lambda (c3: C).(\lambda (v2: T).(eq C (CHead c2 k1 v) (CHead c3 
(Bind b) v2))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(eq K k 
(Bind Void))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b 
Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g c1 
c3))))))) (let H9 \def (eq_ind C c0 (\lambda (c: C).((eq C c (CHead c1 k v)) 
\to (or3 (ex2 C (\lambda (c3: C).(eq C c2 (CHead c3 k v))) (\lambda (c3: 
C).(csubc g c1 c3))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda 
(_: A).(eq K k (Bind Abst))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (_: 
A).(eq C c2 (CHead c3 (Bind Abbr) w))))) (\lambda (c3: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g c1 c3)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(sc3 g (asucc g a) c1 v)))) (\lambda (c3: C).(\lambda (w: 
T).(\lambda (a: A).(sc3 g a c3 w))))) (ex4_3 B C T (\lambda (b: B).(\lambda 
(c3: C).(\lambda (v2: T).(eq C c2 (CHead c3 (Bind b) v2))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind Void))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: 
B).(\lambda (c3: C).(\lambda (_: T).(csubc g c1 c3)))))))) H2 c1 H8) in (let 
H10 \def (eq_ind C c0 (\lambda (c: C).(csubc g c c2)) H1 c1 H8) in 
(or3_intro0 (ex2 C (\lambda (c3: C).(eq C (CHead c2 k v) (CHead c3 k v))) 
(\lambda (c3: C).(csubc g c1 c3))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(eq K k (Bind Abst))))) (\lambda (c3: C).(\lambda (w: 
T).(\lambda (_: A).(eq C (CHead c2 k v) (CHead c3 (Bind Abbr) w))))) (\lambda 
(c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c1 c3)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g a) c1 v)))) (\lambda (c3: 
C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 w))))) (ex4_3 B C T (\lambda 
(b: B).(\lambda (c3: C).(\lambda (v2: T).(eq C (CHead c2 k v) (CHead c3 (Bind 
b) v2))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind 
Void))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b 
Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g c1 
c3))))) (ex_intro2 C (\lambda (c3: C).(eq C (CHead c2 k v) (CHead c3 k v))) 
(\lambda (c3: C).(csubc g c1 c3)) c2 (refl_equal C (CHead c2 k v)) H10)))) k0 
H7) v0 H6)))) H5)) H4))))))))) (\lambda (c0: C).(\lambda (c2: C).(\lambda 
(H1: (csubc g c0 c2)).(\lambda (H2: (((eq C c0 (CHead c1 k v)) \to (or3 (ex2 
C (\lambda (c3: C).(eq C c2 (CHead c3 k v))) (\lambda (c3: C).(csubc g c1 
c3))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k 
(Bind Abst))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (_: A).(eq C c2 
(CHead c3 (Bind Abbr) w))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: 
A).(csubc g c1 c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g 
(asucc g a) c1 v)))) (\lambda (c3: C).(\lambda (w: T).(\lambda (a: A).(sc3 g 
a c3 w))))) (ex4_3 B C T (\lambda (b: B).(\lambda (c3: C).(\lambda (v2: 
T).(eq C c2 (CHead c3 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: T).(eq K k (Bind Void))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g c1 c3))))))))).(\lambda (b: B).(\lambda (H3: (not 
(eq B b Void))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead 
c0 (Bind Void) u1) (CHead c1 k v))).(let H5 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | 
(CHead c _ _) \Rightarrow c])) (CHead c0 (Bind Void) u1) (CHead c1 k v) H4) 
in ((let H6 \def (f_equal C K (\lambda (e: C).(match e in C return (\lambda 
(_: C).K) with [(CSort _) \Rightarrow (Bind Void) | (CHead _ k0 _) 
\Rightarrow k0])) (CHead c0 (Bind Void) u1) (CHead c1 k v) H4) in ((let H7 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u1 | (CHead _ _ t) \Rightarrow t])) (CHead c0 
(Bind Void) u1) (CHead c1 k v) H4) in (\lambda (H8: (eq K (Bind Void) 
k)).(\lambda (H9: (eq C c0 c1)).(let H10 \def (eq_ind C c0 (\lambda (c: 
C).((eq C c (CHead c1 k v)) \to (or3 (ex2 C (\lambda (c3: C).(eq C c2 (CHead 
c3 k v))) (\lambda (c3: C).(csubc g c1 c3))) (ex5_3 C T A (\lambda (_: 
C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abst))))) (\lambda (c3: 
C).(\lambda (w: T).(\lambda (_: A).(eq C c2 (CHead c3 (Bind Abbr) w))))) 
(\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c1 c3)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g a) c1 v)))) (\lambda 
(c3: C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 w))))) (ex4_3 B C T 
(\lambda (b0: B).(\lambda (c3: C).(\lambda (v2: T).(eq C c2 (CHead c3 (Bind 
b0) v2))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind 
Void))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b0 
Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g c1 
c3)))))))) H2 c1 H9) in (let H11 \def (eq_ind C c0 (\lambda (c: C).(csubc g c 
c2)) H1 c1 H9) in (let H12 \def (eq_ind_r K k (\lambda (k0: K).((eq C c1 
(CHead c1 k0 v)) \to (or3 (ex2 C (\lambda (c3: C).(eq C c2 (CHead c3 k0 v))) 
(\lambda (c3: C).(csubc g c1 c3))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(eq K k0 (Bind Abst))))) (\lambda (c3: C).(\lambda (w: 
T).(\lambda (_: A).(eq C c2 (CHead c3 (Bind Abbr) w))))) (\lambda (c3: 
C).(\lambda (_: T).(\lambda (_: A).(csubc g c1 c3)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g a) c1 v)))) (\lambda (c3: 
C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 w))))) (ex4_3 B C T (\lambda 
(b0: B).(\lambda (c3: C).(\lambda (v2: T).(eq C c2 (CHead c3 (Bind b0) 
v2))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(eq K k0 (Bind 
Void))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b0 
Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g c1 
c3)))))))) H10 (Bind Void) H8) in (eq_ind K (Bind Void) (\lambda (k0: K).(or3 
(ex2 C (\lambda (c3: C).(eq C (CHead c2 (Bind b) u2) (CHead c3 k0 v))) 
(\lambda (c3: C).(csubc g c1 c3))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(eq K k0 (Bind Abst))))) (\lambda (c3: C).(\lambda (w: 
T).(\lambda (_: A).(eq C (CHead c2 (Bind b) u2) (CHead c3 (Bind Abbr) w))))) 
(\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c1 c3)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g a) c1 v)))) (\lambda 
(c3: C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 w))))) (ex4_3 B C T 
(\lambda (b0: B).(\lambda (c3: C).(\lambda (v2: T).(eq C (CHead c2 (Bind b) 
u2) (CHead c3 (Bind b0) v2))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
T).(eq K k0 (Bind Void))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (_: 
T).(not (eq B b0 Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: 
T).(csubc g c1 c3))))))) (or3_intro2 (ex2 C (\lambda (c3: C).(eq C (CHead c2 
(Bind b) u2) (CHead c3 (Bind Void) v))) (\lambda (c3: C).(csubc g c1 c3))) 
(ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K (Bind 
Void) (Bind Abst))))) (\lambda (c3: C).(\lambda (w: T).(\lambda (_: A).(eq C 
(CHead c2 (Bind b) u2) (CHead c3 (Bind Abbr) w))))) (\lambda (c3: C).(\lambda 
(_: T).(\lambda (_: A).(csubc g c1 c3)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(sc3 g (asucc g a) c1 v)))) (\lambda (c3: C).(\lambda (w: 
T).(\lambda (a: A).(sc3 g a c3 w))))) (ex4_3 B C T (\lambda (b0: B).(\lambda 
(c3: C).(\lambda (v2: T).(eq C (CHead c2 (Bind b) u2) (CHead c3 (Bind b0) 
v2))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: T).(eq K (Bind Void) 
(Bind Void))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (_: T).(not (eq B 
b0 Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g c1 
c3))))) (ex4_3_intro B C T (\lambda (b0: B).(\lambda (c3: C).(\lambda (v2: 
T).(eq C (CHead c2 (Bind b) u2) (CHead c3 (Bind b0) v2))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: T).(eq K (Bind Void) (Bind Void))))) (\lambda 
(b0: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b0 Void))))) (\lambda (_: 
B).(\lambda (c3: C).(\lambda (_: T).(csubc g c1 c3)))) b c2 u2 (refl_equal C 
(CHead c2 (Bind b) u2)) (refl_equal K (Bind Void)) H3 H11)) k H8))))))) H6)) 
H5))))))))))) (\lambda (c0: C).(\lambda (c2: C).(\lambda (H1: (csubc g c0 
c2)).(\lambda (H2: (((eq C c0 (CHead c1 k v)) \to (or3 (ex2 C (\lambda (c3: 
C).(eq C c2 (CHead c3 k v))) (\lambda (c3: C).(csubc g c1 c3))) (ex5_3 C T A 
(\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abst))))) 
(\lambda (c3: C).(\lambda (w: T).(\lambda (_: A).(eq C c2 (CHead c3 (Bind 
Abbr) w))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c1 
c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g (asucc g a) c1 
v)))) (\lambda (c3: C).(\lambda (w: T).(\lambda (a: A).(sc3 g a c3 w))))) 
(ex4_3 B C T (\lambda (b: B).(\lambda (c3: C).(\lambda (v2: T).(eq C c2 
(CHead c3 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
T).(eq K k (Bind Void))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: 
T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: 
T).(csubc g c1 c3))))))))).(\lambda (v0: T).(\lambda (a: A).(\lambda (H3: 
(sc3 g (asucc g a) c0 v0)).(\lambda (w: T).(\lambda (H4: (sc3 g a c2 
w)).(\lambda (H5: (eq C (CHead c0 (Bind Abst) v0) (CHead c1 k v))).(let H6 
\def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) 
with [(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead c0 
(Bind Abst) v0) (CHead c1 k v) H5) in ((let H7 \def (f_equal C K (\lambda (e: 
C).(match e in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow (Bind 
Abst) | (CHead _ k0 _) \Rightarrow k0])) (CHead c0 (Bind Abst) v0) (CHead c1 
k v) H5) in ((let H8 \def (f_equal C T (\lambda (e: C).(match e in C return 
(\lambda (_: C).T) with [(CSort _) \Rightarrow v0 | (CHead _ _ t) \Rightarrow 
t])) (CHead c0 (Bind Abst) v0) (CHead c1 k v) H5) in (\lambda (H9: (eq K 
(Bind Abst) k)).(\lambda (H10: (eq C c0 c1)).(let H11 \def (eq_ind T v0 
(\lambda (t: T).(sc3 g (asucc g a) c0 t)) H3 v H8) in (let H12 \def (eq_ind C 
c0 (\lambda (c: C).(sc3 g (asucc g a) c v)) H11 c1 H10) in (let H13 \def 
(eq_ind C c0 (\lambda (c: C).((eq C c (CHead c1 k v)) \to (or3 (ex2 C 
(\lambda (c3: C).(eq C c2 (CHead c3 k v))) (\lambda (c3: C).(csubc g c1 c3))) 
(ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind 
Abst))))) (\lambda (c3: C).(\lambda (w0: T).(\lambda (_: A).(eq C c2 (CHead 
c3 (Bind Abbr) w0))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: 
A).(csubc g c1 c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(sc3 g 
(asucc g a0) c1 v)))) (\lambda (c3: C).(\lambda (w0: T).(\lambda (a0: A).(sc3 
g a0 c3 w0))))) (ex4_3 B C T (\lambda (b: B).(\lambda (c3: C).(\lambda (v2: 
T).(eq C c2 (CHead c3 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: T).(eq K k (Bind Void))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g c1 c3)))))))) H2 c1 H10) in (let H14 \def (eq_ind 
C c0 (\lambda (c: C).(csubc g c c2)) H1 c1 H10) in (let H15 \def (eq_ind_r K 
k (\lambda (k0: K).((eq C c1 (CHead c1 k0 v)) \to (or3 (ex2 C (\lambda (c3: 
C).(eq C c2 (CHead c3 k0 v))) (\lambda (c3: C).(csubc g c1 c3))) (ex5_3 C T A 
(\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k0 (Bind Abst))))) 
(\lambda (c3: C).(\lambda (w0: T).(\lambda (_: A).(eq C c2 (CHead c3 (Bind 
Abbr) w0))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c1 
c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(sc3 g (asucc g a0) 
c1 v)))) (\lambda (c3: C).(\lambda (w0: T).(\lambda (a0: A).(sc3 g a0 c3 
w0))))) (ex4_3 B C T (\lambda (b: B).(\lambda (c3: C).(\lambda (v2: T).(eq C 
c2 (CHead c3 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
T).(eq K k0 (Bind Void))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: 
T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: 
T).(csubc g c1 c3)))))))) H13 (Bind Abst) H9) in (eq_ind K (Bind Abst) 
(\lambda (k0: K).(or3 (ex2 C (\lambda (c3: C).(eq C (CHead c2 (Bind Abbr) w) 
(CHead c3 k0 v))) (\lambda (c3: C).(csubc g c1 c3))) (ex5_3 C T A (\lambda 
(_: C).(\lambda (_: T).(\lambda (_: A).(eq K k0 (Bind Abst))))) (\lambda (c3: 
C).(\lambda (w0: T).(\lambda (_: A).(eq C (CHead c2 (Bind Abbr) w) (CHead c3 
(Bind Abbr) w0))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g 
c1 c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(sc3 g (asucc g 
a0) c1 v)))) (\lambda (c3: C).(\lambda (w0: T).(\lambda (a0: A).(sc3 g a0 c3 
w0))))) (ex4_3 B C T (\lambda (b: B).(\lambda (c3: C).(\lambda (v2: T).(eq C 
(CHead c2 (Bind Abbr) w) (CHead c3 (Bind b) v2))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (_: T).(eq K k0 (Bind Void))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g c1 c3))))))) (or3_intro1 (ex2 C (\lambda (c3: 
C).(eq C (CHead c2 (Bind Abbr) w) (CHead c3 (Bind Abst) v))) (\lambda (c3: 
C).(csubc g c1 c3))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda 
(_: A).(eq K (Bind Abst) (Bind Abst))))) (\lambda (c3: C).(\lambda (w0: 
T).(\lambda (_: A).(eq C (CHead c2 (Bind Abbr) w) (CHead c3 (Bind Abbr) 
w0))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c1 c3)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(sc3 g (asucc g a0) c1 v)))) 
(\lambda (c3: C).(\lambda (w0: T).(\lambda (a0: A).(sc3 g a0 c3 w0))))) 
(ex4_3 B C T (\lambda (b: B).(\lambda (c3: C).(\lambda (v2: T).(eq C (CHead 
c2 (Bind Abbr) w) (CHead c3 (Bind b) v2))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: T).(eq K (Bind Abst) (Bind Void))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g c1 c3))))) (ex5_3_intro C T A (\lambda (_: 
C).(\lambda (_: T).(\lambda (_: A).(eq K (Bind Abst) (Bind Abst))))) (\lambda 
(c3: C).(\lambda (w0: T).(\lambda (_: A).(eq C (CHead c2 (Bind Abbr) w) 
(CHead c3 (Bind Abbr) w0))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: 
A).(csubc g c1 c3)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(sc3 g 
(asucc g a0) c1 v)))) (\lambda (c3: C).(\lambda (w0: T).(\lambda (a0: A).(sc3 
g a0 c3 w0)))) c2 w a (refl_equal K (Bind Abst)) (refl_equal C (CHead c2 
(Bind Abbr) w)) H14 H12 H4)) k H9))))))))) H7)) H6)))))))))))) y x H0))) 
H)))))).
(* COMMENTS
Initial nodes: 5205
END *)

theorem csubc_gen_sort_r:
 \forall (g: G).(\forall (x: C).(\forall (n: nat).((csubc g x (CSort n)) \to 
(eq C x (CSort n)))))
\def
 \lambda (g: G).(\lambda (x: C).(\lambda (n: nat).(\lambda (H: (csubc g x 
(CSort n))).(insert_eq C (CSort n) (\lambda (c: C).(csubc g x c)) (\lambda 
(c: C).(eq C x c)) (\lambda (y: C).(\lambda (H0: (csubc g x y)).(csubc_ind g 
(\lambda (c: C).(\lambda (c0: C).((eq C c0 (CSort n)) \to (eq C c c0)))) 
(\lambda (n0: nat).(\lambda (H1: (eq C (CSort n0) (CSort n))).(let H2 \def 
(f_equal C nat (\lambda (e: C).(match e in C return (\lambda (_: C).nat) with 
[(CSort n1) \Rightarrow n1 | (CHead _ _ _) \Rightarrow n0])) (CSort n0) 
(CSort n) H1) in (eq_ind_r nat n (\lambda (n1: nat).(eq C (CSort n1) (CSort 
n1))) (refl_equal C (CSort n)) n0 H2)))) (\lambda (c1: C).(\lambda (c2: 
C).(\lambda (_: (csubc g c1 c2)).(\lambda (_: (((eq C c2 (CSort n)) \to (eq C 
c1 c2)))).(\lambda (k: K).(\lambda (v: T).(\lambda (H3: (eq C (CHead c2 k v) 
(CSort n))).(let H4 \def (eq_ind C (CHead c2 k v) (\lambda (ee: C).(match ee 
in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead 
_ _ _) \Rightarrow True])) I (CSort n) H3) in (False_ind (eq C (CHead c1 k v) 
(CHead c2 k v)) H4))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (_: 
(csubc g c1 c2)).(\lambda (_: (((eq C c2 (CSort n)) \to (eq C c1 
c2)))).(\lambda (b: B).(\lambda (_: (not (eq B b Void))).(\lambda (u1: 
T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead c2 (Bind b) u2) (CSort 
n))).(let H5 \def (eq_ind C (CHead c2 (Bind b) u2) (\lambda (ee: C).(match ee 
in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead 
_ _ _) \Rightarrow True])) I (CSort n) H4) in (False_ind (eq C (CHead c1 
(Bind Void) u1) (CHead c2 (Bind b) u2)) H5))))))))))) (\lambda (c1: 
C).(\lambda (c2: C).(\lambda (_: (csubc g c1 c2)).(\lambda (_: (((eq C c2 
(CSort n)) \to (eq C c1 c2)))).(\lambda (v: T).(\lambda (a: A).(\lambda (_: 
(sc3 g (asucc g a) c1 v)).(\lambda (w: T).(\lambda (_: (sc3 g a c2 
w)).(\lambda (H5: (eq C (CHead c2 (Bind Abbr) w) (CSort n))).(let H6 \def 
(eq_ind C (CHead c2 (Bind Abbr) w) (\lambda (ee: C).(match ee in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ _ _) 
\Rightarrow True])) I (CSort n) H5) in (False_ind (eq C (CHead c1 (Bind Abst) 
v) (CHead c2 (Bind Abbr) w)) H6)))))))))))) x y H0))) H)))).
(* COMMENTS
Initial nodes: 533
END *)

theorem csubc_gen_head_r:
 \forall (g: G).(\forall (c2: C).(\forall (x: C).(\forall (w: T).(\forall (k: 
K).((csubc g x (CHead c2 k w)) \to (or3 (ex2 C (\lambda (c1: C).(eq C x 
(CHead c1 k w))) (\lambda (c1: C).(csubc g c1 c2))) (ex5_3 C T A (\lambda (_: 
C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abbr))))) (\lambda (c1: 
C).(\lambda (v: T).(\lambda (_: A).(eq C x (CHead c1 (Bind Abst) v))))) 
(\lambda (c1: C).(\lambda (_: T).(\lambda (_: A).(csubc g c1 c2)))) (\lambda 
(c1: C).(\lambda (v: T).(\lambda (a: A).(sc3 g (asucc g a) c1 v)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g a c2 w))))) (ex4_3 B C T 
(\lambda (_: B).(\lambda (c1: C).(\lambda (v1: T).(eq C x (CHead c1 (Bind 
Void) v1))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind 
b))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) 
(\lambda (_: B).(\lambda (c1: C).(\lambda (_: T).(csubc g c1 c2)))))))))))
\def
 \lambda (g: G).(\lambda (c2: C).(\lambda (x: C).(\lambda (w: T).(\lambda (k: 
K).(\lambda (H: (csubc g x (CHead c2 k w))).(insert_eq C (CHead c2 k w) 
(\lambda (c: C).(csubc g x c)) (\lambda (_: C).(or3 (ex2 C (\lambda (c1: 
C).(eq C x (CHead c1 k w))) (\lambda (c1: C).(csubc g c1 c2))) (ex5_3 C T A 
(\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abbr))))) 
(\lambda (c1: C).(\lambda (v: T).(\lambda (_: A).(eq C x (CHead c1 (Bind 
Abst) v))))) (\lambda (c1: C).(\lambda (_: T).(\lambda (_: A).(csubc g c1 
c2)))) (\lambda (c1: C).(\lambda (v: T).(\lambda (a: A).(sc3 g (asucc g a) c1 
v)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g a c2 w))))) 
(ex4_3 B C T (\lambda (_: B).(\lambda (c1: C).(\lambda (v1: T).(eq C x (CHead 
c1 (Bind Void) v1))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(eq K 
k (Bind b))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b 
Void))))) (\lambda (_: B).(\lambda (c1: C).(\lambda (_: T).(csubc g c1 
c2))))))) (\lambda (y: C).(\lambda (H0: (csubc g x y)).(csubc_ind g (\lambda 
(c: C).(\lambda (c0: C).((eq C c0 (CHead c2 k w)) \to (or3 (ex2 C (\lambda 
(c1: C).(eq C c (CHead c1 k w))) (\lambda (c1: C).(csubc g c1 c2))) (ex5_3 C 
T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abbr))))) 
(\lambda (c1: C).(\lambda (v: T).(\lambda (_: A).(eq C c (CHead c1 (Bind 
Abst) v))))) (\lambda (c1: C).(\lambda (_: T).(\lambda (_: A).(csubc g c1 
c2)))) (\lambda (c1: C).(\lambda (v: T).(\lambda (a: A).(sc3 g (asucc g a) c1 
v)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g a c2 w))))) 
(ex4_3 B C T (\lambda (_: B).(\lambda (c1: C).(\lambda (v1: T).(eq C c (CHead 
c1 (Bind Void) v1))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(eq K 
k (Bind b))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b 
Void))))) (\lambda (_: B).(\lambda (c1: C).(\lambda (_: T).(csubc g c1 
c2))))))))) (\lambda (n: nat).(\lambda (H1: (eq C (CSort n) (CHead c2 k 
w))).(let H2 \def (eq_ind C (CSort n) (\lambda (ee: C).(match ee in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow True | (CHead _ _ _) 
\Rightarrow False])) I (CHead c2 k w) H1) in (False_ind (or3 (ex2 C (\lambda 
(c1: C).(eq C (CSort n) (CHead c1 k w))) (\lambda (c1: C).(csubc g c1 c2))) 
(ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind 
Abbr))))) (\lambda (c1: C).(\lambda (v: T).(\lambda (_: A).(eq C (CSort n) 
(CHead c1 (Bind Abst) v))))) (\lambda (c1: C).(\lambda (_: T).(\lambda (_: 
A).(csubc g c1 c2)))) (\lambda (c1: C).(\lambda (v: T).(\lambda (a: A).(sc3 g 
(asucc g a) c1 v)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g a 
c2 w))))) (ex4_3 B C T (\lambda (_: B).(\lambda (c1: C).(\lambda (v1: T).(eq 
C (CSort n) (CHead c1 (Bind Void) v1))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(eq K k (Bind b))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c1: 
C).(\lambda (_: T).(csubc g c1 c2)))))) H2)))) (\lambda (c1: C).(\lambda (c0: 
C).(\lambda (H1: (csubc g c1 c0)).(\lambda (H2: (((eq C c0 (CHead c2 k w)) 
\to (or3 (ex2 C (\lambda (c3: C).(eq C c1 (CHead c3 k w))) (\lambda (c3: 
C).(csubc g c3 c2))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda 
(_: A).(eq K k (Bind Abbr))))) (\lambda (c3: C).(\lambda (v: T).(\lambda (_: 
A).(eq C c1 (CHead c3 (Bind Abst) v))))) (\lambda (c3: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g c3 c2)))) (\lambda (c3: C).(\lambda (v: 
T).(\lambda (a: A).(sc3 g (asucc g a) c3 v)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(sc3 g a c2 w))))) (ex4_3 B C T (\lambda (_: B).(\lambda 
(c3: C).(\lambda (v1: T).(eq C c1 (CHead c3 (Bind Void) v1))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind b))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: 
B).(\lambda (c3: C).(\lambda (_: T).(csubc g c3 c2))))))))).(\lambda (k0: 
K).(\lambda (v: T).(\lambda (H3: (eq C (CHead c0 k0 v) (CHead c2 k w))).(let 
H4 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) 
with [(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead c0 k0 
v) (CHead c2 k w) H3) in ((let H5 \def (f_equal C K (\lambda (e: C).(match e 
in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k0 | (CHead _ k1 
_) \Rightarrow k1])) (CHead c0 k0 v) (CHead c2 k w) H3) in ((let H6 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow v | (CHead _ _ t) \Rightarrow t])) (CHead c0 k0 v) 
(CHead c2 k w) H3) in (\lambda (H7: (eq K k0 k)).(\lambda (H8: (eq C c0 
c2)).(eq_ind_r T w (\lambda (t: T).(or3 (ex2 C (\lambda (c3: C).(eq C (CHead 
c1 k0 t) (CHead c3 k w))) (\lambda (c3: C).(csubc g c3 c2))) (ex5_3 C T A 
(\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abbr))))) 
(\lambda (c3: C).(\lambda (v0: T).(\lambda (_: A).(eq C (CHead c1 k0 t) 
(CHead c3 (Bind Abst) v0))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: 
A).(csubc g c3 c2)))) (\lambda (c3: C).(\lambda (v0: T).(\lambda (a: A).(sc3 
g (asucc g a) c3 v0)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 
g a c2 w))))) (ex4_3 B C T (\lambda (_: B).(\lambda (c3: C).(\lambda (v1: 
T).(eq C (CHead c1 k0 t) (CHead c3 (Bind Void) v1))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind b))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: 
B).(\lambda (c3: C).(\lambda (_: T).(csubc g c3 c2))))))) (eq_ind_r K k 
(\lambda (k1: K).(or3 (ex2 C (\lambda (c3: C).(eq C (CHead c1 k1 w) (CHead c3 
k w))) (\lambda (c3: C).(csubc g c3 c2))) (ex5_3 C T A (\lambda (_: 
C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abbr))))) (\lambda (c3: 
C).(\lambda (v0: T).(\lambda (_: A).(eq C (CHead c1 k1 w) (CHead c3 (Bind 
Abst) v0))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c3 
c2)))) (\lambda (c3: C).(\lambda (v0: T).(\lambda (a: A).(sc3 g (asucc g a) 
c3 v0)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g a c2 w))))) 
(ex4_3 B C T (\lambda (_: B).(\lambda (c3: C).(\lambda (v1: T).(eq C (CHead 
c1 k1 w) (CHead c3 (Bind Void) v1))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(eq K k (Bind b))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g c3 c2))))))) (let H9 \def (eq_ind C c0 (\lambda 
(c: C).((eq C c (CHead c2 k w)) \to (or3 (ex2 C (\lambda (c3: C).(eq C c1 
(CHead c3 k w))) (\lambda (c3: C).(csubc g c3 c2))) (ex5_3 C T A (\lambda (_: 
C).(\lambda (_: T).(\lambda (_: A).(eq K k (Bind Abbr))))) (\lambda (c3: 
C).(\lambda (v0: T).(\lambda (_: A).(eq C c1 (CHead c3 (Bind Abst) v0))))) 
(\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c3 c2)))) (\lambda 
(c3: C).(\lambda (v0: T).(\lambda (a: A).(sc3 g (asucc g a) c3 v0)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g a c2 w))))) (ex4_3 B C 
T (\lambda (_: B).(\lambda (c3: C).(\lambda (v1: T).(eq C c1 (CHead c3 (Bind 
Void) v1))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind 
b))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) 
(\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g c3 c2)))))))) H2 c2 
H8) in (let H10 \def (eq_ind C c0 (\lambda (c: C).(csubc g c1 c)) H1 c2 H8) 
in (or3_intro0 (ex2 C (\lambda (c3: C).(eq C (CHead c1 k w) (CHead c3 k w))) 
(\lambda (c3: C).(csubc g c3 c2))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(eq K k (Bind Abbr))))) (\lambda (c3: C).(\lambda (v0: 
T).(\lambda (_: A).(eq C (CHead c1 k w) (CHead c3 (Bind Abst) v0))))) 
(\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c3 c2)))) (\lambda 
(c3: C).(\lambda (v0: T).(\lambda (a: A).(sc3 g (asucc g a) c3 v0)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g a c2 w))))) (ex4_3 B C 
T (\lambda (_: B).(\lambda (c3: C).(\lambda (v1: T).(eq C (CHead c1 k w) 
(CHead c3 (Bind Void) v1))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: 
T).(eq K k (Bind b))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(not 
(eq B b Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g 
c3 c2))))) (ex_intro2 C (\lambda (c3: C).(eq C (CHead c1 k w) (CHead c3 k 
w))) (\lambda (c3: C).(csubc g c3 c2)) c1 (refl_equal C (CHead c1 k w)) 
H10)))) k0 H7) v H6)))) H5)) H4))))))))) (\lambda (c1: C).(\lambda (c0: 
C).(\lambda (H1: (csubc g c1 c0)).(\lambda (H2: (((eq C c0 (CHead c2 k w)) 
\to (or3 (ex2 C (\lambda (c3: C).(eq C c1 (CHead c3 k w))) (\lambda (c3: 
C).(csubc g c3 c2))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda 
(_: A).(eq K k (Bind Abbr))))) (\lambda (c3: C).(\lambda (v: T).(\lambda (_: 
A).(eq C c1 (CHead c3 (Bind Abst) v))))) (\lambda (c3: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g c3 c2)))) (\lambda (c3: C).(\lambda (v: 
T).(\lambda (a: A).(sc3 g (asucc g a) c3 v)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(sc3 g a c2 w))))) (ex4_3 B C T (\lambda (_: B).(\lambda 
(c3: C).(\lambda (v1: T).(eq C c1 (CHead c3 (Bind Void) v1))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind b))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: 
B).(\lambda (c3: C).(\lambda (_: T).(csubc g c3 c2))))))))).(\lambda (b: 
B).(\lambda (H3: (not (eq B b Void))).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (H4: (eq C (CHead c0 (Bind b) u2) (CHead c2 k w))).(let H5 \def 
(f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead c0 (Bind b) 
u2) (CHead c2 k w) H4) in ((let H6 \def (f_equal C K (\lambda (e: C).(match e 
in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow (Bind b) | (CHead 
_ k0 _) \Rightarrow k0])) (CHead c0 (Bind b) u2) (CHead c2 k w) H4) in ((let 
H7 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u2 | (CHead _ _ t) \Rightarrow t])) (CHead c0 
(Bind b) u2) (CHead c2 k w) H4) in (\lambda (H8: (eq K (Bind b) k)).(\lambda 
(H9: (eq C c0 c2)).(let H10 \def (eq_ind C c0 (\lambda (c: C).((eq C c (CHead 
c2 k w)) \to (or3 (ex2 C (\lambda (c3: C).(eq C c1 (CHead c3 k w))) (\lambda 
(c3: C).(csubc g c3 c2))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(eq K k (Bind Abbr))))) (\lambda (c3: C).(\lambda (v: 
T).(\lambda (_: A).(eq C c1 (CHead c3 (Bind Abst) v))))) (\lambda (c3: 
C).(\lambda (_: T).(\lambda (_: A).(csubc g c3 c2)))) (\lambda (c3: 
C).(\lambda (v: T).(\lambda (a: A).(sc3 g (asucc g a) c3 v)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(sc3 g a c2 w))))) (ex4_3 B C T (\lambda 
(_: B).(\lambda (c3: C).(\lambda (v1: T).(eq C c1 (CHead c3 (Bind Void) 
v1))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind 
b0))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b0 
Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g c3 
c2)))))))) H2 c2 H9) in (let H11 \def (eq_ind C c0 (\lambda (c: C).(csubc g 
c1 c)) H1 c2 H9) in (let H12 \def (eq_ind_r K k (\lambda (k0: K).((eq C c2 
(CHead c2 k0 w)) \to (or3 (ex2 C (\lambda (c3: C).(eq C c1 (CHead c3 k0 w))) 
(\lambda (c3: C).(csubc g c3 c2))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(eq K k0 (Bind Abbr))))) (\lambda (c3: C).(\lambda (v: 
T).(\lambda (_: A).(eq C c1 (CHead c3 (Bind Abst) v))))) (\lambda (c3: 
C).(\lambda (_: T).(\lambda (_: A).(csubc g c3 c2)))) (\lambda (c3: 
C).(\lambda (v: T).(\lambda (a: A).(sc3 g (asucc g a) c3 v)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(sc3 g a c2 w))))) (ex4_3 B C T (\lambda 
(_: B).(\lambda (c3: C).(\lambda (v1: T).(eq C c1 (CHead c3 (Bind Void) 
v1))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (_: T).(eq K k0 (Bind 
b0))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (_: T).(not (eq B b0 
Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g c3 
c2)))))))) H10 (Bind b) H8) in (eq_ind K (Bind b) (\lambda (k0: K).(or3 (ex2 
C (\lambda (c3: C).(eq C (CHead c1 (Bind Void) u1) (CHead c3 k0 w))) (\lambda 
(c3: C).(csubc g c3 c2))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: 
T).(\lambda (_: A).(eq K k0 (Bind Abbr))))) (\lambda (c3: C).(\lambda (v: 
T).(\lambda (_: A).(eq C (CHead c1 (Bind Void) u1) (CHead c3 (Bind Abst) 
v))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c3 c2)))) 
(\lambda (c3: C).(\lambda (v: T).(\lambda (a: A).(sc3 g (asucc g a) c3 v)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g a c2 w))))) (ex4_3 B C 
T (\lambda (_: B).(\lambda (c3: C).(\lambda (v1: T).(eq C (CHead c1 (Bind 
Void) u1) (CHead c3 (Bind Void) v1))))) (\lambda (b0: B).(\lambda (_: 
C).(\lambda (_: T).(eq K k0 (Bind b0))))) (\lambda (b0: B).(\lambda (_: 
C).(\lambda (_: T).(not (eq B b0 Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g c3 c2))))))) (or3_intro2 (ex2 C (\lambda (c3: 
C).(eq C (CHead c1 (Bind Void) u1) (CHead c3 (Bind b) w))) (\lambda (c3: 
C).(csubc g c3 c2))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda 
(_: A).(eq K (Bind b) (Bind Abbr))))) (\lambda (c3: C).(\lambda (v: 
T).(\lambda (_: A).(eq C (CHead c1 (Bind Void) u1) (CHead c3 (Bind Abst) 
v))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c3 c2)))) 
(\lambda (c3: C).(\lambda (v: T).(\lambda (a: A).(sc3 g (asucc g a) c3 v)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(sc3 g a c2 w))))) (ex4_3 B C 
T (\lambda (_: B).(\lambda (c3: C).(\lambda (v1: T).(eq C (CHead c1 (Bind 
Void) u1) (CHead c3 (Bind Void) v1))))) (\lambda (b0: B).(\lambda (_: 
C).(\lambda (_: T).(eq K (Bind b) (Bind b0))))) (\lambda (b0: B).(\lambda (_: 
C).(\lambda (_: T).(not (eq B b0 Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g c3 c2))))) (ex4_3_intro B C T (\lambda (_: 
B).(\lambda (c3: C).(\lambda (v1: T).(eq C (CHead c1 (Bind Void) u1) (CHead 
c3 (Bind Void) v1))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (_: T).(eq K 
(Bind b) (Bind b0))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (_: T).(not 
(eq B b0 Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g 
c3 c2)))) b c1 u1 (refl_equal C (CHead c1 (Bind Void) u1)) (refl_equal K 
(Bind b)) H3 H11)) k H8))))))) H6)) H5))))))))))) (\lambda (c1: C).(\lambda 
(c0: C).(\lambda (H1: (csubc g c1 c0)).(\lambda (H2: (((eq C c0 (CHead c2 k 
w)) \to (or3 (ex2 C (\lambda (c3: C).(eq C c1 (CHead c3 k w))) (\lambda (c3: 
C).(csubc g c3 c2))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda 
(_: A).(eq K k (Bind Abbr))))) (\lambda (c3: C).(\lambda (v: T).(\lambda (_: 
A).(eq C c1 (CHead c3 (Bind Abst) v))))) (\lambda (c3: C).(\lambda (_: 
T).(\lambda (_: A).(csubc g c3 c2)))) (\lambda (c3: C).(\lambda (v: 
T).(\lambda (a: A).(sc3 g (asucc g a) c3 v)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(sc3 g a c2 w))))) (ex4_3 B C T (\lambda (_: B).(\lambda 
(c3: C).(\lambda (v1: T).(eq C c1 (CHead c3 (Bind Void) v1))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(eq K k (Bind b))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: 
B).(\lambda (c3: C).(\lambda (_: T).(csubc g c3 c2))))))))).(\lambda (v: 
T).(\lambda (a: A).(\lambda (H3: (sc3 g (asucc g a) c1 v)).(\lambda (w0: 
T).(\lambda (H4: (sc3 g a c0 w0)).(\lambda (H5: (eq C (CHead c0 (Bind Abbr) 
w0) (CHead c2 k w))).(let H6 \def (f_equal C C (\lambda (e: C).(match e in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | (CHead c _ _) 
\Rightarrow c])) (CHead c0 (Bind Abbr) w0) (CHead c2 k w) H5) in ((let H7 
\def (f_equal C K (\lambda (e: C).(match e in C return (\lambda (_: C).K) 
with [(CSort _) \Rightarrow (Bind Abbr) | (CHead _ k0 _) \Rightarrow k0])) 
(CHead c0 (Bind Abbr) w0) (CHead c2 k w) H5) in ((let H8 \def (f_equal C T 
(\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow w0 | (CHead _ _ t) \Rightarrow t])) (CHead c0 (Bind Abbr) w0) 
(CHead c2 k w) H5) in (\lambda (H9: (eq K (Bind Abbr) k)).(\lambda (H10: (eq 
C c0 c2)).(let H11 \def (eq_ind T w0 (\lambda (t: T).(sc3 g a c0 t)) H4 w H8) 
in (let H12 \def (eq_ind C c0 (\lambda (c: C).(sc3 g a c w)) H11 c2 H10) in 
(let H13 \def (eq_ind C c0 (\lambda (c: C).((eq C c (CHead c2 k w)) \to (or3 
(ex2 C (\lambda (c3: C).(eq C c1 (CHead c3 k w))) (\lambda (c3: C).(csubc g 
c3 c2))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k 
(Bind Abbr))))) (\lambda (c3: C).(\lambda (v0: T).(\lambda (_: A).(eq C c1 
(CHead c3 (Bind Abst) v0))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: 
A).(csubc g c3 c2)))) (\lambda (c3: C).(\lambda (v0: T).(\lambda (a0: A).(sc3 
g (asucc g a0) c3 v0)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a0: 
A).(sc3 g a0 c2 w))))) (ex4_3 B C T (\lambda (_: B).(\lambda (c3: C).(\lambda 
(v1: T).(eq C c1 (CHead c3 (Bind Void) v1))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(eq K k (Bind b))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g c3 c2)))))))) H2 c2 H10) in (let H14 \def (eq_ind 
C c0 (\lambda (c: C).(csubc g c1 c)) H1 c2 H10) in (let H15 \def (eq_ind_r K 
k (\lambda (k0: K).((eq C c2 (CHead c2 k0 w)) \to (or3 (ex2 C (\lambda (c3: 
C).(eq C c1 (CHead c3 k0 w))) (\lambda (c3: C).(csubc g c3 c2))) (ex5_3 C T A 
(\lambda (_: C).(\lambda (_: T).(\lambda (_: A).(eq K k0 (Bind Abbr))))) 
(\lambda (c3: C).(\lambda (v0: T).(\lambda (_: A).(eq C c1 (CHead c3 (Bind 
Abst) v0))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c3 
c2)))) (\lambda (c3: C).(\lambda (v0: T).(\lambda (a0: A).(sc3 g (asucc g a0) 
c3 v0)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(sc3 g a0 c2 
w))))) (ex4_3 B C T (\lambda (_: B).(\lambda (c3: C).(\lambda (v1: T).(eq C 
c1 (CHead c3 (Bind Void) v1))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: 
T).(eq K k0 (Bind b))))) (\lambda (b: B).(\lambda (_: C).(\lambda (_: T).(not 
(eq B b Void))))) (\lambda (_: B).(\lambda (c3: C).(\lambda (_: T).(csubc g 
c3 c2)))))))) H13 (Bind Abbr) H9) in (eq_ind K (Bind Abbr) (\lambda (k0: 
K).(or3 (ex2 C (\lambda (c3: C).(eq C (CHead c1 (Bind Abst) v) (CHead c3 k0 
w))) (\lambda (c3: C).(csubc g c3 c2))) (ex5_3 C T A (\lambda (_: C).(\lambda 
(_: T).(\lambda (_: A).(eq K k0 (Bind Abbr))))) (\lambda (c3: C).(\lambda 
(v0: T).(\lambda (_: A).(eq C (CHead c1 (Bind Abst) v) (CHead c3 (Bind Abst) 
v0))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c3 c2)))) 
(\lambda (c3: C).(\lambda (v0: T).(\lambda (a0: A).(sc3 g (asucc g a0) c3 
v0)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(sc3 g a0 c2 w))))) 
(ex4_3 B C T (\lambda (_: B).(\lambda (c3: C).(\lambda (v1: T).(eq C (CHead 
c1 (Bind Abst) v) (CHead c3 (Bind Void) v1))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(eq K k0 (Bind b))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g c3 c2))))))) (or3_intro1 (ex2 C (\lambda (c3: 
C).(eq C (CHead c1 (Bind Abst) v) (CHead c3 (Bind Abbr) w))) (\lambda (c3: 
C).(csubc g c3 c2))) (ex5_3 C T A (\lambda (_: C).(\lambda (_: T).(\lambda 
(_: A).(eq K (Bind Abbr) (Bind Abbr))))) (\lambda (c3: C).(\lambda (v0: 
T).(\lambda (_: A).(eq C (CHead c1 (Bind Abst) v) (CHead c3 (Bind Abst) 
v0))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: A).(csubc g c3 c2)))) 
(\lambda (c3: C).(\lambda (v0: T).(\lambda (a0: A).(sc3 g (asucc g a0) c3 
v0)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a0: A).(sc3 g a0 c2 w))))) 
(ex4_3 B C T (\lambda (_: B).(\lambda (c3: C).(\lambda (v1: T).(eq C (CHead 
c1 (Bind Abst) v) (CHead c3 (Bind Void) v1))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (_: T).(eq K (Bind Abbr) (Bind b))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (_: T).(not (eq B b Void))))) (\lambda (_: B).(\lambda (c3: 
C).(\lambda (_: T).(csubc g c3 c2))))) (ex5_3_intro C T A (\lambda (_: 
C).(\lambda (_: T).(\lambda (_: A).(eq K (Bind Abbr) (Bind Abbr))))) (\lambda 
(c3: C).(\lambda (v0: T).(\lambda (_: A).(eq C (CHead c1 (Bind Abst) v) 
(CHead c3 (Bind Abst) v0))))) (\lambda (c3: C).(\lambda (_: T).(\lambda (_: 
A).(csubc g c3 c2)))) (\lambda (c3: C).(\lambda (v0: T).(\lambda (a0: A).(sc3 
g (asucc g a0) c3 v0)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a0: 
A).(sc3 g a0 c2 w)))) c1 v a (refl_equal K (Bind Abbr)) (refl_equal C (CHead 
c1 (Bind Abst) v)) H14 H3 H12)) k H9))))))))) H7)) H6)))))))))))) x y H0))) 
H)))))).
(* COMMENTS
Initial nodes: 5197
END *)

