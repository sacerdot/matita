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

include "Basic-1/sty0/defs.ma".

theorem sty0_gen_sort:
 \forall (g: G).(\forall (c: C).(\forall (x: T).(\forall (n: nat).((sty0 g c 
(TSort n) x) \to (eq T x (TSort (next g n)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (x: T).(\lambda (n: nat).(\lambda 
(H: (sty0 g c (TSort n) x)).(insert_eq T (TSort n) (\lambda (t: T).(sty0 g c 
t x)) (\lambda (_: T).(eq T x (TSort (next g n)))) (\lambda (y: T).(\lambda 
(H0: (sty0 g c y x)).(sty0_ind g (\lambda (_: C).(\lambda (t: T).(\lambda 
(t0: T).((eq T t (TSort n)) \to (eq T t0 (TSort (next g n))))))) (\lambda (_: 
C).(\lambda (n0: nat).(\lambda (H1: (eq T (TSort n0) (TSort n))).(let H2 \def 
(f_equal T nat (\lambda (e: T).(match e in T return (\lambda (_: T).nat) with 
[(TSort n1) \Rightarrow n1 | (TLRef _) \Rightarrow n0 | (THead _ _ _) 
\Rightarrow n0])) (TSort n0) (TSort n) H1) in (eq_ind_r nat n (\lambda (n1: 
nat).(eq T (TSort (next g n1)) (TSort (next g n)))) (refl_equal T (TSort 
(next g n))) n0 H2))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (v: 
T).(\lambda (i: nat).(\lambda (_: (getl i c0 (CHead d (Bind Abbr) 
v))).(\lambda (w: T).(\lambda (_: (sty0 g d v w)).(\lambda (_: (((eq T v 
(TSort n)) \to (eq T w (TSort (next g n)))))).(\lambda (H4: (eq T (TLRef i) 
(TSort n))).(let H5 \def (eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (TSort n) H4) in 
(False_ind (eq T (lift (S i) O w) (TSort (next g n))) H5))))))))))) (\lambda 
(c0: C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: nat).(\lambda (_: (getl 
i c0 (CHead d (Bind Abst) v))).(\lambda (w: T).(\lambda (_: (sty0 g d v 
w)).(\lambda (_: (((eq T v (TSort n)) \to (eq T w (TSort (next g 
n)))))).(\lambda (H4: (eq T (TLRef i) (TSort n))).(let H5 \def (eq_ind T 
(TLRef i) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) 
\Rightarrow False])) I (TSort n) H4) in (False_ind (eq T (lift (S i) O v) 
(TSort (next g n))) H5))))))))))) (\lambda (b: B).(\lambda (c0: C).(\lambda 
(v: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (sty0 g (CHead c0 (Bind 
b) v) t1 t2)).(\lambda (_: (((eq T t1 (TSort n)) \to (eq T t2 (TSort (next g 
n)))))).(\lambda (H3: (eq T (THead (Bind b) v t1) (TSort n))).(let H4 \def 
(eq_ind T (THead (Bind b) v t1) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) H3) in 
(False_ind (eq T (THead (Bind b) v t2) (TSort (next g n))) H4)))))))))) 
(\lambda (c0: C).(\lambda (v: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(_: (sty0 g c0 t1 t2)).(\lambda (_: (((eq T t1 (TSort n)) \to (eq T t2 (TSort 
(next g n)))))).(\lambda (H3: (eq T (THead (Flat Appl) v t1) (TSort n))).(let 
H4 \def (eq_ind T (THead (Flat Appl) v t1) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) H3) in 
(False_ind (eq T (THead (Flat Appl) v t2) (TSort (next g n))) H4))))))))) 
(\lambda (c0: C).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (sty0 g c0 v1 
v2)).(\lambda (_: (((eq T v1 (TSort n)) \to (eq T v2 (TSort (next g 
n)))))).(\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (sty0 g c0 t1 
t2)).(\lambda (_: (((eq T t1 (TSort n)) \to (eq T t2 (TSort (next g 
n)))))).(\lambda (H5: (eq T (THead (Flat Cast) v1 t1) (TSort n))).(let H6 
\def (eq_ind T (THead (Flat Cast) v1 t1) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) H5) in 
(False_ind (eq T (THead (Flat Cast) v2 t2) (TSort (next g n))) H6)))))))))))) 
c y x H0))) H))))).
(* COMMENTS
Initial nodes: 869
END *)

theorem sty0_gen_lref:
 \forall (g: G).(\forall (c: C).(\forall (x: T).(\forall (n: nat).((sty0 g c 
(TLRef n) x) \to (or (ex3_3 C T T (\lambda (e: C).(\lambda (u: T).(\lambda 
(_: T).(getl n c (CHead e (Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(t: T).(eq T x (lift (S n) O t)))))) (ex3_3 C T T (\lambda (e: C).(\lambda 
(u: T).(\lambda (_: T).(getl n c (CHead e (Bind Abst) u))))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq T x (lift (S n) O u)))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (x: T).(\lambda (n: nat).(\lambda 
(H: (sty0 g c (TLRef n) x)).(insert_eq T (TLRef n) (\lambda (t: T).(sty0 g c 
t x)) (\lambda (_: T).(or (ex3_3 C T T (\lambda (e: C).(\lambda (u: 
T).(\lambda (_: T).(getl n c (CHead e (Bind Abbr) u))))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (t0: T).(sty0 g e u t0)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (t0: T).(eq T x (lift (S n) O t0)))))) (ex3_3 C T 
T (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c (CHead e (Bind 
Abst) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t0: T).(sty0 g e u 
t0)))) (\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq T x (lift (S n) O 
u)))))))) (\lambda (y: T).(\lambda (H0: (sty0 g c y x)).(sty0_ind g (\lambda 
(c0: C).(\lambda (t: T).(\lambda (t0: T).((eq T t (TLRef n)) \to (or (ex3_3 C 
T T (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c0 (CHead e (Bind 
Abbr) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t1: T).(sty0 g e u 
t1)))) (\lambda (_: C).(\lambda (_: T).(\lambda (t1: T).(eq T t0 (lift (S n) 
O t1)))))) (ex3_3 C T T (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl 
n c0 (CHead e (Bind Abst) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda 
(t1: T).(sty0 g e u t1)))) (\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq T t0 (lift (S n) O u))))))))))) (\lambda (c0: C).(\lambda (n0: 
nat).(\lambda (H1: (eq T (TSort n0) (TLRef n))).(let H2 \def (eq_ind T (TSort 
n0) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
False])) I (TLRef n) H1) in (False_ind (or (ex3_3 C T T (\lambda (e: 
C).(\lambda (u: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abbr) u))))) 
(\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u t)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (t: T).(eq T (TSort (next g n0)) (lift (S n) 
O t)))))) (ex3_3 C T T (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl 
n c0 (CHead e (Bind Abst) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: 
T).(sty0 g e u t)))) (\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq T 
(TSort (next g n0)) (lift (S n) O u))))))) H2))))) (\lambda (c0: C).(\lambda 
(d: C).(\lambda (v: T).(\lambda (i: nat).(\lambda (H1: (getl i c0 (CHead d 
(Bind Abbr) v))).(\lambda (w: T).(\lambda (H2: (sty0 g d v w)).(\lambda (_: 
(((eq T v (TLRef n)) \to (or (ex3_3 C T T (\lambda (e: C).(\lambda (u: 
T).(\lambda (_: T).(getl n d (CHead e (Bind Abbr) u))))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (t: T).(eq T w (lift (S n) O t)))))) (ex3_3 C T T (\lambda 
(e: C).(\lambda (u: T).(\lambda (_: T).(getl n d (CHead e (Bind Abst) u))))) 
(\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u t)))) (\lambda 
(_: C).(\lambda (u: T).(\lambda (_: T).(eq T w (lift (S n) O 
u)))))))))).(\lambda (H4: (eq T (TLRef i) (TLRef n))).(let H5 \def (f_equal T 
nat (\lambda (e: T).(match e in T return (\lambda (_: T).nat) with [(TSort _) 
\Rightarrow i | (TLRef n0) \Rightarrow n0 | (THead _ _ _) \Rightarrow i])) 
(TLRef i) (TLRef n) H4) in (let H6 \def (eq_ind nat i (\lambda (n0: 
nat).(getl n0 c0 (CHead d (Bind Abbr) v))) H1 n H5) in (eq_ind_r nat n 
(\lambda (n0: nat).(or (ex3_3 C T T (\lambda (e: C).(\lambda (u: T).(\lambda 
(_: T).(getl n c0 (CHead e (Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(t: T).(eq T (lift (S n0) O w) (lift (S n) O t)))))) (ex3_3 C T T (\lambda 
(e: C).(\lambda (u: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u))))) 
(\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u t)))) (\lambda 
(_: C).(\lambda (u: T).(\lambda (_: T).(eq T (lift (S n0) O w) (lift (S n) O 
u)))))))) (or_introl (ex3_3 C T T (\lambda (e: C).(\lambda (u: T).(\lambda 
(_: T).(getl n c0 (CHead e (Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(t: T).(eq T (lift (S n) O w) (lift (S n) O t)))))) (ex3_3 C T T (\lambda (e: 
C).(\lambda (u: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u))))) 
(\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u t)))) (\lambda 
(_: C).(\lambda (u: T).(\lambda (_: T).(eq T (lift (S n) O w) (lift (S n) O 
u)))))) (ex3_3_intro C T T (\lambda (e: C).(\lambda (u: T).(\lambda (_: 
T).(getl n c0 (CHead e (Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(t: T).(eq T (lift (S n) O w) (lift (S n) O t))))) d v w H6 H2 (refl_equal T 
(lift (S n) O w)))) i H5)))))))))))) (\lambda (c0: C).(\lambda (d: 
C).(\lambda (v: T).(\lambda (i: nat).(\lambda (H1: (getl i c0 (CHead d (Bind 
Abst) v))).(\lambda (w: T).(\lambda (H2: (sty0 g d v w)).(\lambda (_: (((eq T 
v (TLRef n)) \to (or (ex3_3 C T T (\lambda (e: C).(\lambda (u: T).(\lambda 
(_: T).(getl n d (CHead e (Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(t: T).(eq T w (lift (S n) O t)))))) (ex3_3 C T T (\lambda (e: C).(\lambda 
(u: T).(\lambda (_: T).(getl n d (CHead e (Bind Abst) u))))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq T w (lift (S n) O u)))))))))).(\lambda (H4: (eq T 
(TLRef i) (TLRef n))).(let H5 \def (f_equal T nat (\lambda (e: T).(match e in 
T return (\lambda (_: T).nat) with [(TSort _) \Rightarrow i | (TLRef n0) 
\Rightarrow n0 | (THead _ _ _) \Rightarrow i])) (TLRef i) (TLRef n) H4) in 
(let H6 \def (eq_ind nat i (\lambda (n0: nat).(getl n0 c0 (CHead d (Bind 
Abst) v))) H1 n H5) in (eq_ind_r nat n (\lambda (n0: nat).(or (ex3_3 C T T 
(\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c0 (CHead e (Bind 
Abbr) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u 
t)))) (\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(eq T (lift (S n0) O v) 
(lift (S n) O t)))))) (ex3_3 C T T (\lambda (e: C).(\lambda (u: T).(\lambda 
(_: T).(getl n c0 (CHead e (Bind Abst) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq T (lift (S n0) O v) (lift (S n) O u)))))))) (or_intror (ex3_3 C T 
T (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c0 (CHead e (Bind 
Abbr) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u 
t)))) (\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(eq T (lift (S n) O v) 
(lift (S n) O t)))))) (ex3_3 C T T (\lambda (e: C).(\lambda (u: T).(\lambda 
(_: T).(getl n c0 (CHead e (Bind Abst) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq T (lift (S n) O v) (lift (S n) O u)))))) (ex3_3_intro C T T 
(\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c0 (CHead e (Bind 
Abst) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u 
t)))) (\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq T (lift (S n) O v) 
(lift (S n) O u))))) d v w H6 H2 (refl_equal T (lift (S n) O v)))) i 
H5)))))))))))) (\lambda (b: B).(\lambda (c0: C).(\lambda (v: T).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (_: (sty0 g (CHead c0 (Bind b) v) t1 
t2)).(\lambda (_: (((eq T t1 (TLRef n)) \to (or (ex3_3 C T T (\lambda (e: 
C).(\lambda (u: T).(\lambda (_: T).(getl n (CHead c0 (Bind b) v) (CHead e 
(Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(sty0 g e 
u t)))) (\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(eq T t2 (lift (S n) 
O t)))))) (ex3_3 C T T (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl 
n (CHead c0 (Bind b) v) (CHead e (Bind Abst) u))))) (\lambda (e: C).(\lambda 
(u: T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq T t2 (lift (S n) O u)))))))))).(\lambda (H3: (eq T 
(THead (Bind b) v t1) (TLRef n))).(let H4 \def (eq_ind T (THead (Bind b) v 
t1) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) I (TLRef n) H3) in (False_ind (or (ex3_3 C T T (\lambda 
(e: C).(\lambda (u: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abbr) u))))) 
(\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u t)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (t: T).(eq T (THead (Bind b) v t2) (lift (S 
n) O t)))))) (ex3_3 C T T (\lambda (e: C).(\lambda (u: T).(\lambda (_: 
T).(getl n c0 (CHead e (Bind Abst) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq T (THead (Bind b) v t2) (lift (S n) O u))))))) H4)))))))))) 
(\lambda (c0: C).(\lambda (v: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(_: (sty0 g c0 t1 t2)).(\lambda (_: (((eq T t1 (TLRef n)) \to (or (ex3_3 C T 
T (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c0 (CHead e (Bind 
Abbr) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u 
t)))) (\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(eq T t2 (lift (S n) O 
t)))))) (ex3_3 C T T (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n 
c0 (CHead e (Bind Abst) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: 
T).(sty0 g e u t)))) (\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq T t2 
(lift (S n) O u)))))))))).(\lambda (H3: (eq T (THead (Flat Appl) v t1) (TLRef 
n))).(let H4 \def (eq_ind T (THead (Flat Appl) v t1) (\lambda (ee: T).(match 
ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n) 
H3) in (False_ind (or (ex3_3 C T T (\lambda (e: C).(\lambda (u: T).(\lambda 
(_: T).(getl n c0 (CHead e (Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(t: T).(eq T (THead (Flat Appl) v t2) (lift (S n) O t)))))) (ex3_3 C T T 
(\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c0 (CHead e (Bind 
Abst) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u 
t)))) (\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq T (THead (Flat 
Appl) v t2) (lift (S n) O u))))))) H4))))))))) (\lambda (c0: C).(\lambda (v1: 
T).(\lambda (v2: T).(\lambda (_: (sty0 g c0 v1 v2)).(\lambda (_: (((eq T v1 
(TLRef n)) \to (or (ex3_3 C T T (\lambda (e: C).(\lambda (u: T).(\lambda (_: 
T).(getl n c0 (CHead e (Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(t: T).(eq T v2 (lift (S n) O t)))))) (ex3_3 C T T (\lambda (e: C).(\lambda 
(u: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u))))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq T v2 (lift (S n) O u)))))))))).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (_: (sty0 g c0 t1 t2)).(\lambda (_: (((eq T t1 
(TLRef n)) \to (or (ex3_3 C T T (\lambda (e: C).(\lambda (u: T).(\lambda (_: 
T).(getl n c0 (CHead e (Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(t: T).(eq T t2 (lift (S n) O t)))))) (ex3_3 C T T (\lambda (e: C).(\lambda 
(u: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u))))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq T t2 (lift (S n) O u)))))))))).(\lambda (H5: (eq T 
(THead (Flat Cast) v1 t1) (TLRef n))).(let H6 \def (eq_ind T (THead (Flat 
Cast) v1 t1) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ 
_) \Rightarrow True])) I (TLRef n) H5) in (False_ind (or (ex3_3 C T T 
(\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c0 (CHead e (Bind 
Abbr) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u 
t)))) (\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(eq T (THead (Flat 
Cast) v2 t2) (lift (S n) O t)))))) (ex3_3 C T T (\lambda (e: C).(\lambda (u: 
T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u))))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (t: T).(sty0 g e u t)))) (\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq T (THead (Flat Cast) v2 t2) (lift (S n) O u))))))) 
H6)))))))))))) c y x H0))) H))))).
(* COMMENTS
Initial nodes: 3231
END *)

theorem sty0_gen_bind:
 \forall (g: G).(\forall (b: B).(\forall (c: C).(\forall (u: T).(\forall (t1: 
T).(\forall (x: T).((sty0 g c (THead (Bind b) u t1) x) \to (ex2 T (\lambda 
(t2: T).(sty0 g (CHead c (Bind b) u) t1 t2)) (\lambda (t2: T).(eq T x (THead 
(Bind b) u t2))))))))))
\def
 \lambda (g: G).(\lambda (b: B).(\lambda (c: C).(\lambda (u: T).(\lambda (t1: 
T).(\lambda (x: T).(\lambda (H: (sty0 g c (THead (Bind b) u t1) 
x)).(insert_eq T (THead (Bind b) u t1) (\lambda (t: T).(sty0 g c t x)) 
(\lambda (_: T).(ex2 T (\lambda (t2: T).(sty0 g (CHead c (Bind b) u) t1 t2)) 
(\lambda (t2: T).(eq T x (THead (Bind b) u t2))))) (\lambda (y: T).(\lambda 
(H0: (sty0 g c y x)).(sty0_ind g (\lambda (c0: C).(\lambda (t: T).(\lambda 
(t0: T).((eq T t (THead (Bind b) u t1)) \to (ex2 T (\lambda (t2: T).(sty0 g 
(CHead c0 (Bind b) u) t1 t2)) (\lambda (t2: T).(eq T t0 (THead (Bind b) u 
t2)))))))) (\lambda (c0: C).(\lambda (n: nat).(\lambda (H1: (eq T (TSort n) 
(THead (Bind b) u t1))).(let H2 \def (eq_ind T (TSort n) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow False])) I 
(THead (Bind b) u t1) H1) in (False_ind (ex2 T (\lambda (t2: T).(sty0 g 
(CHead c0 (Bind b) u) t1 t2)) (\lambda (t2: T).(eq T (TSort (next g n)) 
(THead (Bind b) u t2)))) H2))))) (\lambda (c0: C).(\lambda (d: C).(\lambda 
(v: T).(\lambda (i: nat).(\lambda (_: (getl i c0 (CHead d (Bind Abbr) 
v))).(\lambda (w: T).(\lambda (_: (sty0 g d v w)).(\lambda (_: (((eq T v 
(THead (Bind b) u t1)) \to (ex2 T (\lambda (t2: T).(sty0 g (CHead d (Bind b) 
u) t1 t2)) (\lambda (t2: T).(eq T w (THead (Bind b) u t2))))))).(\lambda (H4: 
(eq T (TLRef i) (THead (Bind b) u t1))).(let H5 \def (eq_ind T (TLRef i) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow 
False])) I (THead (Bind b) u t1) H4) in (False_ind (ex2 T (\lambda (t2: 
T).(sty0 g (CHead c0 (Bind b) u) t1 t2)) (\lambda (t2: T).(eq T (lift (S i) O 
w) (THead (Bind b) u t2)))) H5))))))))))) (\lambda (c0: C).(\lambda (d: 
C).(\lambda (v: T).(\lambda (i: nat).(\lambda (_: (getl i c0 (CHead d (Bind 
Abst) v))).(\lambda (w: T).(\lambda (_: (sty0 g d v w)).(\lambda (_: (((eq T 
v (THead (Bind b) u t1)) \to (ex2 T (\lambda (t2: T).(sty0 g (CHead d (Bind 
b) u) t1 t2)) (\lambda (t2: T).(eq T w (THead (Bind b) u t2))))))).(\lambda 
(H4: (eq T (TLRef i) (THead (Bind b) u t1))).(let H5 \def (eq_ind T (TLRef i) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow 
False])) I (THead (Bind b) u t1) H4) in (False_ind (ex2 T (\lambda (t2: 
T).(sty0 g (CHead c0 (Bind b) u) t1 t2)) (\lambda (t2: T).(eq T (lift (S i) O 
v) (THead (Bind b) u t2)))) H5))))))))))) (\lambda (b0: B).(\lambda (c0: 
C).(\lambda (v: T).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H1: (sty0 g 
(CHead c0 (Bind b0) v) t0 t2)).(\lambda (H2: (((eq T t0 (THead (Bind b) u 
t1)) \to (ex2 T (\lambda (t3: T).(sty0 g (CHead (CHead c0 (Bind b0) v) (Bind 
b) u) t1 t3)) (\lambda (t3: T).(eq T t2 (THead (Bind b) u t3))))))).(\lambda 
(H3: (eq T (THead (Bind b0) v t0) (THead (Bind b) u t1))).(let H4 \def 
(f_equal T B (\lambda (e: T).(match e in T return (\lambda (_: T).B) with 
[(TSort _) \Rightarrow b0 | (TLRef _) \Rightarrow b0 | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b1) 
\Rightarrow b1 | (Flat _) \Rightarrow b0])])) (THead (Bind b0) v t0) (THead 
(Bind b) u t1) H3) in ((let H5 \def (f_equal T T (\lambda (e: T).(match e in 
T return (\lambda (_: T).T) with [(TSort _) \Rightarrow v | (TLRef _) 
\Rightarrow v | (THead _ t _) \Rightarrow t])) (THead (Bind b0) v t0) (THead 
(Bind b) u t1) H3) in ((let H6 \def (f_equal T T (\lambda (e: T).(match e in 
T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | (TLRef _) 
\Rightarrow t0 | (THead _ _ t) \Rightarrow t])) (THead (Bind b0) v t0) (THead 
(Bind b) u t1) H3) in (\lambda (H7: (eq T v u)).(\lambda (H8: (eq B b0 
b)).(let H9 \def (eq_ind T t0 (\lambda (t: T).((eq T t (THead (Bind b) u t1)) 
\to (ex2 T (\lambda (t3: T).(sty0 g (CHead (CHead c0 (Bind b0) v) (Bind b) u) 
t1 t3)) (\lambda (t3: T).(eq T t2 (THead (Bind b) u t3)))))) H2 t1 H6) in 
(let H10 \def (eq_ind T t0 (\lambda (t: T).(sty0 g (CHead c0 (Bind b0) v) t 
t2)) H1 t1 H6) in (let H11 \def (eq_ind T v (\lambda (t: T).((eq T t1 (THead 
(Bind b) u t1)) \to (ex2 T (\lambda (t3: T).(sty0 g (CHead (CHead c0 (Bind 
b0) t) (Bind b) u) t1 t3)) (\lambda (t3: T).(eq T t2 (THead (Bind b) u 
t3)))))) H9 u H7) in (let H12 \def (eq_ind T v (\lambda (t: T).(sty0 g (CHead 
c0 (Bind b0) t) t1 t2)) H10 u H7) in (eq_ind_r T u (\lambda (t: T).(ex2 T 
(\lambda (t3: T).(sty0 g (CHead c0 (Bind b) u) t1 t3)) (\lambda (t3: T).(eq T 
(THead (Bind b0) t t2) (THead (Bind b) u t3))))) (let H13 \def (eq_ind B b0 
(\lambda (b1: B).((eq T t1 (THead (Bind b) u t1)) \to (ex2 T (\lambda (t3: 
T).(sty0 g (CHead (CHead c0 (Bind b1) u) (Bind b) u) t1 t3)) (\lambda (t3: 
T).(eq T t2 (THead (Bind b) u t3)))))) H11 b H8) in (let H14 \def (eq_ind B 
b0 (\lambda (b1: B).(sty0 g (CHead c0 (Bind b1) u) t1 t2)) H12 b H8) in 
(eq_ind_r B b (\lambda (b1: B).(ex2 T (\lambda (t3: T).(sty0 g (CHead c0 
(Bind b) u) t1 t3)) (\lambda (t3: T).(eq T (THead (Bind b1) u t2) (THead 
(Bind b) u t3))))) (ex_intro2 T (\lambda (t3: T).(sty0 g (CHead c0 (Bind b) 
u) t1 t3)) (\lambda (t3: T).(eq T (THead (Bind b) u t2) (THead (Bind b) u 
t3))) t2 H14 (refl_equal T (THead (Bind b) u t2))) b0 H8))) v H7)))))))) H5)) 
H4)))))))))) (\lambda (c0: C).(\lambda (v: T).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (_: (sty0 g c0 t0 t2)).(\lambda (_: (((eq T t0 (THead (Bind b) u 
t1)) \to (ex2 T (\lambda (t3: T).(sty0 g (CHead c0 (Bind b) u) t1 t3)) 
(\lambda (t3: T).(eq T t2 (THead (Bind b) u t3))))))).(\lambda (H3: (eq T 
(THead (Flat Appl) v t0) (THead (Bind b) u t1))).(let H4 \def (eq_ind T 
(THead (Flat Appl) v t0) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind 
b) u t1) H3) in (False_ind (ex2 T (\lambda (t3: T).(sty0 g (CHead c0 (Bind b) 
u) t1 t3)) (\lambda (t3: T).(eq T (THead (Flat Appl) v t2) (THead (Bind b) u 
t3)))) H4))))))))) (\lambda (c0: C).(\lambda (v1: T).(\lambda (v2: 
T).(\lambda (_: (sty0 g c0 v1 v2)).(\lambda (_: (((eq T v1 (THead (Bind b) u 
t1)) \to (ex2 T (\lambda (t2: T).(sty0 g (CHead c0 (Bind b) u) t1 t2)) 
(\lambda (t2: T).(eq T v2 (THead (Bind b) u t2))))))).(\lambda (t0: 
T).(\lambda (t2: T).(\lambda (_: (sty0 g c0 t0 t2)).(\lambda (_: (((eq T t0 
(THead (Bind b) u t1)) \to (ex2 T (\lambda (t3: T).(sty0 g (CHead c0 (Bind b) 
u) t1 t3)) (\lambda (t3: T).(eq T t2 (THead (Bind b) u t3))))))).(\lambda 
(H5: (eq T (THead (Flat Cast) v1 t0) (THead (Bind b) u t1))).(let H6 \def 
(eq_ind T (THead (Flat Cast) v1 t0) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind b) u t1) H5) in (False_ind (ex2 T (\lambda (t3: 
T).(sty0 g (CHead c0 (Bind b) u) t1 t3)) (\lambda (t3: T).(eq T (THead (Flat 
Cast) v2 t2) (THead (Bind b) u t3)))) H6)))))))))))) c y x H0))) H))))))).
(* COMMENTS
Initial nodes: 1975
END *)

theorem sty0_gen_appl:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall (x: 
T).((sty0 g c (THead (Flat Appl) u t1) x) \to (ex2 T (\lambda (t2: T).(sty0 g 
c t1 t2)) (\lambda (t2: T).(eq T x (THead (Flat Appl) u t2)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda (x: 
T).(\lambda (H: (sty0 g c (THead (Flat Appl) u t1) x)).(insert_eq T (THead 
(Flat Appl) u t1) (\lambda (t: T).(sty0 g c t x)) (\lambda (_: T).(ex2 T 
(\lambda (t2: T).(sty0 g c t1 t2)) (\lambda (t2: T).(eq T x (THead (Flat 
Appl) u t2))))) (\lambda (y: T).(\lambda (H0: (sty0 g c y x)).(sty0_ind g 
(\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).((eq T t (THead (Flat Appl) 
u t1)) \to (ex2 T (\lambda (t2: T).(sty0 g c0 t1 t2)) (\lambda (t2: T).(eq T 
t0 (THead (Flat Appl) u t2)))))))) (\lambda (c0: C).(\lambda (n: 
nat).(\lambda (H1: (eq T (TSort n) (THead (Flat Appl) u t1))).(let H2 \def 
(eq_ind T (TSort n) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (THead (Flat Appl) u t1) H1) in 
(False_ind (ex2 T (\lambda (t2: T).(sty0 g c0 t1 t2)) (\lambda (t2: T).(eq T 
(TSort (next g n)) (THead (Flat Appl) u t2)))) H2))))) (\lambda (c0: 
C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: nat).(\lambda (_: (getl i c0 
(CHead d (Bind Abbr) v))).(\lambda (w: T).(\lambda (_: (sty0 g d v 
w)).(\lambda (_: (((eq T v (THead (Flat Appl) u t1)) \to (ex2 T (\lambda (t2: 
T).(sty0 g d t1 t2)) (\lambda (t2: T).(eq T w (THead (Flat Appl) u 
t2))))))).(\lambda (H4: (eq T (TLRef i) (THead (Flat Appl) u t1))).(let H5 
\def (eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (THead (Flat Appl) u t1) H4) in 
(False_ind (ex2 T (\lambda (t2: T).(sty0 g c0 t1 t2)) (\lambda (t2: T).(eq T 
(lift (S i) O w) (THead (Flat Appl) u t2)))) H5))))))))))) (\lambda (c0: 
C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: nat).(\lambda (_: (getl i c0 
(CHead d (Bind Abst) v))).(\lambda (w: T).(\lambda (_: (sty0 g d v 
w)).(\lambda (_: (((eq T v (THead (Flat Appl) u t1)) \to (ex2 T (\lambda (t2: 
T).(sty0 g d t1 t2)) (\lambda (t2: T).(eq T w (THead (Flat Appl) u 
t2))))))).(\lambda (H4: (eq T (TLRef i) (THead (Flat Appl) u t1))).(let H5 
\def (eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (THead (Flat Appl) u t1) H4) in 
(False_ind (ex2 T (\lambda (t2: T).(sty0 g c0 t1 t2)) (\lambda (t2: T).(eq T 
(lift (S i) O v) (THead (Flat Appl) u t2)))) H5))))))))))) (\lambda (b: 
B).(\lambda (c0: C).(\lambda (v: T).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (_: (sty0 g (CHead c0 (Bind b) v) t0 t2)).(\lambda (_: (((eq T t0 
(THead (Flat Appl) u t1)) \to (ex2 T (\lambda (t3: T).(sty0 g (CHead c0 (Bind 
b) v) t1 t3)) (\lambda (t3: T).(eq T t2 (THead (Flat Appl) u 
t3))))))).(\lambda (H3: (eq T (THead (Bind b) v t0) (THead (Flat Appl) u 
t1))).(let H4 \def (eq_ind T (THead (Bind b) v t0) (\lambda (ee: T).(match ee 
in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef 
_) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow 
False])])) I (THead (Flat Appl) u t1) H3) in (False_ind (ex2 T (\lambda (t3: 
T).(sty0 g c0 t1 t3)) (\lambda (t3: T).(eq T (THead (Bind b) v t2) (THead 
(Flat Appl) u t3)))) H4)))))))))) (\lambda (c0: C).(\lambda (v: T).(\lambda 
(t0: T).(\lambda (t2: T).(\lambda (H1: (sty0 g c0 t0 t2)).(\lambda (H2: (((eq 
T t0 (THead (Flat Appl) u t1)) \to (ex2 T (\lambda (t3: T).(sty0 g c0 t1 t3)) 
(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u t3))))))).(\lambda (H3: (eq T 
(THead (Flat Appl) v t0) (THead (Flat Appl) u t1))).(let H4 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow v | (TLRef _) \Rightarrow v | (THead _ t _) \Rightarrow t])) 
(THead (Flat Appl) v t0) (THead (Flat Appl) u t1) H3) in ((let H5 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t) 
\Rightarrow t])) (THead (Flat Appl) v t0) (THead (Flat Appl) u t1) H3) in 
(\lambda (H6: (eq T v u)).(let H7 \def (eq_ind T t0 (\lambda (t: T).((eq T t 
(THead (Flat Appl) u t1)) \to (ex2 T (\lambda (t3: T).(sty0 g c0 t1 t3)) 
(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u t3)))))) H2 t1 H5) in (let H8 
\def (eq_ind T t0 (\lambda (t: T).(sty0 g c0 t t2)) H1 t1 H5) in (eq_ind_r T 
u (\lambda (t: T).(ex2 T (\lambda (t3: T).(sty0 g c0 t1 t3)) (\lambda (t3: 
T).(eq T (THead (Flat Appl) t t2) (THead (Flat Appl) u t3))))) (ex_intro2 T 
(\lambda (t3: T).(sty0 g c0 t1 t3)) (\lambda (t3: T).(eq T (THead (Flat Appl) 
u t2) (THead (Flat Appl) u t3))) t2 H8 (refl_equal T (THead (Flat Appl) u 
t2))) v H6))))) H4))))))))) (\lambda (c0: C).(\lambda (v1: T).(\lambda (v2: 
T).(\lambda (_: (sty0 g c0 v1 v2)).(\lambda (_: (((eq T v1 (THead (Flat Appl) 
u t1)) \to (ex2 T (\lambda (t2: T).(sty0 g c0 t1 t2)) (\lambda (t2: T).(eq T 
v2 (THead (Flat Appl) u t2))))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda 
(_: (sty0 g c0 t0 t2)).(\lambda (_: (((eq T t0 (THead (Flat Appl) u t1)) \to 
(ex2 T (\lambda (t3: T).(sty0 g c0 t1 t3)) (\lambda (t3: T).(eq T t2 (THead 
(Flat Appl) u t3))))))).(\lambda (H5: (eq T (THead (Flat Cast) v1 t0) (THead 
(Flat Appl) u t1))).(let H6 \def (eq_ind T (THead (Flat Cast) v1 t0) (\lambda 
(ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | 
(Flat f) \Rightarrow (match f in F return (\lambda (_: F).Prop) with [Appl 
\Rightarrow False | Cast \Rightarrow True])])])) I (THead (Flat Appl) u t1) 
H5) in (False_ind (ex2 T (\lambda (t3: T).(sty0 g c0 t1 t3)) (\lambda (t3: 
T).(eq T (THead (Flat Cast) v2 t2) (THead (Flat Appl) u t3)))) H6)))))))))))) 
c y x H0))) H)))))).
(* COMMENTS
Initial nodes: 1489
END *)

theorem sty0_gen_cast:
 \forall (g: G).(\forall (c: C).(\forall (v1: T).(\forall (t1: T).(\forall 
(x: T).((sty0 g c (THead (Flat Cast) v1 t1) x) \to (ex3_2 T T (\lambda (v2: 
T).(\lambda (_: T).(sty0 g c v1 v2))) (\lambda (_: T).(\lambda (t2: T).(sty0 
g c t1 t2))) (\lambda (v2: T).(\lambda (t2: T).(eq T x (THead (Flat Cast) v2 
t2))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (v1: T).(\lambda (t1: T).(\lambda 
(x: T).(\lambda (H: (sty0 g c (THead (Flat Cast) v1 t1) x)).(insert_eq T 
(THead (Flat Cast) v1 t1) (\lambda (t: T).(sty0 g c t x)) (\lambda (_: 
T).(ex3_2 T T (\lambda (v2: T).(\lambda (_: T).(sty0 g c v1 v2))) (\lambda 
(_: T).(\lambda (t2: T).(sty0 g c t1 t2))) (\lambda (v2: T).(\lambda (t2: 
T).(eq T x (THead (Flat Cast) v2 t2)))))) (\lambda (y: T).(\lambda (H0: (sty0 
g c y x)).(sty0_ind g (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).((eq 
T t (THead (Flat Cast) v1 t1)) \to (ex3_2 T T (\lambda (v2: T).(\lambda (_: 
T).(sty0 g c0 v1 v2))) (\lambda (_: T).(\lambda (t2: T).(sty0 g c0 t1 t2))) 
(\lambda (v2: T).(\lambda (t2: T).(eq T t0 (THead (Flat Cast) v2 t2))))))))) 
(\lambda (c0: C).(\lambda (n: nat).(\lambda (H1: (eq T (TSort n) (THead (Flat 
Cast) v1 t1))).(let H2 \def (eq_ind T (TSort n) (\lambda (ee: T).(match ee in 
T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow False])) I (THead (Flat Cast) 
v1 t1) H1) in (False_ind (ex3_2 T T (\lambda (v2: T).(\lambda (_: T).(sty0 g 
c0 v1 v2))) (\lambda (_: T).(\lambda (t2: T).(sty0 g c0 t1 t2))) (\lambda 
(v2: T).(\lambda (t2: T).(eq T (TSort (next g n)) (THead (Flat Cast) v2 
t2))))) H2))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: 
nat).(\lambda (_: (getl i c0 (CHead d (Bind Abbr) v))).(\lambda (w: 
T).(\lambda (_: (sty0 g d v w)).(\lambda (_: (((eq T v (THead (Flat Cast) v1 
t1)) \to (ex3_2 T T (\lambda (v2: T).(\lambda (_: T).(sty0 g d v1 v2))) 
(\lambda (_: T).(\lambda (t2: T).(sty0 g d t1 t2))) (\lambda (v2: T).(\lambda 
(t2: T).(eq T w (THead (Flat Cast) v2 t2)))))))).(\lambda (H4: (eq T (TLRef 
i) (THead (Flat Cast) v1 t1))).(let H5 \def (eq_ind T (TLRef i) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) I 
(THead (Flat Cast) v1 t1) H4) in (False_ind (ex3_2 T T (\lambda (v2: 
T).(\lambda (_: T).(sty0 g c0 v1 v2))) (\lambda (_: T).(\lambda (t2: T).(sty0 
g c0 t1 t2))) (\lambda (v2: T).(\lambda (t2: T).(eq T (lift (S i) O w) (THead 
(Flat Cast) v2 t2))))) H5))))))))))) (\lambda (c0: C).(\lambda (d: 
C).(\lambda (v: T).(\lambda (i: nat).(\lambda (_: (getl i c0 (CHead d (Bind 
Abst) v))).(\lambda (w: T).(\lambda (_: (sty0 g d v w)).(\lambda (_: (((eq T 
v (THead (Flat Cast) v1 t1)) \to (ex3_2 T T (\lambda (v2: T).(\lambda (_: 
T).(sty0 g d v1 v2))) (\lambda (_: T).(\lambda (t2: T).(sty0 g d t1 t2))) 
(\lambda (v2: T).(\lambda (t2: T).(eq T w (THead (Flat Cast) v2 
t2)))))))).(\lambda (H4: (eq T (TLRef i) (THead (Flat Cast) v1 t1))).(let H5 
\def (eq_ind T (TLRef i) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (THead (Flat Cast) v1 t1) H4) in 
(False_ind (ex3_2 T T (\lambda (v2: T).(\lambda (_: T).(sty0 g c0 v1 v2))) 
(\lambda (_: T).(\lambda (t2: T).(sty0 g c0 t1 t2))) (\lambda (v2: 
T).(\lambda (t2: T).(eq T (lift (S i) O v) (THead (Flat Cast) v2 t2))))) 
H5))))))))))) (\lambda (b: B).(\lambda (c0: C).(\lambda (v: T).(\lambda (t0: 
T).(\lambda (t2: T).(\lambda (_: (sty0 g (CHead c0 (Bind b) v) t0 
t2)).(\lambda (_: (((eq T t0 (THead (Flat Cast) v1 t1)) \to (ex3_2 T T 
(\lambda (v2: T).(\lambda (_: T).(sty0 g (CHead c0 (Bind b) v) v1 v2))) 
(\lambda (_: T).(\lambda (t3: T).(sty0 g (CHead c0 (Bind b) v) t1 t3))) 
(\lambda (v2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) v2 
t3)))))))).(\lambda (H3: (eq T (THead (Bind b) v t0) (THead (Flat Cast) v1 
t1))).(let H4 \def (eq_ind T (THead (Bind b) v t0) (\lambda (ee: T).(match ee 
in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef 
_) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow 
False])])) I (THead (Flat Cast) v1 t1) H3) in (False_ind (ex3_2 T T (\lambda 
(v2: T).(\lambda (_: T).(sty0 g c0 v1 v2))) (\lambda (_: T).(\lambda (t3: 
T).(sty0 g c0 t1 t3))) (\lambda (v2: T).(\lambda (t3: T).(eq T (THead (Bind 
b) v t2) (THead (Flat Cast) v2 t3))))) H4)))))))))) (\lambda (c0: C).(\lambda 
(v: T).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (sty0 g c0 t0 
t2)).(\lambda (_: (((eq T t0 (THead (Flat Cast) v1 t1)) \to (ex3_2 T T 
(\lambda (v2: T).(\lambda (_: T).(sty0 g c0 v1 v2))) (\lambda (_: T).(\lambda 
(t3: T).(sty0 g c0 t1 t3))) (\lambda (v2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Cast) v2 t3)))))))).(\lambda (H3: (eq T (THead (Flat Appl) v t0) (THead 
(Flat Cast) v1 t1))).(let H4 \def (eq_ind T (THead (Flat Appl) v t0) (\lambda 
(ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | 
(Flat f) \Rightarrow (match f in F return (\lambda (_: F).Prop) with [Appl 
\Rightarrow True | Cast \Rightarrow False])])])) I (THead (Flat Cast) v1 t1) 
H3) in (False_ind (ex3_2 T T (\lambda (v2: T).(\lambda (_: T).(sty0 g c0 v1 
v2))) (\lambda (_: T).(\lambda (t3: T).(sty0 g c0 t1 t3))) (\lambda (v2: 
T).(\lambda (t3: T).(eq T (THead (Flat Appl) v t2) (THead (Flat Cast) v2 
t3))))) H4))))))))) (\lambda (c0: C).(\lambda (v0: T).(\lambda (v2: 
T).(\lambda (H1: (sty0 g c0 v0 v2)).(\lambda (H2: (((eq T v0 (THead (Flat 
Cast) v1 t1)) \to (ex3_2 T T (\lambda (v3: T).(\lambda (_: T).(sty0 g c0 v1 
v3))) (\lambda (_: T).(\lambda (t2: T).(sty0 g c0 t1 t2))) (\lambda (v3: 
T).(\lambda (t2: T).(eq T v2 (THead (Flat Cast) v3 t2)))))))).(\lambda (t0: 
T).(\lambda (t2: T).(\lambda (H3: (sty0 g c0 t0 t2)).(\lambda (H4: (((eq T t0 
(THead (Flat Cast) v1 t1)) \to (ex3_2 T T (\lambda (v3: T).(\lambda (_: 
T).(sty0 g c0 v1 v3))) (\lambda (_: T).(\lambda (t3: T).(sty0 g c0 t1 t3))) 
(\lambda (v3: T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) v3 
t3)))))))).(\lambda (H5: (eq T (THead (Flat Cast) v0 t0) (THead (Flat Cast) 
v1 t1))).(let H6 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow v0 | (TLRef _) \Rightarrow v0 
| (THead _ t _) \Rightarrow t])) (THead (Flat Cast) v0 t0) (THead (Flat Cast) 
v1 t1) H5) in ((let H7 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 
| (THead _ _ t) \Rightarrow t])) (THead (Flat Cast) v0 t0) (THead (Flat Cast) 
v1 t1) H5) in (\lambda (H8: (eq T v0 v1)).(let H9 \def (eq_ind T t0 (\lambda 
(t: T).((eq T t (THead (Flat Cast) v1 t1)) \to (ex3_2 T T (\lambda (v3: 
T).(\lambda (_: T).(sty0 g c0 v1 v3))) (\lambda (_: T).(\lambda (t3: T).(sty0 
g c0 t1 t3))) (\lambda (v3: T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) 
v3 t3))))))) H4 t1 H7) in (let H10 \def (eq_ind T t0 (\lambda (t: T).(sty0 g 
c0 t t2)) H3 t1 H7) in (let H11 \def (eq_ind T v0 (\lambda (t: T).((eq T t 
(THead (Flat Cast) v1 t1)) \to (ex3_2 T T (\lambda (v3: T).(\lambda (_: 
T).(sty0 g c0 v1 v3))) (\lambda (_: T).(\lambda (t3: T).(sty0 g c0 t1 t3))) 
(\lambda (v3: T).(\lambda (t3: T).(eq T v2 (THead (Flat Cast) v3 t3))))))) H2 
v1 H8) in (let H12 \def (eq_ind T v0 (\lambda (t: T).(sty0 g c0 t v2)) H1 v1 
H8) in (ex3_2_intro T T (\lambda (v3: T).(\lambda (_: T).(sty0 g c0 v1 v3))) 
(\lambda (_: T).(\lambda (t3: T).(sty0 g c0 t1 t3))) (\lambda (v3: 
T).(\lambda (t3: T).(eq T (THead (Flat Cast) v2 t2) (THead (Flat Cast) v3 
t3)))) v2 t2 H12 H10 (refl_equal T (THead (Flat Cast) v2 t2))))))))) 
H6)))))))))))) c y x H0))) H)))))).
(* COMMENTS
Initial nodes: 1855
END *)

