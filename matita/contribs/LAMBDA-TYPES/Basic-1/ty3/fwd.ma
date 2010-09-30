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

include "Basic-1/ty3/defs.ma".

include "Basic-1/pc3/props.ma".

theorem ty3_gen_sort:
 \forall (g: G).(\forall (c: C).(\forall (x: T).(\forall (n: nat).((ty3 g c 
(TSort n) x) \to (pc3 c (TSort (next g n)) x)))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (x: T).(\lambda (n: nat).(\lambda 
(H: (ty3 g c (TSort n) x)).(insert_eq T (TSort n) (\lambda (t: T).(ty3 g c t 
x)) (\lambda (_: T).(pc3 c (TSort (next g n)) x)) (\lambda (y: T).(\lambda 
(H0: (ty3 g c y x)).(ty3_ind g (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: 
T).((eq T t (TSort n)) \to (pc3 c0 (TSort (next g n)) t0))))) (\lambda (c0: 
C).(\lambda (t2: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 t2 t)).(\lambda 
(_: (((eq T t2 (TSort n)) \to (pc3 c0 (TSort (next g n)) t)))).(\lambda (u: 
T).(\lambda (t1: T).(\lambda (H3: (ty3 g c0 u t1)).(\lambda (H4: (((eq T u 
(TSort n)) \to (pc3 c0 (TSort (next g n)) t1)))).(\lambda (H5: (pc3 c0 t1 
t2)).(\lambda (H6: (eq T u (TSort n))).(let H7 \def (f_equal T T (\lambda (e: 
T).e) u (TSort n) H6) in (let H8 \def (eq_ind T u (\lambda (t0: T).((eq T t0 
(TSort n)) \to (pc3 c0 (TSort (next g n)) t1))) H4 (TSort n) H7) in (let H9 
\def (eq_ind T u (\lambda (t0: T).(ty3 g c0 t0 t1)) H3 (TSort n) H7) in 
(pc3_t t1 c0 (TSort (next g n)) (H8 (refl_equal T (TSort n))) t2 
H5))))))))))))))) (\lambda (c0: C).(\lambda (m: nat).(\lambda (H1: (eq T 
(TSort m) (TSort n))).(let H2 \def (f_equal T nat (\lambda (e: T).(match e in 
T return (\lambda (_: T).nat) with [(TSort n0) \Rightarrow n0 | (TLRef _) 
\Rightarrow m | (THead _ _ _) \Rightarrow m])) (TSort m) (TSort n) H1) in 
(eq_ind_r nat n (\lambda (n0: nat).(pc3 c0 (TSort (next g n)) (TSort (next g 
n0)))) (pc3_refl c0 (TSort (next g n))) m H2))))) (\lambda (n0: nat).(\lambda 
(c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (_: (getl n0 c0 (CHead d 
(Bind Abbr) u))).(\lambda (t: T).(\lambda (_: (ty3 g d u t)).(\lambda (_: 
(((eq T u (TSort n)) \to (pc3 d (TSort (next g n)) t)))).(\lambda (H4: (eq T 
(TLRef n0) (TSort n))).(let H5 \def (eq_ind T (TLRef n0) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) I 
(TSort n) H4) in (False_ind (pc3 c0 (TSort (next g n)) (lift (S n0) O t)) 
H5))))))))))) (\lambda (n0: nat).(\lambda (c0: C).(\lambda (d: C).(\lambda 
(u: T).(\lambda (_: (getl n0 c0 (CHead d (Bind Abst) u))).(\lambda (t: 
T).(\lambda (_: (ty3 g d u t)).(\lambda (_: (((eq T u (TSort n)) \to (pc3 d 
(TSort (next g n)) t)))).(\lambda (H4: (eq T (TLRef n0) (TSort n))).(let H5 
\def (eq_ind T (TLRef n0) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (TSort n) H4) in (False_ind (pc3 c0 
(TSort (next g n)) (lift (S n0) O u)) H5))))))))))) (\lambda (c0: C).(\lambda 
(u: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 u t)).(\lambda (_: (((eq T u 
(TSort n)) \to (pc3 c0 (TSort (next g n)) t)))).(\lambda (b: B).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (_: (ty3 g (CHead c0 (Bind b) u) t1 
t2)).(\lambda (_: (((eq T t1 (TSort n)) \to (pc3 (CHead c0 (Bind b) u) (TSort 
(next g n)) t2)))).(\lambda (H5: (eq T (THead (Bind b) u t1) (TSort n))).(let 
H6 \def (eq_ind T (THead (Bind b) u t1) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) H5) in 
(False_ind (pc3 c0 (TSort (next g n)) (THead (Bind b) u t2)) H6))))))))))))) 
(\lambda (c0: C).(\lambda (w: T).(\lambda (u: T).(\lambda (_: (ty3 g c0 w 
u)).(\lambda (_: (((eq T w (TSort n)) \to (pc3 c0 (TSort (next g n)) 
u)))).(\lambda (v: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 v (THead (Bind 
Abst) u t))).(\lambda (_: (((eq T v (TSort n)) \to (pc3 c0 (TSort (next g n)) 
(THead (Bind Abst) u t))))).(\lambda (H5: (eq T (THead (Flat Appl) w v) 
(TSort n))).(let H6 \def (eq_ind T (THead (Flat Appl) w v) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(TSort n) H5) in (False_ind (pc3 c0 (TSort (next g n)) (THead (Flat Appl) w 
(THead (Bind Abst) u t))) H6)))))))))))) (\lambda (c0: C).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (_: (ty3 g c0 t1 t2)).(\lambda (_: (((eq T t1 
(TSort n)) \to (pc3 c0 (TSort (next g n)) t2)))).(\lambda (t0: T).(\lambda 
(_: (ty3 g c0 t2 t0)).(\lambda (_: (((eq T t2 (TSort n)) \to (pc3 c0 (TSort 
(next g n)) t0)))).(\lambda (H5: (eq T (THead (Flat Cast) t2 t1) (TSort 
n))).(let H6 \def (eq_ind T (THead (Flat Cast) t2 t1) (\lambda (ee: T).(match 
ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) 
H5) in (False_ind (pc3 c0 (TSort (next g n)) (THead (Flat Cast) t0 t2)) 
H6))))))))))) c y x H0))) H))))).
(* COMMENTS
Initial nodes: 1179
END *)

theorem ty3_gen_lref:
 \forall (g: G).(\forall (c: C).(\forall (x: T).(\forall (n: nat).((ty3 g c 
(TLRef n) x) \to (or (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda 
(t: T).(pc3 c (lift (S n) O t) x)))) (\lambda (e: C).(\lambda (u: T).(\lambda 
(_: T).(getl n c (CHead e (Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t: T).(ty3 g e u t))))) (ex3_3 C T T (\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(pc3 c (lift (S n) O u) x)))) (\lambda (e: C).(\lambda 
(u: T).(\lambda (_: T).(getl n c (CHead e (Bind Abst) u))))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u t))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (x: T).(\lambda (n: nat).(\lambda 
(H: (ty3 g c (TLRef n) x)).(insert_eq T (TLRef n) (\lambda (t: T).(ty3 g c t 
x)) (\lambda (_: T).(or (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda 
(t0: T).(pc3 c (lift (S n) O t0) x)))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (_: T).(getl n c (CHead e (Bind Abbr) u))))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (t0: T).(ty3 g e u t0))))) (ex3_3 C T T (\lambda 
(_: C).(\lambda (u: T).(\lambda (_: T).(pc3 c (lift (S n) O u) x)))) (\lambda 
(e: C).(\lambda (u: T).(\lambda (_: T).(getl n c (CHead e (Bind Abst) u))))) 
(\lambda (e: C).(\lambda (u: T).(\lambda (t0: T).(ty3 g e u t0))))))) 
(\lambda (y: T).(\lambda (H0: (ty3 g c y x)).(ty3_ind g (\lambda (c0: 
C).(\lambda (t: T).(\lambda (t0: T).((eq T t (TLRef n)) \to (or (ex3_3 C T T 
(\lambda (_: C).(\lambda (_: T).(\lambda (t1: T).(pc3 c0 (lift (S n) O t1) 
t0)))) (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c0 (CHead e 
(Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t1: T).(ty3 g e 
u t1))))) (ex3_3 C T T (\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(pc3 
c0 (lift (S n) O u) t0)))) (\lambda (e: C).(\lambda (u: T).(\lambda (_: 
T).(getl n c0 (CHead e (Bind Abst) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t1: T).(ty3 g e u t1)))))))))) (\lambda (c0: C).(\lambda (t2: 
T).(\lambda (t: T).(\lambda (_: (ty3 g c0 t2 t)).(\lambda (_: (((eq T t2 
(TLRef n)) \to (or (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t0: 
T).(pc3 c0 (lift (S n) O t0) t)))) (\lambda (e: C).(\lambda (u: T).(\lambda 
(_: T).(getl n c0 (CHead e (Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t0: T).(ty3 g e u t0))))) (ex3_3 C T T (\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(pc3 c0 (lift (S n) O u) t)))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u))))) 
(\lambda (e: C).(\lambda (u: T).(\lambda (t0: T).(ty3 g e u 
t0))))))))).(\lambda (u: T).(\lambda (t1: T).(\lambda (H3: (ty3 g c0 u 
t1)).(\lambda (H4: (((eq T u (TLRef n)) \to (or (ex3_3 C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift (S n) O t0) t1)))) (\lambda 
(e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abbr) 
u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0))))) 
(ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 c0 (lift 
(S n) O u0) t1)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n 
c0 (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(t0: T).(ty3 g e u0 t0))))))))).(\lambda (H5: (pc3 c0 t1 t2)).(\lambda (H6: 
(eq T u (TLRef n))).(let H7 \def (f_equal T T (\lambda (e: T).e) u (TLRef n) 
H6) in (let H8 \def (eq_ind T u (\lambda (t0: T).((eq T t0 (TLRef n)) \to (or 
(ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t3: T).(pc3 c0 (lift 
(S n) O t3) t1)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n 
c0 (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(t3: T).(ty3 g e u0 t3))))) (ex3_3 C T T (\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(pc3 c0 (lift (S n) O u0) t1)))) (\lambda (e: C).(\lambda 
(u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u0))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (t3: T).(ty3 g e u0 t3)))))))) H4 (TLRef n) H7) 
in (let H9 \def (eq_ind T u (\lambda (t0: T).(ty3 g c0 t0 t1)) H3 (TLRef n) 
H7) in (let H10 \def (H8 (refl_equal T (TLRef n))) in (or_ind (ex3_3 C T T 
(\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift (S n) O t0) 
t1)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e 
(Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g 
e u0 t0))))) (ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: 
T).(pc3 c0 (lift (S n) O u0) t1)))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(_: T).(getl n c0 (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (t0: T).(ty3 g e u0 t0))))) (or (ex3_3 C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift (S n) O t0) t2)))) (\lambda 
(e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abbr) 
u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0))))) 
(ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 c0 (lift 
(S n) O u0) t2)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n 
c0 (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(t0: T).(ty3 g e u0 t0)))))) (\lambda (H11: (ex3_3 C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift (S n) O t0) t1)))) (\lambda 
(e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abbr) 
u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 
t0)))))).(ex3_3_ind C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t0: 
T).(pc3 c0 (lift (S n) O t0) t1)))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(_: T).(getl n c0 (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (t0: T).(ty3 g e u0 t0)))) (or (ex3_3 C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift (S n) O t0) t2)))) (\lambda 
(e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abbr) 
u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0))))) 
(ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 c0 (lift 
(S n) O u0) t2)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n 
c0 (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(t0: T).(ty3 g e u0 t0)))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: 
T).(\lambda (H12: (pc3 c0 (lift (S n) O x2) t1)).(\lambda (H13: (getl n c0 
(CHead x0 (Bind Abbr) x1))).(\lambda (H14: (ty3 g x0 x1 x2)).(or_introl 
(ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift 
(S n) O t0) t2)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n 
c0 (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(t0: T).(ty3 g e u0 t0))))) (ex3_3 C T T (\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(pc3 c0 (lift (S n) O u0) t2)))) (\lambda (e: C).(\lambda 
(u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u0))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0))))) (ex3_3_intro C T T 
(\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift (S n) O t0) 
t2)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e 
(Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g 
e u0 t0)))) x0 x1 x2 (pc3_t t1 c0 (lift (S n) O x2) H12 t2 H5) H13 
H14)))))))) H11)) (\lambda (H11: (ex3_3 C T T (\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(pc3 c0 (lift (S n) O u0) t1)))) (\lambda (e: C).(\lambda 
(u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u0))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0)))))).(ex3_3_ind C T T 
(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 c0 (lift (S n) O u0) 
t1)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e 
(Bind Abst) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g 
e u0 t0)))) (or (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t0: 
T).(pc3 c0 (lift (S n) O t0) t2)))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(_: T).(getl n c0 (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (t0: T).(ty3 g e u0 t0))))) (ex3_3 C T T (\lambda (_: C).(\lambda 
(u0: T).(\lambda (_: T).(pc3 c0 (lift (S n) O u0) t2)))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u0))))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0)))))) 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: T).(\lambda (H12: (pc3 c0 
(lift (S n) O x1) t1)).(\lambda (H13: (getl n c0 (CHead x0 (Bind Abst) 
x1))).(\lambda (H14: (ty3 g x0 x1 x2)).(or_intror (ex3_3 C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift (S n) O t0) t2)))) (\lambda 
(e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abbr) 
u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0))))) 
(ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 c0 (lift 
(S n) O u0) t2)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n 
c0 (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(t0: T).(ty3 g e u0 t0))))) (ex3_3_intro C T T (\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(pc3 c0 (lift (S n) O u0) t2)))) (\lambda (e: C).(\lambda 
(u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u0))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0)))) x0 x1 x2 (pc3_t t1 c0 
(lift (S n) O x1) H12 t2 H5) H13 H14)))))))) H11)) H10)))))))))))))))) 
(\lambda (c0: C).(\lambda (m: nat).(\lambda (H1: (eq T (TSort m) (TLRef 
n))).(let H2 \def (eq_ind T (TSort m) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow False])) I (TLRef n) H1) in 
(False_ind (or (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t: 
T).(pc3 c0 (lift (S n) O t) (TSort (next g m)))))) (\lambda (e: C).(\lambda 
(u: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abbr) u))))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u t))))) (ex3_3 C T T (\lambda 
(_: C).(\lambda (u: T).(\lambda (_: T).(pc3 c0 (lift (S n) O u) (TSort (next 
g m)))))) (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c0 (CHead e 
(Bind Abst) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u 
t)))))) H2))))) (\lambda (n0: nat).(\lambda (c0: C).(\lambda (d: C).(\lambda 
(u: T).(\lambda (H1: (getl n0 c0 (CHead d (Bind Abbr) u))).(\lambda (t: 
T).(\lambda (H2: (ty3 g d u t)).(\lambda (_: (((eq T u (TLRef n)) \to (or 
(ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(pc3 d (lift (S 
n) O t0) t)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n d 
(CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: 
T).(ty3 g e u0 t0))))) (ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda 
(_: T).(pc3 d (lift (S n) O u0) t)))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (_: T).(getl n d (CHead e (Bind Abst) u0))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0))))))))).(\lambda (H4: 
(eq T (TLRef n0) (TLRef n))).(let H5 \def (f_equal T nat (\lambda (e: 
T).(match e in T return (\lambda (_: T).nat) with [(TSort _) \Rightarrow n0 | 
(TLRef n1) \Rightarrow n1 | (THead _ _ _) \Rightarrow n0])) (TLRef n0) (TLRef 
n) H4) in (let H6 \def (eq_ind nat n0 (\lambda (n1: nat).(getl n1 c0 (CHead d 
(Bind Abbr) u))) H1 n H5) in (eq_ind_r nat n (\lambda (n1: nat).(or (ex3_3 C 
T T (\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift (S n) O 
t0) (lift (S n1) O t))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: 
T).(getl n c0 (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (t0: T).(ty3 g e u0 t0))))) (ex3_3 C T T (\lambda (_: C).(\lambda 
(u0: T).(\lambda (_: T).(pc3 c0 (lift (S n) O u0) (lift (S n1) O t))))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind 
Abst) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 
t0))))))) (or_introl (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda 
(t0: T).(pc3 c0 (lift (S n) O t0) (lift (S n) O t))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abbr) u0))))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0))))) (ex3_3 
C T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 c0 (lift (S n) O 
u0) (lift (S n) O t))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: 
T).(getl n c0 (CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (t0: T).(ty3 g e u0 t0))))) (ex3_3_intro C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift (S n) O t0) (lift (S n) O 
t))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e 
(Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g 
e u0 t0)))) d u t (pc3_refl c0 (lift (S n) O t)) H6 H2)) n0 H5)))))))))))) 
(\lambda (n0: nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda 
(H1: (getl n0 c0 (CHead d (Bind Abst) u))).(\lambda (t: T).(\lambda (H2: (ty3 
g d u t)).(\lambda (_: (((eq T u (TLRef n)) \to (or (ex3_3 C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t0: T).(pc3 d (lift (S n) O t0) t)))) (\lambda 
(e: C).(\lambda (u0: T).(\lambda (_: T).(getl n d (CHead e (Bind Abbr) 
u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0))))) 
(ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 d (lift (S 
n) O u0) t)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n d 
(CHead e (Bind Abst) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: 
T).(ty3 g e u0 t0))))))))).(\lambda (H4: (eq T (TLRef n0) (TLRef n))).(let H5 
\def (f_equal T nat (\lambda (e: T).(match e in T return (\lambda (_: T).nat) 
with [(TSort _) \Rightarrow n0 | (TLRef n1) \Rightarrow n1 | (THead _ _ _) 
\Rightarrow n0])) (TLRef n0) (TLRef n) H4) in (let H6 \def (eq_ind nat n0 
(\lambda (n1: nat).(getl n1 c0 (CHead d (Bind Abst) u))) H1 n H5) in 
(eq_ind_r nat n (\lambda (n1: nat).(or (ex3_3 C T T (\lambda (_: C).(\lambda 
(_: T).(\lambda (t0: T).(pc3 c0 (lift (S n) O t0) (lift (S n1) O u))))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind 
Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 
t0))))) (ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 c0 
(lift (S n) O u0) (lift (S n1) O u))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u0))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0))))))) (or_intror (ex3_3 
C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift (S n) O 
t0) (lift (S n) O u))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: 
T).(getl n c0 (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (t0: T).(ty3 g e u0 t0))))) (ex3_3 C T T (\lambda (_: C).(\lambda 
(u0: T).(\lambda (_: T).(pc3 c0 (lift (S n) O u0) (lift (S n) O u))))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind 
Abst) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 
t0))))) (ex3_3_intro C T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: 
T).(pc3 c0 (lift (S n) O u0) (lift (S n) O u))))) (\lambda (e: C).(\lambda 
(u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u0))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0)))) d u t (pc3_refl c0 
(lift (S n) O u)) H6 H2)) n0 H5)))))))))))) (\lambda (c0: C).(\lambda (u: 
T).(\lambda (t: T).(\lambda (_: (ty3 g c0 u t)).(\lambda (_: (((eq T u (TLRef 
n)) \to (or (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t0: 
T).(pc3 c0 (lift (S n) O t0) t)))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(_: T).(getl n c0 (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (t0: T).(ty3 g e u0 t0))))) (ex3_3 C T T (\lambda (_: C).(\lambda 
(u0: T).(\lambda (_: T).(pc3 c0 (lift (S n) O u0) t)))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u0))))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 
t0))))))))).(\lambda (b: B).(\lambda (t1: T).(\lambda (t2: T).(\lambda (_: 
(ty3 g (CHead c0 (Bind b) u) t1 t2)).(\lambda (_: (((eq T t1 (TLRef n)) \to 
(or (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(pc3 (CHead 
c0 (Bind b) u) (lift (S n) O t0) t2)))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (_: T).(getl n (CHead c0 (Bind b) u) (CHead e (Bind Abbr) u0))))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0))))) (ex3_3 
C T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(pc3 (CHead c0 (Bind 
b) u) (lift (S n) O u0) t2)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: 
T).(getl n (CHead c0 (Bind b) u) (CHead e (Bind Abst) u0))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 t0))))))))).(\lambda (H5: 
(eq T (THead (Bind b) u t1) (TLRef n))).(let H6 \def (eq_ind T (THead (Bind 
b) u t1) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) I (TLRef n) H5) in (False_ind (or (ex3_3 C T T (\lambda 
(_: C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift (S n) O t0) (THead 
(Bind b) u t2))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n 
c0 (CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda 
(t0: T).(ty3 g e u0 t0))))) (ex3_3 C T T (\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(pc3 c0 (lift (S n) O u0) (THead (Bind b) u t2))))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind 
Abst) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 
t0)))))) H6))))))))))))) (\lambda (c0: C).(\lambda (w: T).(\lambda (u: 
T).(\lambda (_: (ty3 g c0 w u)).(\lambda (_: (((eq T w (TLRef n)) \to (or 
(ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(pc3 c0 (lift (S 
n) O t) u)))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 
(CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t: 
T).(ty3 g e u0 t))))) (ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda 
(_: T).(pc3 c0 (lift (S n) O u0) u)))) (\lambda (e: C).(\lambda (u0: 
T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u0))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (t: T).(ty3 g e u0 t))))))))).(\lambda (v: 
T).(\lambda (t: T).(\lambda (_: (ty3 g c0 v (THead (Bind Abst) u 
t))).(\lambda (_: (((eq T v (TLRef n)) \to (or (ex3_3 C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift (S n) O t0) (THead (Bind 
Abst) u t))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 
(CHead e (Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: 
T).(ty3 g e u0 t0))))) (ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda 
(_: T).(pc3 c0 (lift (S n) O u0) (THead (Bind Abst) u t))))) (\lambda (e: 
C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u0))))) 
(\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g e u0 
t0))))))))).(\lambda (H5: (eq T (THead (Flat Appl) w v) (TLRef n))).(let H6 
\def (eq_ind T (THead (Flat Appl) w v) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n) H5) in 
(False_ind (or (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t0: 
T).(pc3 c0 (lift (S n) O t0) (THead (Flat Appl) w (THead (Bind Abst) u 
t)))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e 
(Bind Abbr) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g 
e u0 t0))))) (ex3_3 C T T (\lambda (_: C).(\lambda (u0: T).(\lambda (_: 
T).(pc3 c0 (lift (S n) O u0) (THead (Flat Appl) w (THead (Bind Abst) u 
t)))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (_: T).(getl n c0 (CHead e 
(Bind Abst) u0))))) (\lambda (e: C).(\lambda (u0: T).(\lambda (t0: T).(ty3 g 
e u0 t0)))))) H6)))))))))))) (\lambda (c0: C).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (_: (ty3 g c0 t1 t2)).(\lambda (_: (((eq T t1 (TLRef n)) \to (or 
(ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(pc3 c0 (lift (S 
n) O t) t2)))) (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c0 
(CHead e (Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: 
T).(ty3 g e u t))))) (ex3_3 C T T (\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(pc3 c0 (lift (S n) O u) t2)))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u))))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u t))))))))).(\lambda (t0: 
T).(\lambda (_: (ty3 g c0 t2 t0)).(\lambda (_: (((eq T t2 (TLRef n)) \to (or 
(ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(pc3 c0 (lift (S 
n) O t) t0)))) (\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c0 
(CHead e (Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: 
T).(ty3 g e u t))))) (ex3_3 C T T (\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(pc3 c0 (lift (S n) O u) t0)))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u))))) (\lambda (e: 
C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u t))))))))).(\lambda (H5: (eq T 
(THead (Flat Cast) t2 t1) (TLRef n))).(let H6 \def (eq_ind T (THead (Flat 
Cast) t2 t1) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ 
_) \Rightarrow True])) I (TLRef n) H5) in (False_ind (or (ex3_3 C T T 
(\lambda (_: C).(\lambda (_: T).(\lambda (t: T).(pc3 c0 (lift (S n) O t) 
(THead (Flat Cast) t0 t2))))) (\lambda (e: C).(\lambda (u: T).(\lambda (_: 
T).(getl n c0 (CHead e (Bind Abbr) u))))) (\lambda (e: C).(\lambda (u: 
T).(\lambda (t: T).(ty3 g e u t))))) (ex3_3 C T T (\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(pc3 c0 (lift (S n) O u) (THead (Flat Cast) t0 t2))))) 
(\lambda (e: C).(\lambda (u: T).(\lambda (_: T).(getl n c0 (CHead e (Bind 
Abst) u))))) (\lambda (e: C).(\lambda (u: T).(\lambda (t: T).(ty3 g e u 
t)))))) H6))))))))))) c y x H0))) H))))).
(* COMMENTS
Initial nodes: 5569
END *)

theorem ty3_gen_bind:
 \forall (g: G).(\forall (b: B).(\forall (c: C).(\forall (u: T).(\forall (t1: 
T).(\forall (x: T).((ty3 g c (THead (Bind b) u t1) x) \to (ex3_2 T T (\lambda 
(t2: T).(\lambda (_: T).(pc3 c (THead (Bind b) u t2) x))) (\lambda (_: 
T).(\lambda (t: T).(ty3 g c u t))) (\lambda (t2: T).(\lambda (_: T).(ty3 g 
(CHead c (Bind b) u) t1 t2))))))))))
\def
 \lambda (g: G).(\lambda (b: B).(\lambda (c: C).(\lambda (u: T).(\lambda (t1: 
T).(\lambda (x: T).(\lambda (H: (ty3 g c (THead (Bind b) u t1) x)).(insert_eq 
T (THead (Bind b) u t1) (\lambda (t: T).(ty3 g c t x)) (\lambda (_: T).(ex3_2 
T T (\lambda (t2: T).(\lambda (_: T).(pc3 c (THead (Bind b) u t2) x))) 
(\lambda (_: T).(\lambda (t0: T).(ty3 g c u t0))) (\lambda (t2: T).(\lambda 
(_: T).(ty3 g (CHead c (Bind b) u) t1 t2))))) (\lambda (y: T).(\lambda (H0: 
(ty3 g c y x)).(ty3_ind g (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: 
T).((eq T t (THead (Bind b) u t1)) \to (ex3_2 T T (\lambda (t2: T).(\lambda 
(_: T).(pc3 c0 (THead (Bind b) u t2) t0))) (\lambda (_: T).(\lambda (t3: 
T).(ty3 g c0 u t3))) (\lambda (t2: T).(\lambda (_: T).(ty3 g (CHead c0 (Bind 
b) u) t1 t2)))))))) (\lambda (c0: C).(\lambda (t2: T).(\lambda (t: 
T).(\lambda (_: (ty3 g c0 t2 t)).(\lambda (_: (((eq T t2 (THead (Bind b) u 
t1)) \to (ex3_2 T T (\lambda (t3: T).(\lambda (_: T).(pc3 c0 (THead (Bind b) 
u t3) t))) (\lambda (_: T).(\lambda (t0: T).(ty3 g c0 u t0))) (\lambda (t3: 
T).(\lambda (_: T).(ty3 g (CHead c0 (Bind b) u) t1 t3))))))).(\lambda (u0: 
T).(\lambda (t0: T).(\lambda (H3: (ty3 g c0 u0 t0)).(\lambda (H4: (((eq T u0 
(THead (Bind b) u t1)) \to (ex3_2 T T (\lambda (t3: T).(\lambda (_: T).(pc3 
c0 (THead (Bind b) u t3) t0))) (\lambda (_: T).(\lambda (t4: T).(ty3 g c0 u 
t4))) (\lambda (t3: T).(\lambda (_: T).(ty3 g (CHead c0 (Bind b) u) t1 
t3))))))).(\lambda (H5: (pc3 c0 t0 t2)).(\lambda (H6: (eq T u0 (THead (Bind 
b) u t1))).(let H7 \def (f_equal T T (\lambda (e: T).e) u0 (THead (Bind b) u 
t1) H6) in (let H8 \def (eq_ind T u0 (\lambda (t3: T).((eq T t3 (THead (Bind 
b) u t1)) \to (ex3_2 T T (\lambda (t4: T).(\lambda (_: T).(pc3 c0 (THead 
(Bind b) u t4) t0))) (\lambda (_: T).(\lambda (t5: T).(ty3 g c0 u t5))) 
(\lambda (t4: T).(\lambda (_: T).(ty3 g (CHead c0 (Bind b) u) t1 t4)))))) H4 
(THead (Bind b) u t1) H7) in (let H9 \def (eq_ind T u0 (\lambda (t3: T).(ty3 
g c0 t3 t0)) H3 (THead (Bind b) u t1) H7) in (let H10 \def (H8 (refl_equal T 
(THead (Bind b) u t1))) in (ex3_2_ind T T (\lambda (t3: T).(\lambda (_: 
T).(pc3 c0 (THead (Bind b) u t3) t0))) (\lambda (_: T).(\lambda (t4: T).(ty3 
g c0 u t4))) (\lambda (t3: T).(\lambda (_: T).(ty3 g (CHead c0 (Bind b) u) t1 
t3))) (ex3_2 T T (\lambda (t3: T).(\lambda (_: T).(pc3 c0 (THead (Bind b) u 
t3) t2))) (\lambda (_: T).(\lambda (t4: T).(ty3 g c0 u t4))) (\lambda (t3: 
T).(\lambda (_: T).(ty3 g (CHead c0 (Bind b) u) t1 t3)))) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H11: (pc3 c0 (THead (Bind b) u x0) 
t0)).(\lambda (H12: (ty3 g c0 u x1)).(\lambda (H13: (ty3 g (CHead c0 (Bind b) 
u) t1 x0)).(ex3_2_intro T T (\lambda (t3: T).(\lambda (_: T).(pc3 c0 (THead 
(Bind b) u t3) t2))) (\lambda (_: T).(\lambda (t4: T).(ty3 g c0 u t4))) 
(\lambda (t3: T).(\lambda (_: T).(ty3 g (CHead c0 (Bind b) u) t1 t3))) x0 x1 
(pc3_t t0 c0 (THead (Bind b) u x0) H11 t2 H5) H12 H13)))))) 
H10)))))))))))))))) (\lambda (c0: C).(\lambda (m: nat).(\lambda (H1: (eq T 
(TSort m) (THead (Bind b) u t1))).(let H2 \def (eq_ind T (TSort m) (\lambda 
(ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
False])) I (THead (Bind b) u t1) H1) in (False_ind (ex3_2 T T (\lambda (t2: 
T).(\lambda (_: T).(pc3 c0 (THead (Bind b) u t2) (TSort (next g m))))) 
(\lambda (_: T).(\lambda (t: T).(ty3 g c0 u t))) (\lambda (t2: T).(\lambda 
(_: T).(ty3 g (CHead c0 (Bind b) u) t1 t2)))) H2))))) (\lambda (n: 
nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u0: T).(\lambda (_: (getl n 
c0 (CHead d (Bind Abbr) u0))).(\lambda (t: T).(\lambda (_: (ty3 g d u0 
t)).(\lambda (_: (((eq T u0 (THead (Bind b) u t1)) \to (ex3_2 T T (\lambda 
(t2: T).(\lambda (_: T).(pc3 d (THead (Bind b) u t2) t))) (\lambda (_: 
T).(\lambda (t0: T).(ty3 g d u t0))) (\lambda (t2: T).(\lambda (_: T).(ty3 g 
(CHead d (Bind b) u) t1 t2))))))).(\lambda (H4: (eq T (TLRef n) (THead (Bind 
b) u t1))).(let H5 \def (eq_ind T (TLRef n) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead (Bind b) u t1) 
H4) in (False_ind (ex3_2 T T (\lambda (t2: T).(\lambda (_: T).(pc3 c0 (THead 
(Bind b) u t2) (lift (S n) O t)))) (\lambda (_: T).(\lambda (t0: T).(ty3 g c0 
u t0))) (\lambda (t2: T).(\lambda (_: T).(ty3 g (CHead c0 (Bind b) u) t1 
t2)))) H5))))))))))) (\lambda (n: nat).(\lambda (c0: C).(\lambda (d: 
C).(\lambda (u0: T).(\lambda (_: (getl n c0 (CHead d (Bind Abst) 
u0))).(\lambda (t: T).(\lambda (_: (ty3 g d u0 t)).(\lambda (_: (((eq T u0 
(THead (Bind b) u t1)) \to (ex3_2 T T (\lambda (t2: T).(\lambda (_: T).(pc3 d 
(THead (Bind b) u t2) t))) (\lambda (_: T).(\lambda (t0: T).(ty3 g d u t0))) 
(\lambda (t2: T).(\lambda (_: T).(ty3 g (CHead d (Bind b) u) t1 
t2))))))).(\lambda (H4: (eq T (TLRef n) (THead (Bind b) u t1))).(let H5 \def 
(eq_ind T (TLRef n) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (THead (Bind b) u t1) H4) in (False_ind 
(ex3_2 T T (\lambda (t2: T).(\lambda (_: T).(pc3 c0 (THead (Bind b) u t2) 
(lift (S n) O u0)))) (\lambda (_: T).(\lambda (t0: T).(ty3 g c0 u t0))) 
(\lambda (t2: T).(\lambda (_: T).(ty3 g (CHead c0 (Bind b) u) t1 t2)))) 
H5))))))))))) (\lambda (c0: C).(\lambda (u0: T).(\lambda (t: T).(\lambda (H1: 
(ty3 g c0 u0 t)).(\lambda (H2: (((eq T u0 (THead (Bind b) u t1)) \to (ex3_2 T 
T (\lambda (t2: T).(\lambda (_: T).(pc3 c0 (THead (Bind b) u t2) t))) 
(\lambda (_: T).(\lambda (t0: T).(ty3 g c0 u t0))) (\lambda (t2: T).(\lambda 
(_: T).(ty3 g (CHead c0 (Bind b) u) t1 t2))))))).(\lambda (b0: B).(\lambda 
(t0: T).(\lambda (t2: T).(\lambda (H3: (ty3 g (CHead c0 (Bind b0) u0) t0 
t2)).(\lambda (H4: (((eq T t0 (THead (Bind b) u t1)) \to (ex3_2 T T (\lambda 
(t3: T).(\lambda (_: T).(pc3 (CHead c0 (Bind b0) u0) (THead (Bind b) u t3) 
t2))) (\lambda (_: T).(\lambda (t4: T).(ty3 g (CHead c0 (Bind b0) u0) u t4))) 
(\lambda (t3: T).(\lambda (_: T).(ty3 g (CHead (CHead c0 (Bind b0) u0) (Bind 
b) u) t1 t3))))))).(\lambda (H5: (eq T (THead (Bind b0) u0 t0) (THead (Bind 
b) u t1))).(let H6 \def (f_equal T B (\lambda (e: T).(match e in T return 
(\lambda (_: T).B) with [(TSort _) \Rightarrow b0 | (TLRef _) \Rightarrow b0 
| (THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).B) with 
[(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow b0])])) (THead (Bind b0) u0 
t0) (THead (Bind b) u t1) H5) in ((let H7 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u0 | 
(TLRef _) \Rightarrow u0 | (THead _ t3 _) \Rightarrow t3])) (THead (Bind b0) 
u0 t0) (THead (Bind b) u t1) H5) in ((let H8 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | 
(TLRef _) \Rightarrow t0 | (THead _ _ t3) \Rightarrow t3])) (THead (Bind b0) 
u0 t0) (THead (Bind b) u t1) H5) in (\lambda (H9: (eq T u0 u)).(\lambda (H10: 
(eq B b0 b)).(let H11 \def (eq_ind T t0 (\lambda (t3: T).((eq T t3 (THead 
(Bind b) u t1)) \to (ex3_2 T T (\lambda (t4: T).(\lambda (_: T).(pc3 (CHead 
c0 (Bind b0) u0) (THead (Bind b) u t4) t2))) (\lambda (_: T).(\lambda (t5: 
T).(ty3 g (CHead c0 (Bind b0) u0) u t5))) (\lambda (t4: T).(\lambda (_: 
T).(ty3 g (CHead (CHead c0 (Bind b0) u0) (Bind b) u) t1 t4)))))) H4 t1 H8) in 
(let H12 \def (eq_ind T t0 (\lambda (t3: T).(ty3 g (CHead c0 (Bind b0) u0) t3 
t2)) H3 t1 H8) in (let H13 \def (eq_ind B b0 (\lambda (b1: B).((eq T t1 
(THead (Bind b) u t1)) \to (ex3_2 T T (\lambda (t3: T).(\lambda (_: T).(pc3 
(CHead c0 (Bind b1) u0) (THead (Bind b) u t3) t2))) (\lambda (_: T).(\lambda 
(t4: T).(ty3 g (CHead c0 (Bind b1) u0) u t4))) (\lambda (t3: T).(\lambda (_: 
T).(ty3 g (CHead (CHead c0 (Bind b1) u0) (Bind b) u) t1 t3)))))) H11 b H10) 
in (let H14 \def (eq_ind B b0 (\lambda (b1: B).(ty3 g (CHead c0 (Bind b1) u0) 
t1 t2)) H12 b H10) in (eq_ind_r B b (\lambda (b1: B).(ex3_2 T T (\lambda (t3: 
T).(\lambda (_: T).(pc3 c0 (THead (Bind b) u t3) (THead (Bind b1) u0 t2)))) 
(\lambda (_: T).(\lambda (t4: T).(ty3 g c0 u t4))) (\lambda (t3: T).(\lambda 
(_: T).(ty3 g (CHead c0 (Bind b) u) t1 t3))))) (let H15 \def (eq_ind T u0 
(\lambda (t3: T).((eq T t1 (THead (Bind b) u t1)) \to (ex3_2 T T (\lambda 
(t4: T).(\lambda (_: T).(pc3 (CHead c0 (Bind b) t3) (THead (Bind b) u t4) 
t2))) (\lambda (_: T).(\lambda (t5: T).(ty3 g (CHead c0 (Bind b) t3) u t5))) 
(\lambda (t4: T).(\lambda (_: T).(ty3 g (CHead (CHead c0 (Bind b) t3) (Bind 
b) u) t1 t4)))))) H13 u H9) in (let H16 \def (eq_ind T u0 (\lambda (t3: 
T).(ty3 g (CHead c0 (Bind b) t3) t1 t2)) H14 u H9) in (let H17 \def (eq_ind T 
u0 (\lambda (t3: T).((eq T t3 (THead (Bind b) u t1)) \to (ex3_2 T T (\lambda 
(t4: T).(\lambda (_: T).(pc3 c0 (THead (Bind b) u t4) t))) (\lambda (_: 
T).(\lambda (t5: T).(ty3 g c0 u t5))) (\lambda (t4: T).(\lambda (_: T).(ty3 g 
(CHead c0 (Bind b) u) t1 t4)))))) H2 u H9) in (let H18 \def (eq_ind T u0 
(\lambda (t3: T).(ty3 g c0 t3 t)) H1 u H9) in (eq_ind_r T u (\lambda (t3: 
T).(ex3_2 T T (\lambda (t4: T).(\lambda (_: T).(pc3 c0 (THead (Bind b) u t4) 
(THead (Bind b) t3 t2)))) (\lambda (_: T).(\lambda (t5: T).(ty3 g c0 u t5))) 
(\lambda (t4: T).(\lambda (_: T).(ty3 g (CHead c0 (Bind b) u) t1 t4))))) 
(ex3_2_intro T T (\lambda (t3: T).(\lambda (_: T).(pc3 c0 (THead (Bind b) u 
t3) (THead (Bind b) u t2)))) (\lambda (_: T).(\lambda (t4: T).(ty3 g c0 u 
t4))) (\lambda (t3: T).(\lambda (_: T).(ty3 g (CHead c0 (Bind b) u) t1 t3))) 
t2 t (pc3_refl c0 (THead (Bind b) u t2)) H18 H16) u0 H9))))) b0 H10)))))))) 
H7)) H6))))))))))))) (\lambda (c0: C).(\lambda (w: T).(\lambda (u0: 
T).(\lambda (_: (ty3 g c0 w u0)).(\lambda (_: (((eq T w (THead (Bind b) u 
t1)) \to (ex3_2 T T (\lambda (t2: T).(\lambda (_: T).(pc3 c0 (THead (Bind b) 
u t2) u0))) (\lambda (_: T).(\lambda (t: T).(ty3 g c0 u t))) (\lambda (t2: 
T).(\lambda (_: T).(ty3 g (CHead c0 (Bind b) u) t1 t2))))))).(\lambda (v: 
T).(\lambda (t: T).(\lambda (_: (ty3 g c0 v (THead (Bind Abst) u0 
t))).(\lambda (_: (((eq T v (THead (Bind b) u t1)) \to (ex3_2 T T (\lambda 
(t2: T).(\lambda (_: T).(pc3 c0 (THead (Bind b) u t2) (THead (Bind Abst) u0 
t)))) (\lambda (_: T).(\lambda (t0: T).(ty3 g c0 u t0))) (\lambda (t2: 
T).(\lambda (_: T).(ty3 g (CHead c0 (Bind b) u) t1 t2))))))).(\lambda (H5: 
(eq T (THead (Flat Appl) w v) (THead (Bind b) u t1))).(let H6 \def (eq_ind T 
(THead (Flat Appl) w v) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind 
b) u t1) H5) in (False_ind (ex3_2 T T (\lambda (t2: T).(\lambda (_: T).(pc3 
c0 (THead (Bind b) u t2) (THead (Flat Appl) w (THead (Bind Abst) u0 t))))) 
(\lambda (_: T).(\lambda (t0: T).(ty3 g c0 u t0))) (\lambda (t2: T).(\lambda 
(_: T).(ty3 g (CHead c0 (Bind b) u) t1 t2)))) H6)))))))))))) (\lambda (c0: 
C).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (ty3 g c0 t0 t2)).(\lambda 
(_: (((eq T t0 (THead (Bind b) u t1)) \to (ex3_2 T T (\lambda (t3: 
T).(\lambda (_: T).(pc3 c0 (THead (Bind b) u t3) t2))) (\lambda (_: 
T).(\lambda (t: T).(ty3 g c0 u t))) (\lambda (t3: T).(\lambda (_: T).(ty3 g 
(CHead c0 (Bind b) u) t1 t3))))))).(\lambda (t3: T).(\lambda (_: (ty3 g c0 t2 
t3)).(\lambda (_: (((eq T t2 (THead (Bind b) u t1)) \to (ex3_2 T T (\lambda 
(t4: T).(\lambda (_: T).(pc3 c0 (THead (Bind b) u t4) t3))) (\lambda (_: 
T).(\lambda (t: T).(ty3 g c0 u t))) (\lambda (t4: T).(\lambda (_: T).(ty3 g 
(CHead c0 (Bind b) u) t1 t4))))))).(\lambda (H5: (eq T (THead (Flat Cast) t2 
t0) (THead (Bind b) u t1))).(let H6 \def (eq_ind T (THead (Flat Cast) t2 t0) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | 
(Flat _) \Rightarrow True])])) I (THead (Bind b) u t1) H5) in (False_ind 
(ex3_2 T T (\lambda (t4: T).(\lambda (_: T).(pc3 c0 (THead (Bind b) u t4) 
(THead (Flat Cast) t3 t2)))) (\lambda (_: T).(\lambda (t: T).(ty3 g c0 u t))) 
(\lambda (t4: T).(\lambda (_: T).(ty3 g (CHead c0 (Bind b) u) t1 t4)))) 
H6))))))))))) c y x H0))) H))))))).
(* COMMENTS
Initial nodes: 3389
END *)

theorem ty3_gen_appl:
 \forall (g: G).(\forall (c: C).(\forall (w: T).(\forall (v: T).(\forall (x: 
T).((ty3 g c (THead (Flat Appl) w v) x) \to (ex3_2 T T (\lambda (u: 
T).(\lambda (t: T).(pc3 c (THead (Flat Appl) w (THead (Bind Abst) u t)) x))) 
(\lambda (u: T).(\lambda (t: T).(ty3 g c v (THead (Bind Abst) u t)))) 
(\lambda (u: T).(\lambda (_: T).(ty3 g c w u)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (w: T).(\lambda (v: T).(\lambda (x: 
T).(\lambda (H: (ty3 g c (THead (Flat Appl) w v) x)).(insert_eq T (THead 
(Flat Appl) w v) (\lambda (t: T).(ty3 g c t x)) (\lambda (_: T).(ex3_2 T T 
(\lambda (u: T).(\lambda (t0: T).(pc3 c (THead (Flat Appl) w (THead (Bind 
Abst) u t0)) x))) (\lambda (u: T).(\lambda (t0: T).(ty3 g c v (THead (Bind 
Abst) u t0)))) (\lambda (u: T).(\lambda (_: T).(ty3 g c w u))))) (\lambda (y: 
T).(\lambda (H0: (ty3 g c y x)).(ty3_ind g (\lambda (c0: C).(\lambda (t: 
T).(\lambda (t0: T).((eq T t (THead (Flat Appl) w v)) \to (ex3_2 T T (\lambda 
(u: T).(\lambda (t1: T).(pc3 c0 (THead (Flat Appl) w (THead (Bind Abst) u 
t1)) t0))) (\lambda (u: T).(\lambda (t1: T).(ty3 g c0 v (THead (Bind Abst) u 
t1)))) (\lambda (u: T).(\lambda (_: T).(ty3 g c0 w u)))))))) (\lambda (c0: 
C).(\lambda (t2: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 t2 t)).(\lambda 
(_: (((eq T t2 (THead (Flat Appl) w v)) \to (ex3_2 T T (\lambda (u: 
T).(\lambda (t0: T).(pc3 c0 (THead (Flat Appl) w (THead (Bind Abst) u t0)) 
t))) (\lambda (u: T).(\lambda (t0: T).(ty3 g c0 v (THead (Bind Abst) u t0)))) 
(\lambda (u: T).(\lambda (_: T).(ty3 g c0 w u))))))).(\lambda (u: T).(\lambda 
(t1: T).(\lambda (H3: (ty3 g c0 u t1)).(\lambda (H4: (((eq T u (THead (Flat 
Appl) w v)) \to (ex3_2 T T (\lambda (u0: T).(\lambda (t0: T).(pc3 c0 (THead 
(Flat Appl) w (THead (Bind Abst) u0 t0)) t1))) (\lambda (u0: T).(\lambda (t0: 
T).(ty3 g c0 v (THead (Bind Abst) u0 t0)))) (\lambda (u0: T).(\lambda (_: 
T).(ty3 g c0 w u0))))))).(\lambda (H5: (pc3 c0 t1 t2)).(\lambda (H6: (eq T u 
(THead (Flat Appl) w v))).(let H7 \def (f_equal T T (\lambda (e: T).e) u 
(THead (Flat Appl) w v) H6) in (let H8 \def (eq_ind T u (\lambda (t0: T).((eq 
T t0 (THead (Flat Appl) w v)) \to (ex3_2 T T (\lambda (u0: T).(\lambda (t3: 
T).(pc3 c0 (THead (Flat Appl) w (THead (Bind Abst) u0 t3)) t1))) (\lambda 
(u0: T).(\lambda (t3: T).(ty3 g c0 v (THead (Bind Abst) u0 t3)))) (\lambda 
(u0: T).(\lambda (_: T).(ty3 g c0 w u0)))))) H4 (THead (Flat Appl) w v) H7) 
in (let H9 \def (eq_ind T u (\lambda (t0: T).(ty3 g c0 t0 t1)) H3 (THead 
(Flat Appl) w v) H7) in (let H10 \def (H8 (refl_equal T (THead (Flat Appl) w 
v))) in (ex3_2_ind T T (\lambda (u0: T).(\lambda (t0: T).(pc3 c0 (THead (Flat 
Appl) w (THead (Bind Abst) u0 t0)) t1))) (\lambda (u0: T).(\lambda (t0: 
T).(ty3 g c0 v (THead (Bind Abst) u0 t0)))) (\lambda (u0: T).(\lambda (_: 
T).(ty3 g c0 w u0))) (ex3_2 T T (\lambda (u0: T).(\lambda (t0: T).(pc3 c0 
(THead (Flat Appl) w (THead (Bind Abst) u0 t0)) t2))) (\lambda (u0: 
T).(\lambda (t0: T).(ty3 g c0 v (THead (Bind Abst) u0 t0)))) (\lambda (u0: 
T).(\lambda (_: T).(ty3 g c0 w u0)))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H11: (pc3 c0 (THead (Flat Appl) w (THead (Bind Abst) x0 x1)) 
t1)).(\lambda (H12: (ty3 g c0 v (THead (Bind Abst) x0 x1))).(\lambda (H13: 
(ty3 g c0 w x0)).(ex3_2_intro T T (\lambda (u0: T).(\lambda (t0: T).(pc3 c0 
(THead (Flat Appl) w (THead (Bind Abst) u0 t0)) t2))) (\lambda (u0: 
T).(\lambda (t0: T).(ty3 g c0 v (THead (Bind Abst) u0 t0)))) (\lambda (u0: 
T).(\lambda (_: T).(ty3 g c0 w u0))) x0 x1 (pc3_t t1 c0 (THead (Flat Appl) w 
(THead (Bind Abst) x0 x1)) H11 t2 H5) H12 H13)))))) H10)))))))))))))))) 
(\lambda (c0: C).(\lambda (m: nat).(\lambda (H1: (eq T (TSort m) (THead (Flat 
Appl) w v))).(let H2 \def (eq_ind T (TSort m) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow False])) I (THead (Flat Appl) w 
v) H1) in (False_ind (ex3_2 T T (\lambda (u: T).(\lambda (t: T).(pc3 c0 
(THead (Flat Appl) w (THead (Bind Abst) u t)) (TSort (next g m))))) (\lambda 
(u: T).(\lambda (t: T).(ty3 g c0 v (THead (Bind Abst) u t)))) (\lambda (u: 
T).(\lambda (_: T).(ty3 g c0 w u)))) H2))))) (\lambda (n: nat).(\lambda (c0: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (_: (getl n c0 (CHead d (Bind 
Abbr) u))).(\lambda (t: T).(\lambda (_: (ty3 g d u t)).(\lambda (_: (((eq T u 
(THead (Flat Appl) w v)) \to (ex3_2 T T (\lambda (u0: T).(\lambda (t0: 
T).(pc3 d (THead (Flat Appl) w (THead (Bind Abst) u0 t0)) t))) (\lambda (u0: 
T).(\lambda (t0: T).(ty3 g d v (THead (Bind Abst) u0 t0)))) (\lambda (u0: 
T).(\lambda (_: T).(ty3 g d w u0))))))).(\lambda (H4: (eq T (TLRef n) (THead 
(Flat Appl) w v))).(let H5 \def (eq_ind T (TLRef n) (\lambda (ee: T).(match 
ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead 
(Flat Appl) w v) H4) in (False_ind (ex3_2 T T (\lambda (u0: T).(\lambda (t0: 
T).(pc3 c0 (THead (Flat Appl) w (THead (Bind Abst) u0 t0)) (lift (S n) O 
t)))) (\lambda (u0: T).(\lambda (t0: T).(ty3 g c0 v (THead (Bind Abst) u0 
t0)))) (\lambda (u0: T).(\lambda (_: T).(ty3 g c0 w u0)))) H5))))))))))) 
(\lambda (n: nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda 
(_: (getl n c0 (CHead d (Bind Abst) u))).(\lambda (t: T).(\lambda (_: (ty3 g 
d u t)).(\lambda (_: (((eq T u (THead (Flat Appl) w v)) \to (ex3_2 T T 
(\lambda (u0: T).(\lambda (t0: T).(pc3 d (THead (Flat Appl) w (THead (Bind 
Abst) u0 t0)) t))) (\lambda (u0: T).(\lambda (t0: T).(ty3 g d v (THead (Bind 
Abst) u0 t0)))) (\lambda (u0: T).(\lambda (_: T).(ty3 g d w 
u0))))))).(\lambda (H4: (eq T (TLRef n) (THead (Flat Appl) w v))).(let H5 
\def (eq_ind T (TLRef n) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (THead (Flat Appl) w v) H4) in 
(False_ind (ex3_2 T T (\lambda (u0: T).(\lambda (t0: T).(pc3 c0 (THead (Flat 
Appl) w (THead (Bind Abst) u0 t0)) (lift (S n) O u)))) (\lambda (u0: 
T).(\lambda (t0: T).(ty3 g c0 v (THead (Bind Abst) u0 t0)))) (\lambda (u0: 
T).(\lambda (_: T).(ty3 g c0 w u0)))) H5))))))))))) (\lambda (c0: C).(\lambda 
(u: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 u t)).(\lambda (_: (((eq T u 
(THead (Flat Appl) w v)) \to (ex3_2 T T (\lambda (u0: T).(\lambda (t0: 
T).(pc3 c0 (THead (Flat Appl) w (THead (Bind Abst) u0 t0)) t))) (\lambda (u0: 
T).(\lambda (t0: T).(ty3 g c0 v (THead (Bind Abst) u0 t0)))) (\lambda (u0: 
T).(\lambda (_: T).(ty3 g c0 w u0))))))).(\lambda (b: B).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (_: (ty3 g (CHead c0 (Bind b) u) t1 
t2)).(\lambda (_: (((eq T t1 (THead (Flat Appl) w v)) \to (ex3_2 T T (\lambda 
(u0: T).(\lambda (t0: T).(pc3 (CHead c0 (Bind b) u) (THead (Flat Appl) w 
(THead (Bind Abst) u0 t0)) t2))) (\lambda (u0: T).(\lambda (t0: T).(ty3 g 
(CHead c0 (Bind b) u) v (THead (Bind Abst) u0 t0)))) (\lambda (u0: 
T).(\lambda (_: T).(ty3 g (CHead c0 (Bind b) u) w u0))))))).(\lambda (H5: (eq 
T (THead (Bind b) u t1) (THead (Flat Appl) w v))).(let H6 \def (eq_ind T 
(THead (Bind b) u t1) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat 
Appl) w v) H5) in (False_ind (ex3_2 T T (\lambda (u0: T).(\lambda (t0: 
T).(pc3 c0 (THead (Flat Appl) w (THead (Bind Abst) u0 t0)) (THead (Bind b) u 
t2)))) (\lambda (u0: T).(\lambda (t0: T).(ty3 g c0 v (THead (Bind Abst) u0 
t0)))) (\lambda (u0: T).(\lambda (_: T).(ty3 g c0 w u0)))) H6))))))))))))) 
(\lambda (c0: C).(\lambda (w0: T).(\lambda (u: T).(\lambda (H1: (ty3 g c0 w0 
u)).(\lambda (H2: (((eq T w0 (THead (Flat Appl) w v)) \to (ex3_2 T T (\lambda 
(u0: T).(\lambda (t: T).(pc3 c0 (THead (Flat Appl) w (THead (Bind Abst) u0 
t)) u))) (\lambda (u0: T).(\lambda (t: T).(ty3 g c0 v (THead (Bind Abst) u0 
t)))) (\lambda (u0: T).(\lambda (_: T).(ty3 g c0 w u0))))))).(\lambda (v0: 
T).(\lambda (t: T).(\lambda (H3: (ty3 g c0 v0 (THead (Bind Abst) u 
t))).(\lambda (H4: (((eq T v0 (THead (Flat Appl) w v)) \to (ex3_2 T T 
(\lambda (u0: T).(\lambda (t0: T).(pc3 c0 (THead (Flat Appl) w (THead (Bind 
Abst) u0 t0)) (THead (Bind Abst) u t)))) (\lambda (u0: T).(\lambda (t0: 
T).(ty3 g c0 v (THead (Bind Abst) u0 t0)))) (\lambda (u0: T).(\lambda (_: 
T).(ty3 g c0 w u0))))))).(\lambda (H5: (eq T (THead (Flat Appl) w0 v0) (THead 
(Flat Appl) w v))).(let H6 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow w0 | (TLRef _) 
\Rightarrow w0 | (THead _ t0 _) \Rightarrow t0])) (THead (Flat Appl) w0 v0) 
(THead (Flat Appl) w v) H5) in ((let H7 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow v0 | 
(TLRef _) \Rightarrow v0 | (THead _ _ t0) \Rightarrow t0])) (THead (Flat 
Appl) w0 v0) (THead (Flat Appl) w v) H5) in (\lambda (H8: (eq T w0 w)).(let 
H9 \def (eq_ind T v0 (\lambda (t0: T).((eq T t0 (THead (Flat Appl) w v)) \to 
(ex3_2 T T (\lambda (u0: T).(\lambda (t1: T).(pc3 c0 (THead (Flat Appl) w 
(THead (Bind Abst) u0 t1)) (THead (Bind Abst) u t)))) (\lambda (u0: 
T).(\lambda (t1: T).(ty3 g c0 v (THead (Bind Abst) u0 t1)))) (\lambda (u0: 
T).(\lambda (_: T).(ty3 g c0 w u0)))))) H4 v H7) in (let H10 \def (eq_ind T 
v0 (\lambda (t0: T).(ty3 g c0 t0 (THead (Bind Abst) u t))) H3 v H7) in (let 
H11 \def (eq_ind T w0 (\lambda (t0: T).((eq T t0 (THead (Flat Appl) w v)) \to 
(ex3_2 T T (\lambda (u0: T).(\lambda (t1: T).(pc3 c0 (THead (Flat Appl) w 
(THead (Bind Abst) u0 t1)) u))) (\lambda (u0: T).(\lambda (t1: T).(ty3 g c0 v 
(THead (Bind Abst) u0 t1)))) (\lambda (u0: T).(\lambda (_: T).(ty3 g c0 w 
u0)))))) H2 w H8) in (let H12 \def (eq_ind T w0 (\lambda (t0: T).(ty3 g c0 t0 
u)) H1 w H8) in (eq_ind_r T w (\lambda (t0: T).(ex3_2 T T (\lambda (u0: 
T).(\lambda (t1: T).(pc3 c0 (THead (Flat Appl) w (THead (Bind Abst) u0 t1)) 
(THead (Flat Appl) t0 (THead (Bind Abst) u t))))) (\lambda (u0: T).(\lambda 
(t1: T).(ty3 g c0 v (THead (Bind Abst) u0 t1)))) (\lambda (u0: T).(\lambda 
(_: T).(ty3 g c0 w u0))))) (ex3_2_intro T T (\lambda (u0: T).(\lambda (t0: 
T).(pc3 c0 (THead (Flat Appl) w (THead (Bind Abst) u0 t0)) (THead (Flat Appl) 
w (THead (Bind Abst) u t))))) (\lambda (u0: T).(\lambda (t0: T).(ty3 g c0 v 
(THead (Bind Abst) u0 t0)))) (\lambda (u0: T).(\lambda (_: T).(ty3 g c0 w 
u0))) u t (pc3_refl c0 (THead (Flat Appl) w (THead (Bind Abst) u t))) H10 
H12) w0 H8))))))) H6)))))))))))) (\lambda (c0: C).(\lambda (t1: T).(\lambda 
(t2: T).(\lambda (_: (ty3 g c0 t1 t2)).(\lambda (_: (((eq T t1 (THead (Flat 
Appl) w v)) \to (ex3_2 T T (\lambda (u: T).(\lambda (t: T).(pc3 c0 (THead 
(Flat Appl) w (THead (Bind Abst) u t)) t2))) (\lambda (u: T).(\lambda (t: 
T).(ty3 g c0 v (THead (Bind Abst) u t)))) (\lambda (u: T).(\lambda (_: 
T).(ty3 g c0 w u))))))).(\lambda (t0: T).(\lambda (_: (ty3 g c0 t2 
t0)).(\lambda (_: (((eq T t2 (THead (Flat Appl) w v)) \to (ex3_2 T T (\lambda 
(u: T).(\lambda (t: T).(pc3 c0 (THead (Flat Appl) w (THead (Bind Abst) u t)) 
t0))) (\lambda (u: T).(\lambda (t: T).(ty3 g c0 v (THead (Bind Abst) u t)))) 
(\lambda (u: T).(\lambda (_: T).(ty3 g c0 w u))))))).(\lambda (H5: (eq T 
(THead (Flat Cast) t2 t1) (THead (Flat Appl) w v))).(let H6 \def (eq_ind T 
(THead (Flat Cast) t2 t1) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow False | (Flat f) \Rightarrow (match f in F return 
(\lambda (_: F).Prop) with [Appl \Rightarrow False | Cast \Rightarrow 
True])])])) I (THead (Flat Appl) w v) H5) in (False_ind (ex3_2 T T (\lambda 
(u: T).(\lambda (t: T).(pc3 c0 (THead (Flat Appl) w (THead (Bind Abst) u t)) 
(THead (Flat Cast) t0 t2)))) (\lambda (u: T).(\lambda (t: T).(ty3 g c0 v 
(THead (Bind Abst) u t)))) (\lambda (u: T).(\lambda (_: T).(ty3 g c0 w u)))) 
H6))))))))))) c y x H0))) H)))))).
(* COMMENTS
Initial nodes: 3171
END *)

theorem ty3_gen_cast:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t2: T).(\forall 
(x: T).((ty3 g c (THead (Flat Cast) t2 t1) x) \to (ex3 T (\lambda (t0: 
T).(pc3 c (THead (Flat Cast) t0 t2) x)) (\lambda (_: T).(ty3 g c t1 t2)) 
(\lambda (t0: T).(ty3 g c t2 t0))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(x: T).(\lambda (H: (ty3 g c (THead (Flat Cast) t2 t1) x)).(insert_eq T 
(THead (Flat Cast) t2 t1) (\lambda (t: T).(ty3 g c t x)) (\lambda (_: T).(ex3 
T (\lambda (t0: T).(pc3 c (THead (Flat Cast) t0 t2) x)) (\lambda (_: T).(ty3 
g c t1 t2)) (\lambda (t0: T).(ty3 g c t2 t0)))) (\lambda (y: T).(\lambda (H0: 
(ty3 g c y x)).(ty3_ind g (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: 
T).((eq T t (THead (Flat Cast) t2 t1)) \to (ex3 T (\lambda (t3: T).(pc3 c0 
(THead (Flat Cast) t3 t2) t0)) (\lambda (_: T).(ty3 g c0 t1 t2)) (\lambda 
(t3: T).(ty3 g c0 t2 t3))))))) (\lambda (c0: C).(\lambda (t0: T).(\lambda (t: 
T).(\lambda (_: (ty3 g c0 t0 t)).(\lambda (_: (((eq T t0 (THead (Flat Cast) 
t2 t1)) \to (ex3 T (\lambda (t3: T).(pc3 c0 (THead (Flat Cast) t3 t2) t)) 
(\lambda (_: T).(ty3 g c0 t1 t2)) (\lambda (t3: T).(ty3 g c0 t2 
t3)))))).(\lambda (u: T).(\lambda (t3: T).(\lambda (H3: (ty3 g c0 u 
t3)).(\lambda (H4: (((eq T u (THead (Flat Cast) t2 t1)) \to (ex3 T (\lambda 
(t4: T).(pc3 c0 (THead (Flat Cast) t4 t2) t3)) (\lambda (_: T).(ty3 g c0 t1 
t2)) (\lambda (t4: T).(ty3 g c0 t2 t4)))))).(\lambda (H5: (pc3 c0 t3 
t0)).(\lambda (H6: (eq T u (THead (Flat Cast) t2 t1))).(let H7 \def (f_equal 
T T (\lambda (e: T).e) u (THead (Flat Cast) t2 t1) H6) in (let H8 \def 
(eq_ind T u (\lambda (t4: T).((eq T t4 (THead (Flat Cast) t2 t1)) \to (ex3 T 
(\lambda (t5: T).(pc3 c0 (THead (Flat Cast) t5 t2) t3)) (\lambda (_: T).(ty3 
g c0 t1 t2)) (\lambda (t5: T).(ty3 g c0 t2 t5))))) H4 (THead (Flat Cast) t2 
t1) H7) in (let H9 \def (eq_ind T u (\lambda (t4: T).(ty3 g c0 t4 t3)) H3 
(THead (Flat Cast) t2 t1) H7) in (let H10 \def (H8 (refl_equal T (THead (Flat 
Cast) t2 t1))) in (ex3_ind T (\lambda (t4: T).(pc3 c0 (THead (Flat Cast) t4 
t2) t3)) (\lambda (_: T).(ty3 g c0 t1 t2)) (\lambda (t4: T).(ty3 g c0 t2 t4)) 
(ex3 T (\lambda (t4: T).(pc3 c0 (THead (Flat Cast) t4 t2) t0)) (\lambda (_: 
T).(ty3 g c0 t1 t2)) (\lambda (t4: T).(ty3 g c0 t2 t4))) (\lambda (x0: 
T).(\lambda (H11: (pc3 c0 (THead (Flat Cast) x0 t2) t3)).(\lambda (H12: (ty3 
g c0 t1 t2)).(\lambda (H13: (ty3 g c0 t2 x0)).(ex3_intro T (\lambda (t4: 
T).(pc3 c0 (THead (Flat Cast) t4 t2) t0)) (\lambda (_: T).(ty3 g c0 t1 t2)) 
(\lambda (t4: T).(ty3 g c0 t2 t4)) x0 (pc3_t t3 c0 (THead (Flat Cast) x0 t2) 
H11 t0 H5) H12 H13))))) H10)))))))))))))))) (\lambda (c0: C).(\lambda (m: 
nat).(\lambda (H1: (eq T (TSort m) (THead (Flat Cast) t2 t1))).(let H2 \def 
(eq_ind T (TSort m) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (THead (Flat Cast) t2 t1) H1) in 
(False_ind (ex3 T (\lambda (t0: T).(pc3 c0 (THead (Flat Cast) t0 t2) (TSort 
(next g m)))) (\lambda (_: T).(ty3 g c0 t1 t2)) (\lambda (t0: T).(ty3 g c0 t2 
t0))) H2))))) (\lambda (n: nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u: 
T).(\lambda (_: (getl n c0 (CHead d (Bind Abbr) u))).(\lambda (t: T).(\lambda 
(_: (ty3 g d u t)).(\lambda (_: (((eq T u (THead (Flat Cast) t2 t1)) \to (ex3 
T (\lambda (t0: T).(pc3 d (THead (Flat Cast) t0 t2) t)) (\lambda (_: T).(ty3 
g d t1 t2)) (\lambda (t0: T).(ty3 g d t2 t0)))))).(\lambda (H4: (eq T (TLRef 
n) (THead (Flat Cast) t2 t1))).(let H5 \def (eq_ind T (TLRef n) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) I 
(THead (Flat Cast) t2 t1) H4) in (False_ind (ex3 T (\lambda (t0: T).(pc3 c0 
(THead (Flat Cast) t0 t2) (lift (S n) O t))) (\lambda (_: T).(ty3 g c0 t1 
t2)) (\lambda (t0: T).(ty3 g c0 t2 t0))) H5))))))))))) (\lambda (n: 
nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (_: (getl n c0 
(CHead d (Bind Abst) u))).(\lambda (t: T).(\lambda (_: (ty3 g d u 
t)).(\lambda (_: (((eq T u (THead (Flat Cast) t2 t1)) \to (ex3 T (\lambda 
(t0: T).(pc3 d (THead (Flat Cast) t0 t2) t)) (\lambda (_: T).(ty3 g d t1 t2)) 
(\lambda (t0: T).(ty3 g d t2 t0)))))).(\lambda (H4: (eq T (TLRef n) (THead 
(Flat Cast) t2 t1))).(let H5 \def (eq_ind T (TLRef n) (\lambda (ee: T).(match 
ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead 
(Flat Cast) t2 t1) H4) in (False_ind (ex3 T (\lambda (t0: T).(pc3 c0 (THead 
(Flat Cast) t0 t2) (lift (S n) O u))) (\lambda (_: T).(ty3 g c0 t1 t2)) 
(\lambda (t0: T).(ty3 g c0 t2 t0))) H5))))))))))) (\lambda (c0: C).(\lambda 
(u: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 u t)).(\lambda (_: (((eq T u 
(THead (Flat Cast) t2 t1)) \to (ex3 T (\lambda (t0: T).(pc3 c0 (THead (Flat 
Cast) t0 t2) t)) (\lambda (_: T).(ty3 g c0 t1 t2)) (\lambda (t0: T).(ty3 g c0 
t2 t0)))))).(\lambda (b: B).(\lambda (t0: T).(\lambda (t3: T).(\lambda (_: 
(ty3 g (CHead c0 (Bind b) u) t0 t3)).(\lambda (_: (((eq T t0 (THead (Flat 
Cast) t2 t1)) \to (ex3 T (\lambda (t4: T).(pc3 (CHead c0 (Bind b) u) (THead 
(Flat Cast) t4 t2) t3)) (\lambda (_: T).(ty3 g (CHead c0 (Bind b) u) t1 t2)) 
(\lambda (t4: T).(ty3 g (CHead c0 (Bind b) u) t2 t4)))))).(\lambda (H5: (eq T 
(THead (Bind b) u t0) (THead (Flat Cast) t2 t1))).(let H6 \def (eq_ind T 
(THead (Bind b) u t0) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat 
Cast) t2 t1) H5) in (False_ind (ex3 T (\lambda (t4: T).(pc3 c0 (THead (Flat 
Cast) t4 t2) (THead (Bind b) u t3))) (\lambda (_: T).(ty3 g c0 t1 t2)) 
(\lambda (t4: T).(ty3 g c0 t2 t4))) H6))))))))))))) (\lambda (c0: C).(\lambda 
(w: T).(\lambda (u: T).(\lambda (_: (ty3 g c0 w u)).(\lambda (_: (((eq T w 
(THead (Flat Cast) t2 t1)) \to (ex3 T (\lambda (t0: T).(pc3 c0 (THead (Flat 
Cast) t0 t2) u)) (\lambda (_: T).(ty3 g c0 t1 t2)) (\lambda (t0: T).(ty3 g c0 
t2 t0)))))).(\lambda (v: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 v (THead 
(Bind Abst) u t))).(\lambda (_: (((eq T v (THead (Flat Cast) t2 t1)) \to (ex3 
T (\lambda (t0: T).(pc3 c0 (THead (Flat Cast) t0 t2) (THead (Bind Abst) u 
t))) (\lambda (_: T).(ty3 g c0 t1 t2)) (\lambda (t0: T).(ty3 g c0 t2 
t0)))))).(\lambda (H5: (eq T (THead (Flat Appl) w v) (THead (Flat Cast) t2 
t1))).(let H6 \def (eq_ind T (THead (Flat Appl) w v) (\lambda (ee: T).(match 
ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat f) \Rightarrow 
(match f in F return (\lambda (_: F).Prop) with [Appl \Rightarrow True | Cast 
\Rightarrow False])])])) I (THead (Flat Cast) t2 t1) H5) in (False_ind (ex3 T 
(\lambda (t0: T).(pc3 c0 (THead (Flat Cast) t0 t2) (THead (Flat Appl) w 
(THead (Bind Abst) u t)))) (\lambda (_: T).(ty3 g c0 t1 t2)) (\lambda (t0: 
T).(ty3 g c0 t2 t0))) H6)))))))))))) (\lambda (c0: C).(\lambda (t0: 
T).(\lambda (t3: T).(\lambda (H1: (ty3 g c0 t0 t3)).(\lambda (H2: (((eq T t0 
(THead (Flat Cast) t2 t1)) \to (ex3 T (\lambda (t4: T).(pc3 c0 (THead (Flat 
Cast) t4 t2) t3)) (\lambda (_: T).(ty3 g c0 t1 t2)) (\lambda (t4: T).(ty3 g 
c0 t2 t4)))))).(\lambda (t4: T).(\lambda (H3: (ty3 g c0 t3 t4)).(\lambda (H4: 
(((eq T t3 (THead (Flat Cast) t2 t1)) \to (ex3 T (\lambda (t5: T).(pc3 c0 
(THead (Flat Cast) t5 t2) t4)) (\lambda (_: T).(ty3 g c0 t1 t2)) (\lambda 
(t5: T).(ty3 g c0 t2 t5)))))).(\lambda (H5: (eq T (THead (Flat Cast) t3 t0) 
(THead (Flat Cast) t2 t1))).(let H6 \def (f_equal T T (\lambda (e: T).(match 
e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t3 | (TLRef _) 
\Rightarrow t3 | (THead _ t _) \Rightarrow t])) (THead (Flat Cast) t3 t0) 
(THead (Flat Cast) t2 t1) H5) in ((let H7 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | 
(TLRef _) \Rightarrow t0 | (THead _ _ t) \Rightarrow t])) (THead (Flat Cast) 
t3 t0) (THead (Flat Cast) t2 t1) H5) in (\lambda (H8: (eq T t3 t2)).(let H9 
\def (eq_ind T t3 (\lambda (t: T).((eq T t (THead (Flat Cast) t2 t1)) \to 
(ex3 T (\lambda (t5: T).(pc3 c0 (THead (Flat Cast) t5 t2) t4)) (\lambda (_: 
T).(ty3 g c0 t1 t2)) (\lambda (t5: T).(ty3 g c0 t2 t5))))) H4 t2 H8) in (let 
H10 \def (eq_ind T t3 (\lambda (t: T).(ty3 g c0 t t4)) H3 t2 H8) in (let H11 
\def (eq_ind T t3 (\lambda (t: T).((eq T t0 (THead (Flat Cast) t2 t1)) \to 
(ex3 T (\lambda (t5: T).(pc3 c0 (THead (Flat Cast) t5 t2) t)) (\lambda (_: 
T).(ty3 g c0 t1 t2)) (\lambda (t5: T).(ty3 g c0 t2 t5))))) H2 t2 H8) in (let 
H12 \def (eq_ind T t3 (\lambda (t: T).(ty3 g c0 t0 t)) H1 t2 H8) in (eq_ind_r 
T t2 (\lambda (t: T).(ex3 T (\lambda (t5: T).(pc3 c0 (THead (Flat Cast) t5 
t2) (THead (Flat Cast) t4 t))) (\lambda (_: T).(ty3 g c0 t1 t2)) (\lambda 
(t5: T).(ty3 g c0 t2 t5)))) (let H13 \def (eq_ind T t0 (\lambda (t: T).((eq T 
t (THead (Flat Cast) t2 t1)) \to (ex3 T (\lambda (t5: T).(pc3 c0 (THead (Flat 
Cast) t5 t2) t2)) (\lambda (_: T).(ty3 g c0 t1 t2)) (\lambda (t5: T).(ty3 g 
c0 t2 t5))))) H11 t1 H7) in (let H14 \def (eq_ind T t0 (\lambda (t: T).(ty3 g 
c0 t t2)) H12 t1 H7) in (ex3_intro T (\lambda (t5: T).(pc3 c0 (THead (Flat 
Cast) t5 t2) (THead (Flat Cast) t4 t2))) (\lambda (_: T).(ty3 g c0 t1 t2)) 
(\lambda (t5: T).(ty3 g c0 t2 t5)) t4 (pc3_refl c0 (THead (Flat Cast) t4 t2)) 
H14 H10))) t3 H8))))))) H6))))))))))) c y x H0))) H)))))).
(* COMMENTS
Initial nodes: 2609
END *)

theorem tys3_gen_nil:
 \forall (g: G).(\forall (c: C).(\forall (u: T).((tys3 g c TNil u) \to (ex T 
(\lambda (u0: T).(ty3 g c u u0))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (H: (tys3 g c TNil 
u)).(insert_eq TList TNil (\lambda (t: TList).(tys3 g c t u)) (\lambda (_: 
TList).(ex T (\lambda (u0: T).(ty3 g c u u0)))) (\lambda (y: TList).(\lambda 
(H0: (tys3 g c y u)).(tys3_ind g c (\lambda (t: TList).(\lambda (t0: T).((eq 
TList t TNil) \to (ex T (\lambda (u0: T).(ty3 g c t0 u0)))))) (\lambda (u0: 
T).(\lambda (u1: T).(\lambda (H1: (ty3 g c u0 u1)).(\lambda (_: (eq TList 
TNil TNil)).(ex_intro T (\lambda (u2: T).(ty3 g c u0 u2)) u1 H1))))) (\lambda 
(t: T).(\lambda (u0: T).(\lambda (_: (ty3 g c t u0)).(\lambda (ts: 
TList).(\lambda (_: (tys3 g c ts u0)).(\lambda (_: (((eq TList ts TNil) \to 
(ex T (\lambda (u1: T).(ty3 g c u0 u1)))))).(\lambda (H4: (eq TList (TCons t 
ts) TNil)).(let H5 \def (eq_ind TList (TCons t ts) (\lambda (ee: 
TList).(match ee in TList return (\lambda (_: TList).Prop) with [TNil 
\Rightarrow False | (TCons _ _) \Rightarrow True])) I TNil H4) in (False_ind 
(ex T (\lambda (u1: T).(ty3 g c u0 u1))) H5))))))))) y u H0))) H)))).
(* COMMENTS
Initial nodes: 255
END *)

theorem tys3_gen_cons:
 \forall (g: G).(\forall (c: C).(\forall (ts: TList).(\forall (t: T).(\forall 
(u: T).((tys3 g c (TCons t ts) u) \to (land (ty3 g c t u) (tys3 g c ts 
u)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (ts: TList).(\lambda (t: T).(\lambda 
(u: T).(\lambda (H: (tys3 g c (TCons t ts) u)).(insert_eq TList (TCons t ts) 
(\lambda (t0: TList).(tys3 g c t0 u)) (\lambda (_: TList).(land (ty3 g c t u) 
(tys3 g c ts u))) (\lambda (y: TList).(\lambda (H0: (tys3 g c y u)).(tys3_ind 
g c (\lambda (t0: TList).(\lambda (t1: T).((eq TList t0 (TCons t ts)) \to 
(land (ty3 g c t t1) (tys3 g c ts t1))))) (\lambda (u0: T).(\lambda (u1: 
T).(\lambda (_: (ty3 g c u0 u1)).(\lambda (H2: (eq TList TNil (TCons t 
ts))).(let H3 \def (eq_ind TList TNil (\lambda (ee: TList).(match ee in TList 
return (\lambda (_: TList).Prop) with [TNil \Rightarrow True | (TCons _ _) 
\Rightarrow False])) I (TCons t ts) H2) in (False_ind (land (ty3 g c t u0) 
(tys3 g c ts u0)) H3)))))) (\lambda (t0: T).(\lambda (u0: T).(\lambda (H1: 
(ty3 g c t0 u0)).(\lambda (ts0: TList).(\lambda (H2: (tys3 g c ts0 
u0)).(\lambda (H3: (((eq TList ts0 (TCons t ts)) \to (land (ty3 g c t u0) 
(tys3 g c ts u0))))).(\lambda (H4: (eq TList (TCons t0 ts0) (TCons t 
ts))).(let H5 \def (f_equal TList T (\lambda (e: TList).(match e in TList 
return (\lambda (_: TList).T) with [TNil \Rightarrow t0 | (TCons t1 _) 
\Rightarrow t1])) (TCons t0 ts0) (TCons t ts) H4) in ((let H6 \def (f_equal 
TList TList (\lambda (e: TList).(match e in TList return (\lambda (_: 
TList).TList) with [TNil \Rightarrow ts0 | (TCons _ t1) \Rightarrow t1])) 
(TCons t0 ts0) (TCons t ts) H4) in (\lambda (H7: (eq T t0 t)).(let H8 \def 
(eq_ind TList ts0 (\lambda (t1: TList).((eq TList t1 (TCons t ts)) \to (land 
(ty3 g c t u0) (tys3 g c ts u0)))) H3 ts H6) in (let H9 \def (eq_ind TList 
ts0 (\lambda (t1: TList).(tys3 g c t1 u0)) H2 ts H6) in (let H10 \def (eq_ind 
T t0 (\lambda (t1: T).(ty3 g c t1 u0)) H1 t H7) in (conj (ty3 g c t u0) (tys3 
g c ts u0) H10 H9)))))) H5))))))))) y u H0))) H)))))).
(* COMMENTS
Initial nodes: 479
END *)

