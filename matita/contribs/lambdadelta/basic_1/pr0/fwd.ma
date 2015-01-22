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

include "Basic-1/pr0/props.ma".

theorem pr0_gen_sort:
 \forall (x: T).(\forall (n: nat).((pr0 (TSort n) x) \to (eq T x (TSort n))))
\def
 \lambda (x: T).(\lambda (n: nat).(\lambda (H: (pr0 (TSort n) x)).(insert_eq 
T (TSort n) (\lambda (t: T).(pr0 t x)) (\lambda (t: T).(eq T x t)) (\lambda 
(y: T).(\lambda (H0: (pr0 y x)).(pr0_ind (\lambda (t: T).(\lambda (t0: 
T).((eq T t (TSort n)) \to (eq T t0 t)))) (\lambda (t: T).(\lambda (H1: (eq T 
t (TSort n))).(let H2 \def (f_equal T T (\lambda (e: T).e) t (TSort n) H1) in 
(eq_ind_r T (TSort n) (\lambda (t0: T).(eq T t0 t0)) (refl_equal T (TSort n)) 
t H2)))) (\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (pr0 u1 u2)).(\lambda 
(_: (((eq T u1 (TSort n)) \to (eq T u2 u1)))).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (_: (pr0 t1 t2)).(\lambda (_: (((eq T t1 (TSort n)) \to (eq T t2 
t1)))).(\lambda (k: K).(\lambda (H5: (eq T (THead k u1 t1) (TSort n))).(let 
H6 \def (eq_ind T (THead k u1 t1) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) H5) in 
(False_ind (eq T (THead k u2 t2) (THead k u1 t1)) H6)))))))))))) (\lambda (u: 
T).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (pr0 v1 v2)).(\lambda (_: 
(((eq T v1 (TSort n)) \to (eq T v2 v1)))).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (_: (pr0 t1 t2)).(\lambda (_: (((eq T t1 (TSort n)) \to (eq T t2 
t1)))).(\lambda (H5: (eq T (THead (Flat Appl) v1 (THead (Bind Abst) u t1)) 
(TSort n))).(let H6 \def (eq_ind T (THead (Flat Appl) v1 (THead (Bind Abst) u 
t1)) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) I (TSort n) H5) in (False_ind (eq T (THead (Bind Abbr) v2 
t2) (THead (Flat Appl) v1 (THead (Bind Abst) u t1))) H6)))))))))))) (\lambda 
(b: B).(\lambda (_: (not (eq B b Abst))).(\lambda (v1: T).(\lambda (v2: 
T).(\lambda (_: (pr0 v1 v2)).(\lambda (_: (((eq T v1 (TSort n)) \to (eq T v2 
v1)))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (pr0 u1 u2)).(\lambda 
(_: (((eq T u1 (TSort n)) \to (eq T u2 u1)))).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (_: (pr0 t1 t2)).(\lambda (_: (((eq T t1 (TSort n)) \to (eq T t2 
t1)))).(\lambda (H8: (eq T (THead (Flat Appl) v1 (THead (Bind b) u1 t1)) 
(TSort n))).(let H9 \def (eq_ind T (THead (Flat Appl) v1 (THead (Bind b) u1 
t1)) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) I (TSort n) H8) in (False_ind (eq T (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t2)) (THead (Flat Appl) v1 (THead (Bind 
b) u1 t1))) H9))))))))))))))))) (\lambda (u1: T).(\lambda (u2: T).(\lambda 
(_: (pr0 u1 u2)).(\lambda (_: (((eq T u1 (TSort n)) \to (eq T u2 
u1)))).(\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (pr0 t1 t2)).(\lambda 
(_: (((eq T t1 (TSort n)) \to (eq T t2 t1)))).(\lambda (w: T).(\lambda (_: 
(subst0 O u2 t2 w)).(\lambda (H6: (eq T (THead (Bind Abbr) u1 t1) (TSort 
n))).(let H7 \def (eq_ind T (THead (Bind Abbr) u1 t1) (\lambda (ee: T).(match 
ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) 
H6) in (False_ind (eq T (THead (Bind Abbr) u2 w) (THead (Bind Abbr) u1 t1)) 
H7))))))))))))) (\lambda (b: B).(\lambda (_: (not (eq B b Abst))).(\lambda 
(t1: T).(\lambda (t2: T).(\lambda (_: (pr0 t1 t2)).(\lambda (_: (((eq T t1 
(TSort n)) \to (eq T t2 t1)))).(\lambda (u: T).(\lambda (H4: (eq T (THead 
(Bind b) u (lift (S O) O t1)) (TSort n))).(let H5 \def (eq_ind T (THead (Bind 
b) u (lift (S O) O t1)) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow True])) I (TSort n) H4) in (False_ind (eq T t2 
(THead (Bind b) u (lift (S O) O t1))) H5)))))))))) (\lambda (t1: T).(\lambda 
(t2: T).(\lambda (_: (pr0 t1 t2)).(\lambda (_: (((eq T t1 (TSort n)) \to (eq 
T t2 t1)))).(\lambda (u: T).(\lambda (H3: (eq T (THead (Flat Cast) u t1) 
(TSort n))).(let H4 \def (eq_ind T (THead (Flat Cast) u t1) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(TSort n) H3) in (False_ind (eq T t2 (THead (Flat Cast) u t1)) H4)))))))) y x 
H0))) H))).
(* COMMENTS
Initial nodes: 1045
END *)

theorem pr0_gen_lref:
 \forall (x: T).(\forall (n: nat).((pr0 (TLRef n) x) \to (eq T x (TLRef n))))
\def
 \lambda (x: T).(\lambda (n: nat).(\lambda (H: (pr0 (TLRef n) x)).(insert_eq 
T (TLRef n) (\lambda (t: T).(pr0 t x)) (\lambda (t: T).(eq T x t)) (\lambda 
(y: T).(\lambda (H0: (pr0 y x)).(pr0_ind (\lambda (t: T).(\lambda (t0: 
T).((eq T t (TLRef n)) \to (eq T t0 t)))) (\lambda (t: T).(\lambda (H1: (eq T 
t (TLRef n))).(let H2 \def (f_equal T T (\lambda (e: T).e) t (TLRef n) H1) in 
(eq_ind_r T (TLRef n) (\lambda (t0: T).(eq T t0 t0)) (refl_equal T (TLRef n)) 
t H2)))) (\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (pr0 u1 u2)).(\lambda 
(_: (((eq T u1 (TLRef n)) \to (eq T u2 u1)))).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (_: (pr0 t1 t2)).(\lambda (_: (((eq T t1 (TLRef n)) \to (eq T t2 
t1)))).(\lambda (k: K).(\lambda (H5: (eq T (THead k u1 t1) (TLRef n))).(let 
H6 \def (eq_ind T (THead k u1 t1) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n) H5) in 
(False_ind (eq T (THead k u2 t2) (THead k u1 t1)) H6)))))))))))) (\lambda (u: 
T).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (pr0 v1 v2)).(\lambda (_: 
(((eq T v1 (TLRef n)) \to (eq T v2 v1)))).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (_: (pr0 t1 t2)).(\lambda (_: (((eq T t1 (TLRef n)) \to (eq T t2 
t1)))).(\lambda (H5: (eq T (THead (Flat Appl) v1 (THead (Bind Abst) u t1)) 
(TLRef n))).(let H6 \def (eq_ind T (THead (Flat Appl) v1 (THead (Bind Abst) u 
t1)) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) I (TLRef n) H5) in (False_ind (eq T (THead (Bind Abbr) v2 
t2) (THead (Flat Appl) v1 (THead (Bind Abst) u t1))) H6)))))))))))) (\lambda 
(b: B).(\lambda (_: (not (eq B b Abst))).(\lambda (v1: T).(\lambda (v2: 
T).(\lambda (_: (pr0 v1 v2)).(\lambda (_: (((eq T v1 (TLRef n)) \to (eq T v2 
v1)))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (pr0 u1 u2)).(\lambda 
(_: (((eq T u1 (TLRef n)) \to (eq T u2 u1)))).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (_: (pr0 t1 t2)).(\lambda (_: (((eq T t1 (TLRef n)) \to (eq T t2 
t1)))).(\lambda (H8: (eq T (THead (Flat Appl) v1 (THead (Bind b) u1 t1)) 
(TLRef n))).(let H9 \def (eq_ind T (THead (Flat Appl) v1 (THead (Bind b) u1 
t1)) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) I (TLRef n) H8) in (False_ind (eq T (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t2)) (THead (Flat Appl) v1 (THead (Bind 
b) u1 t1))) H9))))))))))))))))) (\lambda (u1: T).(\lambda (u2: T).(\lambda 
(_: (pr0 u1 u2)).(\lambda (_: (((eq T u1 (TLRef n)) \to (eq T u2 
u1)))).(\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (pr0 t1 t2)).(\lambda 
(_: (((eq T t1 (TLRef n)) \to (eq T t2 t1)))).(\lambda (w: T).(\lambda (_: 
(subst0 O u2 t2 w)).(\lambda (H6: (eq T (THead (Bind Abbr) u1 t1) (TLRef 
n))).(let H7 \def (eq_ind T (THead (Bind Abbr) u1 t1) (\lambda (ee: T).(match 
ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n) 
H6) in (False_ind (eq T (THead (Bind Abbr) u2 w) (THead (Bind Abbr) u1 t1)) 
H7))))))))))))) (\lambda (b: B).(\lambda (_: (not (eq B b Abst))).(\lambda 
(t1: T).(\lambda (t2: T).(\lambda (_: (pr0 t1 t2)).(\lambda (_: (((eq T t1 
(TLRef n)) \to (eq T t2 t1)))).(\lambda (u: T).(\lambda (H4: (eq T (THead 
(Bind b) u (lift (S O) O t1)) (TLRef n))).(let H5 \def (eq_ind T (THead (Bind 
b) u (lift (S O) O t1)) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow True])) I (TLRef n) H4) in (False_ind (eq T t2 
(THead (Bind b) u (lift (S O) O t1))) H5)))))))))) (\lambda (t1: T).(\lambda 
(t2: T).(\lambda (_: (pr0 t1 t2)).(\lambda (_: (((eq T t1 (TLRef n)) \to (eq 
T t2 t1)))).(\lambda (u: T).(\lambda (H3: (eq T (THead (Flat Cast) u t1) 
(TLRef n))).(let H4 \def (eq_ind T (THead (Flat Cast) u t1) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(TLRef n) H3) in (False_ind (eq T t2 (THead (Flat Cast) u t1)) H4)))))))) y x 
H0))) H))).
(* COMMENTS
Initial nodes: 1045
END *)

theorem pr0_gen_abst:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Bind Abst) u1 
t1) x) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead (Bind 
Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr0 t1 t2)))))))
\def
 \lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (H: (pr0 (THead 
(Bind Abst) u1 t1) x)).(insert_eq T (THead (Bind Abst) u1 t1) (\lambda (t: 
T).(pr0 t x)) (\lambda (_: T).(ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 
u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2))))) (\lambda (y: 
T).(\lambda (H0: (pr0 y x)).(pr0_ind (\lambda (t: T).(\lambda (t0: T).((eq T 
t (THead (Bind Abst) u1 t1)) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T t0 (THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2))))))) (\lambda 
(t: T).(\lambda (H1: (eq T t (THead (Bind Abst) u1 t1))).(let H2 \def 
(f_equal T T (\lambda (e: T).e) t (THead (Bind Abst) u1 t1) H1) in (eq_ind_r 
T (THead (Bind Abst) u1 t1) (\lambda (t0: T).(ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T t0 (THead (Bind Abst) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 
t2))))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t2: T).(eq T (THead (Bind 
Abst) u1 t1) (THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2))) u1 t1 
(refl_equal T (THead (Bind Abst) u1 t1)) (pr0_refl u1) (pr0_refl t1)) t 
H2)))) (\lambda (u0: T).(\lambda (u2: T).(\lambda (H1: (pr0 u0 u2)).(\lambda 
(H2: (((eq T u0 (THead (Bind Abst) u1 t1)) \to (ex3_2 T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T u2 (THead (Bind Abst) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 
t2))))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H3: (pr0 t0 
t2)).(\lambda (H4: (((eq T t0 (THead (Bind Abst) u1 t1)) \to (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abst) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))))))).(\lambda (k: K).(\lambda (H5: (eq T (THead k u0 t0) 
(THead (Bind Abst) u1 t1))).(let H6 \def (f_equal T K (\lambda (e: T).(match 
e in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k0 _ _) \Rightarrow k0])) (THead k u0 t0) (THead (Bind 
Abst) u1 t1) H5) in ((let H7 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow u0 | (TLRef _) 
\Rightarrow u0 | (THead _ t _) \Rightarrow t])) (THead k u0 t0) (THead (Bind 
Abst) u1 t1) H5) in ((let H8 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | (TLRef _) 
\Rightarrow t0 | (THead _ _ t) \Rightarrow t])) (THead k u0 t0) (THead (Bind 
Abst) u1 t1) H5) in (\lambda (H9: (eq T u0 u1)).(\lambda (H10: (eq K k (Bind 
Abst))).(eq_ind_r K (Bind Abst) (\lambda (k0: K).(ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T (THead k0 u2 t2) (THead (Bind Abst) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))))) (let H11 \def (eq_ind T t0 (\lambda (t: T).((eq T t (THead 
(Bind Abst) u1 t1)) \to (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 
(THead (Bind Abst) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) 
(\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))))) H4 t1 H8) in (let H12 \def 
(eq_ind T t0 (\lambda (t: T).(pr0 t t2)) H3 t1 H8) in (let H13 \def (eq_ind T 
u0 (\lambda (t: T).((eq T t (THead (Bind Abst) u1 t1)) \to (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T u2 (THead (Bind Abst) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))))) H2 u1 H9) in (let H14 \def (eq_ind T u0 (\lambda (t: 
T).(pr0 t u2)) H1 u1 H9) in (ex3_2_intro T T (\lambda (u3: T).(\lambda (t3: 
T).(eq T (THead (Bind Abst) u2 t2) (THead (Bind Abst) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3))) u2 t2 (refl_equal T (THead (Bind Abst) u2 t2)) H14 H12))))) k H10)))) 
H7)) H6)))))))))))) (\lambda (u: T).(\lambda (v1: T).(\lambda (v2: 
T).(\lambda (_: (pr0 v1 v2)).(\lambda (_: (((eq T v1 (THead (Bind Abst) u1 
t1)) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T v2 (THead (Bind 
Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr0 t1 t2))))))).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (_: (pr0 t0 t2)).(\lambda (_: (((eq T t0 (THead (Bind Abst) u1 
t1)) \to (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3))))))).(\lambda (H5: (eq T (THead (Flat Appl) 
v1 (THead (Bind Abst) u t0)) (THead (Bind Abst) u1 t1))).(let H6 \def (eq_ind 
T (THead (Flat Appl) v1 (THead (Bind Abst) u t0)) (\lambda (ee: T).(match ee 
in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef 
_) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind Abst) u1 t1) H5) in (False_ind (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) v2 t2) (THead (Bind Abst) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) H6)))))))))))) (\lambda (b: B).(\lambda 
(_: (not (eq B b Abst))).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (pr0 
v1 v2)).(\lambda (_: (((eq T v1 (THead (Bind Abst) u1 t1)) \to (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T v2 (THead (Bind Abst) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: 
T).(pr0 t1 t2))))))).(\lambda (u0: T).(\lambda (u2: T).(\lambda (_: (pr0 u0 
u2)).(\lambda (_: (((eq T u0 (THead (Bind Abst) u1 t1)) \to (ex3_2 T T 
(\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead (Bind Abst) u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t2: 
T).(pr0 t1 t2))))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 
t2)).(\lambda (_: (((eq T t0 (THead (Bind Abst) u1 t1)) \to (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abst) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))))))).(\lambda (H8: (eq T (THead (Flat Appl) v1 (THead (Bind 
b) u0 t0)) (THead (Bind Abst) u1 t1))).(let H9 \def (eq_ind T (THead (Flat 
Appl) v1 (THead (Bind b) u0 t0)) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind Abst) u1 t1) H8) in (False_ind (ex3_2 T T (\lambda 
(u3: T).(\lambda (t3: T).(eq T (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t2)) (THead (Bind Abst) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) 
H9))))))))))))))))) (\lambda (u0: T).(\lambda (u2: T).(\lambda (_: (pr0 u0 
u2)).(\lambda (_: (((eq T u0 (THead (Bind Abst) u1 t1)) \to (ex3_2 T T 
(\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead (Bind Abst) u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t2: 
T).(pr0 t1 t2))))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 
t2)).(\lambda (_: (((eq T t0 (THead (Bind Abst) u1 t1)) \to (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abst) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))))))).(\lambda (w: T).(\lambda (_: (subst0 O u2 t2 
w)).(\lambda (H6: (eq T (THead (Bind Abbr) u0 t0) (THead (Bind Abst) u1 
t1))).(let H7 \def (eq_ind T (THead (Bind Abbr) u0 t0) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K 
return (\lambda (_: K).Prop) with [(Bind b) \Rightarrow (match b in B return 
(\lambda (_: B).Prop) with [Abbr \Rightarrow True | Abst \Rightarrow False | 
Void \Rightarrow False]) | (Flat _) \Rightarrow False])])) I (THead (Bind 
Abst) u1 t1) H6) in (False_ind (ex3_2 T T (\lambda (u3: T).(\lambda (t3: 
T).(eq T (THead (Bind Abbr) u2 w) (THead (Bind Abst) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) H7))))))))))))) (\lambda (b: B).(\lambda (H1: (not (eq B b 
Abst))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 t2)).(\lambda 
(H3: (((eq T t0 (THead (Bind Abst) u1 t1)) \to (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abst) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3))))))).(\lambda (u: T).(\lambda (H4: (eq T (THead (Bind b) u (lift (S O) O 
t0)) (THead (Bind Abst) u1 t1))).(let H5 \def (f_equal T B (\lambda (e: 
T).(match e in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow b | 
(TLRef _) \Rightarrow b | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow 
b])])) (THead (Bind b) u (lift (S O) O t0)) (THead (Bind Abst) u1 t1) H4) in 
((let H6 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow u | (TLRef _) \Rightarrow u | (THead _ t _) 
\Rightarrow t])) (THead (Bind b) u (lift (S O) O t0)) (THead (Bind Abst) u1 
t1) H4) in ((let H7 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map (f: ((nat 
\to nat))) (d: nat) (t: T) on t: T \def (match t with [(TSort n) \Rightarrow 
(TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with [true 
\Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t3) \Rightarrow 
(THead k (lref_map f d u0) (lref_map f (s k d) t3))]) in lref_map) (\lambda 
(x0: nat).(plus x0 (S O))) O t0) | (TLRef _) \Rightarrow ((let rec lref_map 
(f: ((nat \to nat))) (d: nat) (t: T) on t: T \def (match t with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t3) 
\Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t3))]) in 
lref_map) (\lambda (x0: nat).(plus x0 (S O))) O t0) | (THead _ _ t) 
\Rightarrow t])) (THead (Bind b) u (lift (S O) O t0)) (THead (Bind Abst) u1 
t1) H4) in (\lambda (_: (eq T u u1)).(\lambda (H9: (eq B b Abst)).(let H10 
\def (eq_ind B b (\lambda (b0: B).(not (eq B b0 Abst))) H1 Abst H9) in (let 
H11 \def (eq_ind_r T t1 (\lambda (t: T).((eq T t0 (THead (Bind Abst) u1 t)) 
\to (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abst) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t t3)))))) H3 (lift (S O) O t0) H7) in (eq_ind T 
(lift (S O) O t0) (\lambda (t: T).(ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t t3))))) (let H12 
\def (match (H10 (refl_equal B Abst)) in False return (\lambda (_: 
False).(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 (lift (S O) O t0) t3))))) with []) in H12) t1 
H7)))))) H6)) H5)))))))))) (\lambda (t0: T).(\lambda (t2: T).(\lambda (_: 
(pr0 t0 t2)).(\lambda (_: (((eq T t0 (THead (Bind Abst) u1 t1)) \to (ex3_2 T 
T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abst) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))))))).(\lambda (u: T).(\lambda (H3: (eq T (THead (Flat Cast) u 
t0) (THead (Bind Abst) u1 t1))).(let H4 \def (eq_ind T (THead (Flat Cast) u 
t0) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind Abst) u1 
t1) H3) in (False_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 
(THead (Bind Abst) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) H4)))))))) y x H0))) H)))).
(* COMMENTS
Initial nodes: 2838
END *)

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
(Flat Appl) u1 t1) x)).(insert_eq T (THead (Flat Appl) u1 t1) (\lambda (t: 
T).(pr0 t x)) (\lambda (_: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
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
T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))))))) (\lambda (y: 
T).(\lambda (H0: (pr0 y x)).(pr0_ind (\lambda (t: T).(\lambda (t0: T).((eq T 
t (THead (Flat Appl) u1 t1)) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T t0 (THead (Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (ex4_4 T T T 
T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t2: T).(eq T t0 (THead (Bind Abbr) u2 t2)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (v2: T).(\lambda (t2: T).(eq T 
t0 (THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O u2) t2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(\lambda (_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 
v2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))))))))) (\lambda (t: 
T).(\lambda (H1: (eq T t (THead (Flat Appl) u1 t1))).(let H2 \def (f_equal T 
T (\lambda (e: T).e) t (THead (Flat Appl) u1 t1) H1) in (eq_ind_r T (THead 
(Flat Appl) u1 t1) (\lambda (t0: T).(or3 (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T t0 (THead (Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (ex4_4 T T T 
T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t2: T).(eq T t0 (THead (Bind Abbr) u2 t2)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (v2: T).(\lambda (t2: T).(eq T 
t0 (THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O u2) t2))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(\lambda (_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 
v2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))))))) (or3_intro0 (ex3_2 T 
T (\lambda (u2: T).(\lambda (t2: T).(eq T (THead (Flat Appl) u1 t1) (THead 
(Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t2: T).(eq T (THead (Flat Appl) u1 t1) (THead (Bind Abbr) u2 t2)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 
u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t2: 
T).(pr0 z1 t2)))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(v2: T).(\lambda (t2: T).(eq T (THead (Flat Appl) u1 t1) (THead (Bind b) v2 
(THead (Flat Appl) (lift (S O) O u2) t2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t2: T).(pr0 z1 t2)))))))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T (THead (Flat Appl) u1 t1) (THead (Flat Appl) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 
t2))) u1 t1 (refl_equal T (THead (Flat Appl) u1 t1)) (pr0_refl u1) (pr0_refl 
t1))) t H2)))) (\lambda (u0: T).(\lambda (u2: T).(\lambda (H1: (pr0 u0 
u2)).(\lambda (H2: (((eq T u0 (THead (Flat Appl) u1 t1)) \to (or3 (ex3_2 T T 
(\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t2: 
T).(pr0 t1 t2)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead (Bind 
Abbr) u3 t2)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t2: T).(pr0 z1 t2)))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (v2: T).(\lambda (t2: T).(eq T u2 (THead (Bind b) v2 (THead 
(Flat Appl) (lift (S O) O u3) t2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t2: T).(pr0 z1 t2)))))))))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda 
(H3: (pr0 t0 t2)).(\lambda (H4: (((eq T t0 (THead (Flat Appl) u1 t1)) \to 
(or3 (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) 
u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t3: 
T).(eq T t2 (THead (Bind Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (v2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
b) v2 (THead (Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda 
(_: T).(pr0 u1 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))))))))).(\lambda (k: K).(\lambda (H5: (eq 
T (THead k u0 t0) (THead (Flat Appl) u1 t1))).(let H6 \def (f_equal T K 
(\lambda (e: T).(match e in T return (\lambda (_: T).K) with [(TSort _) 
\Rightarrow k | (TLRef _) \Rightarrow k | (THead k0 _ _) \Rightarrow k0])) 
(THead k u0 t0) (THead (Flat Appl) u1 t1) H5) in ((let H7 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead _ t _) \Rightarrow t])) 
(THead k u0 t0) (THead (Flat Appl) u1 t1) H5) in ((let H8 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t) \Rightarrow t])) 
(THead k u0 t0) (THead (Flat Appl) u1 t1) H5) in (\lambda (H9: (eq T u0 
u1)).(\lambda (H10: (eq K k (Flat Appl))).(eq_ind_r K (Flat Appl) (\lambda 
(k0: K).(or3 (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T (THead k0 u2 
t2) (THead (Flat Appl) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 
u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (t3: T).(eq T (THead k0 u2 t2) (THead (Bind Abbr) u3 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 
u3))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(v2: T).(\lambda (t3: T).(eq T (THead k0 u2 t2) (THead (Bind b) v2 (THead 
(Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3)))))))))) (let H11 \def (eq_ind T t0 (\lambda (t: T).((eq 
T t (THead (Flat Appl) u1 t1)) \to (or3 (ex3_2 T T (\lambda (u3: T).(\lambda 
(t3: T).(eq T t2 (THead (Flat Appl) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T 
T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u3 t3)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))))) (\lambda 
(_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) 
(ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: 
B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (v2: T).(\lambda (t3: T).(eq T 
t2 (THead (Bind b) v2 (THead (Flat Appl) (lift (S O) O u3) t3))))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: 
T).(\lambda (_: T).(pr0 u1 u3))))))) (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 
v2))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3))))))))))) H4 t1 H8) in (let 
H12 \def (eq_ind T t0 (\lambda (t: T).(pr0 t t2)) H3 t1 H8) in (let H13 \def 
(eq_ind T u0 (\lambda (t: T).((eq T t (THead (Flat Appl) u1 t1)) \to (or3 
(ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T u2 (THead (Flat Appl) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t3: 
T).(eq T u2 (THead (Bind Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (v2: T).(\lambda (t3: T).(eq T u2 (THead (Bind 
b) v2 (THead (Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda 
(_: T).(pr0 u1 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3))))))))))) H2 u1 H9) in (let H14 \def (eq_ind 
T u0 (\lambda (t: T).(pr0 t u2)) H1 u1 H9) in (or3_intro0 (ex3_2 T T (\lambda 
(u3: T).(\lambda (t3: T).(eq T (THead (Flat Appl) u2 t2) (THead (Flat Appl) 
u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t3: 
T).(eq T (THead (Flat Appl) u2 t2) (THead (Bind Abbr) u3 t3)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 
t3)))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (v2: T).(\lambda 
(t3: T).(eq T (THead (Flat Appl) u2 t2) (THead (Bind b) v2 (THead (Flat Appl) 
(lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 u3))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 
t3)))))))) (ex3_2_intro T T (\lambda (u3: T).(\lambda (t3: T).(eq T (THead 
(Flat Appl) u2 t2) (THead (Flat Appl) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))) u2 t2 
(refl_equal T (THead (Flat Appl) u2 t2)) H14 H12)))))) k H10)))) H7)) 
H6)))))))))))) (\lambda (u: T).(\lambda (v1: T).(\lambda (v2: T).(\lambda 
(H1: (pr0 v1 v2)).(\lambda (H2: (((eq T v1 (THead (Flat Appl) u1 t1)) \to 
(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T v2 (THead (Flat Appl) 
u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr0 t1 t2)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t2: 
T).(eq T v2 (THead (Bind Abbr) u2 t2)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (v3: T).(\lambda (t2: T).(eq T v2 (THead (Bind 
b) v3 (THead (Flat Appl) (lift (S O) O u2) t2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda 
(_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (t2: T).(pr0 z1 t2)))))))))))).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (H3: (pr0 t0 t2)).(\lambda (H4: (((eq T t0 (THead (Flat Appl) u1 
t1)) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (v3: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
b) v3 (THead (Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda 
(_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))))))))).(\lambda (H5: (eq T (THead (Flat 
Appl) v1 (THead (Bind Abst) u t0)) (THead (Flat Appl) u1 t1))).(let H6 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow v1 | (TLRef _) \Rightarrow v1 | (THead _ t _) 
\Rightarrow t])) (THead (Flat Appl) v1 (THead (Bind Abst) u t0)) (THead (Flat 
Appl) u1 t1) H5) in ((let H7 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow (THead (Bind Abst) u 
t0) | (TLRef _) \Rightarrow (THead (Bind Abst) u t0) | (THead _ _ t) 
\Rightarrow t])) (THead (Flat Appl) v1 (THead (Bind Abst) u t0)) (THead (Flat 
Appl) u1 t1) H5) in (\lambda (H8: (eq T v1 u1)).(let H9 \def (eq_ind T v1 
(\lambda (t: T).((eq T t (THead (Flat Appl) u1 t1)) \to (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T v2 (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T v2 (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (v3: T).(\lambda (t3: T).(eq T v2 (THead (Bind b) v3 (THead 
(Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3))))))))))) H2 u1 H8) in (let H10 \def (eq_ind T v1 
(\lambda (t: T).(pr0 t v2)) H1 u1 H8) in (let H11 \def (eq_ind_r T t1 
(\lambda (t: T).((eq T t0 (THead (Flat Appl) u1 t)) \to (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(eq T t (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (v3: T).(\lambda (t3: T).(eq T t2 (THead (Bind b) v3 (THead 
(Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3))))))))))) H4 (THead (Bind Abst) u t0) H7) in (let H12 
\def (eq_ind_r T t1 (\lambda (t: T).((eq T u1 (THead (Flat Appl) u1 t)) \to 
(or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T v2 (THead (Flat Appl) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T v2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (v3: T).(\lambda (t3: T).(eq T v2 (THead (Bind 
b) v3 (THead (Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda 
(_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3))))))))))) H9 (THead (Bind Abst) u t0) H7) in 
(eq_ind T (THead (Bind Abst) u t0) (\lambda (t: T).(or3 (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) v2 t2) (THead (Flat Appl) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T (THead (Bind Abbr) v2 t2) (THead (Bind Abbr) u2 t3)))))) (\lambda 
(_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) 
(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 
t3)))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(eq T t (THead (Bind b) y1 z1)))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (v3: T).(\lambda 
(t3: T).(eq T (THead (Bind Abbr) v2 t2) (THead (Bind b) v3 (THead (Flat Appl) 
(lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 u2))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 
t3)))))))))) (or3_intro1 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
(THead (Bind Abbr) v2 t2) (THead (Flat Appl) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 (THead 
(Bind Abst) u t0) t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) u t0) (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) v2 t2) (THead (Bind Abbr) u2 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind Abst) u t0) (THead 
(Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (v3: T).(\lambda (t3: T).(eq T (THead (Bind 
Abbr) v2 t2) (THead (Bind b) v3 (THead (Flat Appl) (lift (S O) O u2) 
t3))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda 
(y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (v3: T).(\lambda (_: T).(pr0 
y1 v3))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))))) (ex4_4_intro T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind Abst) u t0) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) 
v2 t2) (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3))))) u t0 v2 t2 
(refl_equal T (THead (Bind Abst) u t0)) (refl_equal T (THead (Bind Abbr) v2 
t2)) H10 H3)) t1 H7))))))) H6)))))))))))) (\lambda (b: B).(\lambda (H1: (not 
(eq B b Abst))).(\lambda (v1: T).(\lambda (v2: T).(\lambda (H2: (pr0 v1 
v2)).(\lambda (H3: (((eq T v1 (THead (Flat Appl) u1 t1)) \to (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T v2 (THead (Flat Appl) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: 
T).(pr0 t1 t2)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t2: T).(eq T v2 (THead (Bind 
Abbr) u2 t2)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t2: T).(pr0 z1 t2)))))) (ex6_6 B T T T T T (\lambda (b0: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (v3: T).(\lambda (t2: T).(eq T v2 (THead (Bind b0) v3 (THead 
(Flat Appl) (lift (S O) O u2) t2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t2: T).(pr0 z1 t2)))))))))))).(\lambda (u0: T).(\lambda (u2: T).(\lambda 
(H4: (pr0 u0 u2)).(\lambda (H5: (((eq T u0 (THead (Flat Appl) u1 t1)) \to 
(or3 (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead (Flat Appl) 
u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: 
T).(\lambda (t2: T).(pr0 t1 t2)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t2: 
T).(eq T u2 (THead (Bind Abbr) u3 t2)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))) (ex6_6 B T T T T T 
(\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (v3: T).(\lambda (t2: T).(eq T u2 (THead (Bind 
b0) v3 (THead (Flat Appl) (lift (S O) O u3) t2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda 
(_: T).(pr0 u1 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (t2: T).(pr0 z1 t2)))))))))))).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (H6: (pr0 t0 t2)).(\lambda (H7: (((eq T t0 (THead (Flat Appl) u1 
t1)) \to (or3 (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Appl) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(t3: T).(eq T t2 (THead (Bind Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (v3: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
b0) v3 (THead (Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda 
(_: T).(pr0 u1 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))))))))).(\lambda (H8: (eq T (THead (Flat 
Appl) v1 (THead (Bind b) u0 t0)) (THead (Flat Appl) u1 t1))).(let H9 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow v1 | (TLRef _) \Rightarrow v1 | (THead _ t _) 
\Rightarrow t])) (THead (Flat Appl) v1 (THead (Bind b) u0 t0)) (THead (Flat 
Appl) u1 t1) H8) in ((let H10 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow (THead (Bind b) u0 t0) 
| (TLRef _) \Rightarrow (THead (Bind b) u0 t0) | (THead _ _ t) \Rightarrow 
t])) (THead (Flat Appl) v1 (THead (Bind b) u0 t0)) (THead (Flat Appl) u1 t1) 
H8) in (\lambda (H11: (eq T v1 u1)).(let H12 \def (eq_ind T v1 (\lambda (t: 
T).((eq T t (THead (Flat Appl) u1 t1)) \to (or3 (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T v2 (THead (Flat Appl) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t3: T).(eq T v2 (THead (Bind 
Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b0: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (v3: T).(\lambda (t3: T).(eq T v2 (THead (Bind b0) v3 (THead 
(Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3))))))))))) H3 u1 H11) in (let H13 \def (eq_ind T v1 
(\lambda (t: T).(pr0 t v2)) H2 u1 H11) in (let H14 \def (eq_ind_r T t1 
(\lambda (t: T).((eq T t0 (THead (Flat Appl) u1 t)) \to (or3 (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(eq T t (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b0: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t (THead (Bind 
b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (v3: T).(\lambda (t3: T).(eq T t2 (THead (Bind b0) v3 (THead 
(Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3))))))))))) H7 (THead (Bind b) u0 t0) H10) in (let H15 \def 
(eq_ind_r T t1 (\lambda (t: T).((eq T u0 (THead (Flat Appl) u1 t)) \to (or3 
(ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T u2 (THead (Flat Appl) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t (THead (Bind Abst) y1 
z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t3: 
T).(eq T u2 (THead (Bind Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t 
(THead (Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (v3: T).(\lambda (t3: T).(eq T u2 (THead (Bind 
b0) v3 (THead (Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda 
(_: T).(pr0 u1 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3))))))))))) H5 (THead (Bind b) u0 t0) H10) in 
(let H16 \def (eq_ind_r T t1 (\lambda (t: T).((eq T u1 (THead (Flat Appl) u1 
t)) \to (or3 (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T v2 (THead 
(Flat Appl) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(t3: T).(eq T v2 (THead (Bind Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t 
(THead (Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (v3: T).(\lambda (t3: T).(eq T v2 (THead (Bind 
b0) v3 (THead (Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda 
(_: T).(pr0 u1 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (v3: T).(\lambda (_: T).(pr0 y1 v3))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3))))))))))) H12 (THead (Bind b) u0 t0) H10) in 
(eq_ind T (THead (Bind b) u0 t0) (\lambda (t: T).(or3 (ex3_2 T T (\lambda 
(u3: T).(\lambda (t3: T).(eq T (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t2)) (THead (Flat Appl) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t t3)))) (ex4_4 T T T 
T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t 
(THead (Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (t3: T).(eq T (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O 
v2) t2)) (THead (Bind Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t 
(THead (Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (v3: T).(\lambda (t3: T).(eq T (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t2)) (THead (Bind b0) v3 (THead (Flat 
Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 u3))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 
t3)))))))))) (or3_intro2 (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t2)) (THead (Flat 
Appl) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 (THead (Bind b) u0 t0) t3)))) (ex4_4 T T T T 
(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T 
(THead (Bind b) u0 t0) (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t2)) (THead (Bind Abbr) u3 t3)))))) 
(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 
u3))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: 
T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b0: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind b) u0 t0) (THead 
(Bind b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (v3: T).(\lambda (t3: T).(eq T (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t2)) (THead (Bind b0) v3 (THead (Flat 
Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 u3))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 
t3)))))))) (ex6_6_intro B T T T T T (\lambda (b0: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b0 
Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T (THead (Bind b) u0 t0) (THead (Bind 
b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u3: T).(\lambda (v3: T).(\lambda (t3: T).(eq T (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t2)) (THead (Bind b0) v3 (THead (Flat Appl) 
(lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 u3))))))) 
(\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(v3: T).(\lambda (_: T).(pr0 y1 v3))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 
t3))))))) b u0 t0 v2 u2 t2 H1 (refl_equal T (THead (Bind b) u0 t0)) 
(refl_equal T (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t2))) 
H13 H4 H6)) t1 H10)))))))) H9))))))))))))))))) (\lambda (u0: T).(\lambda (u2: 
T).(\lambda (_: (pr0 u0 u2)).(\lambda (_: (((eq T u0 (THead (Flat Appl) u1 
t1)) \to (or3 (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead 
(Flat Appl) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(t2: T).(eq T u2 (THead (Bind Abbr) u3 t2)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t2: T).(pr0 z1 t2)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (v2: T).(\lambda (t2: T).(eq T u2 (THead (Bind 
b) v2 (THead (Flat Appl) (lift (S O) O u3) t2))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda 
(_: T).(pr0 u1 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (t2: T).(pr0 z1 t2)))))))))))).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (_: (pr0 t0 t2)).(\lambda (_: (((eq T t0 (THead (Flat Appl) u1 
t1)) \to (or3 (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Appl) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(t3: T).(eq T t2 (THead (Bind Abbr) u3 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u3: T).(\lambda (v2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
b) v2 (THead (Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda 
(_: T).(pr0 u1 u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))))))))).(\lambda (w: T).(\lambda (_: 
(subst0 O u2 t2 w)).(\lambda (H6: (eq T (THead (Bind Abbr) u0 t0) (THead 
(Flat Appl) u1 t1))).(let H7 \def (eq_ind T (THead (Bind Abbr) u0 t0) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | 
(Flat _) \Rightarrow False])])) I (THead (Flat Appl) u1 t1) H6) in (False_ind 
(or3 (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) u2 
w) (THead (Flat Appl) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 
u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead 
(Bind Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) u2 w) (THead (Bind Abbr) u3 
t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B 
b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind b) y1 z1)))))))) 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (u3: T).(\lambda 
(v2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) u2 w) (THead (Bind b) v2 
(THead (Flat Appl) (lift (S O) O u3) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u3: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u3))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3))))))))) H7))))))))))))) (\lambda (b: B).(\lambda (_: (not 
(eq B b Abst))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 
t2)).(\lambda (_: (((eq T t0 (THead (Flat Appl) u1 t1)) \to (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b0: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (v2: T).(\lambda (t3: T).(eq T t2 (THead (Bind b0) v2 (THead 
(Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3)))))))))))).(\lambda (u: T).(\lambda (H4: (eq T (THead 
(Bind b) u (lift (S O) O t0)) (THead (Flat Appl) u1 t1))).(let H5 \def 
(eq_ind T (THead (Bind b) u (lift (S O) O t0)) (\lambda (ee: T).(match ee in 
T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow 
False])])) I (THead (Flat Appl) u1 t1) H4) in (False_ind (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b0: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b0 Abst)))))))) (\lambda (b0: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b0) y1 z1)))))))) (\lambda (b0: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (v2: T).(\lambda (t3: T).(eq T t2 (THead (Bind b0) v2 (THead 
(Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3))))))))) H5)))))))))) (\lambda (t0: T).(\lambda (t2: 
T).(\lambda (_: (pr0 t0 t2)).(\lambda (_: (((eq T t0 (THead (Flat Appl) u1 
t1)) \to (or3 (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
Abst) y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 
(THead (Bind b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (v2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
b) v2 (THead (Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda 
(_: T).(pr0 u1 u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) 
(\lambda (_: B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))))))))).(\lambda (u: T).(\lambda (H3: (eq 
T (THead (Flat Cast) u t0) (THead (Flat Appl) u1 t1))).(let H4 \def (eq_ind T 
(THead (Flat Cast) u t0) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow False | (Flat f) \Rightarrow (match f in F return 
(\lambda (_: F).Prop) with [Appl \Rightarrow False | Cast \Rightarrow 
True])])])) I (THead (Flat Appl) u1 t1) H3) in (False_ind (or3 (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Appl) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))) (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(eq T t1 (THead (Bind Abst) y1 z1)))))) (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr0 u1 u2))))) (\lambda (_: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (t3: T).(pr0 z1 t3)))))) (ex6_6 B T T T T T (\lambda (b: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(_: T).(not (eq B b Abst)))))))) (\lambda (b: B).(\lambda (y1: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(eq T t1 (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (v2: T).(\lambda (t3: T).(eq T t2 (THead (Bind b) v2 (THead 
(Flat Appl) (lift (S O) O u2) t3))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(\lambda (_: T).(pr0 u1 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (v2: T).(\lambda (_: T).(pr0 y1 v2))))))) (\lambda (_: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda 
(t3: T).(pr0 z1 t3))))))))) H4)))))))) y x H0))) H)))).
(* COMMENTS
Initial nodes: 12299
END *)

theorem pr0_gen_cast:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Flat Cast) u1 
t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 x)))))
\def
 \lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (H: (pr0 (THead 
(Flat Cast) u1 t1) x)).(insert_eq T (THead (Flat Cast) u1 t1) (\lambda (t: 
T).(pr0 t x)) (\lambda (_: T).(or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 
u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 x))) 
(\lambda (y: T).(\lambda (H0: (pr0 y x)).(pr0_ind (\lambda (t: T).(\lambda 
(t0: T).((eq T t (THead (Flat Cast) u1 t1)) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T t0 (THead (Flat Cast) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 
t2)))) (pr0 t1 t0))))) (\lambda (t: T).(\lambda (H1: (eq T t (THead (Flat 
Cast) u1 t1))).(let H2 \def (f_equal T T (\lambda (e: T).e) t (THead (Flat 
Cast) u1 t1) H1) in (eq_ind_r T (THead (Flat Cast) u1 t1) (\lambda (t0: 
T).(or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Flat 
Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 t0))) (or_introl (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T (THead (Flat Cast) u1 t1) (THead 
(Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (THead (Flat Cast) u1 t1)) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t2: T).(eq T (THead (Flat Cast) 
u1 t1) (THead (Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 
u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2))) u1 t1 (refl_equal T 
(THead (Flat Cast) u1 t1)) (pr0_refl u1) (pr0_refl t1))) t H2)))) (\lambda 
(u0: T).(\lambda (u2: T).(\lambda (H1: (pr0 u0 u2)).(\lambda (H2: (((eq T u0 
(THead (Flat Cast) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t2: 
T).(eq T u2 (THead (Flat Cast) u3 t2)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 
u2))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H3: (pr0 t0 t2)).(\lambda 
(H4: (((eq T t0 (THead (Flat Cast) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 t2))))).(\lambda (k: K).(\lambda (H5: (eq T (THead k u0 t0) 
(THead (Flat Cast) u1 t1))).(let H6 \def (f_equal T K (\lambda (e: T).(match 
e in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k0 _ _) \Rightarrow k0])) (THead k u0 t0) (THead (Flat 
Cast) u1 t1) H5) in ((let H7 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow u0 | (TLRef _) 
\Rightarrow u0 | (THead _ t _) \Rightarrow t])) (THead k u0 t0) (THead (Flat 
Cast) u1 t1) H5) in ((let H8 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | (TLRef _) 
\Rightarrow t0 | (THead _ _ t) \Rightarrow t])) (THead k u0 t0) (THead (Flat 
Cast) u1 t1) H5) in (\lambda (H9: (eq T u0 u1)).(\lambda (H10: (eq K k (Flat 
Cast))).(eq_ind_r K (Flat Cast) (\lambda (k0: K).(or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T (THead k0 u2 t2) (THead (Flat Cast) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))) (pr0 t1 (THead k0 u2 t2)))) (let H11 \def (eq_ind T t0 
(\lambda (t: T).((eq T t (THead (Flat Cast) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))) (pr0 t1 t2)))) H4 t1 H8) in (let H12 \def (eq_ind T t0 
(\lambda (t: T).(pr0 t t2)) H3 t1 H8) in (let H13 \def (eq_ind T u0 (\lambda 
(t: T).((eq T t (THead (Flat Cast) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T u2 (THead (Flat Cast) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 u2)))) H2 u1 H9) in (let H14 \def (eq_ind T u0 (\lambda (t: 
T).(pr0 t u2)) H1 u1 H9) in (or_introl (ex3_2 T T (\lambda (u3: T).(\lambda 
(t3: T).(eq T (THead (Flat Cast) u2 t2) (THead (Flat Cast) u3 t3)))) (\lambda 
(u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 
t1 t3)))) (pr0 t1 (THead (Flat Cast) u2 t2)) (ex3_2_intro T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T (THead (Flat Cast) u2 t2) (THead (Flat Cast) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3))) u2 t2 (refl_equal T (THead (Flat Cast) u2 
t2)) H14 H12)))))) k H10)))) H7)) H6)))))))))))) (\lambda (u: T).(\lambda 
(v1: T).(\lambda (v2: T).(\lambda (_: (pr0 v1 v2)).(\lambda (_: (((eq T v1 
(THead (Flat Cast) u1 t1)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T v2 (THead (Flat Cast) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 
v2))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 t2)).(\lambda 
(_: (((eq T t0 (THead (Flat Cast) u1 t1)) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 t2))))).(\lambda (H5: (eq T (THead (Flat Appl) v1 (THead (Bind 
Abst) u t0)) (THead (Flat Cast) u1 t1))).(let H6 \def (eq_ind T (THead (Flat 
Appl) v1 (THead (Bind Abst) u t0)) (\lambda (ee: T).(match ee in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat f) \Rightarrow (match f 
in F return (\lambda (_: F).Prop) with [Appl \Rightarrow True | Cast 
\Rightarrow False])])])) I (THead (Flat Cast) u1 t1) H5) in (False_ind (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) v2 t2) 
(THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (THead (Bind Abbr) v2 
t2))) H6)))))))))))) (\lambda (b: B).(\lambda (_: (not (eq B b 
Abst))).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (pr0 v1 v2)).(\lambda 
(_: (((eq T v1 (THead (Flat Cast) u1 t1)) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T v2 (THead (Flat Cast) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 
t2)))) (pr0 t1 v2))))).(\lambda (u0: T).(\lambda (u2: T).(\lambda (_: (pr0 u0 
u2)).(\lambda (_: (((eq T u0 (THead (Flat Cast) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead (Flat Cast) u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t2: 
T).(pr0 t1 t2)))) (pr0 t1 u2))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda 
(_: (pr0 t0 t2)).(\lambda (_: (((eq T t0 (THead (Flat Cast) u1 t1)) \to (or 
(ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 t2))))).(\lambda (H8: (eq T (THead 
(Flat Appl) v1 (THead (Bind b) u0 t0)) (THead (Flat Cast) u1 t1))).(let H9 
\def (eq_ind T (THead (Flat Appl) v1 (THead (Bind b) u0 t0)) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K 
return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat f) 
\Rightarrow (match f in F return (\lambda (_: F).Prop) with [Appl \Rightarrow 
True | Cast \Rightarrow False])])])) I (THead (Flat Cast) u1 t1) H8) in 
(False_ind (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t2)) (THead (Flat Cast) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t2)))) H9))))))))))))))))) (\lambda (u0: T).(\lambda 
(u2: T).(\lambda (_: (pr0 u0 u2)).(\lambda (_: (((eq T u0 (THead (Flat Cast) 
u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead 
(Flat Cast) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 u2))))).(\lambda (t0: 
T).(\lambda (t2: T).(\lambda (_: (pr0 t0 t2)).(\lambda (_: (((eq T t0 (THead 
(Flat Cast) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq 
T t2 (THead (Flat Cast) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 
u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 
t2))))).(\lambda (w: T).(\lambda (_: (subst0 O u2 t2 w)).(\lambda (H6: (eq T 
(THead (Bind Abbr) u0 t0) (THead (Flat Cast) u1 t1))).(let H7 \def (eq_ind T 
(THead (Bind Abbr) u0 t0) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat 
Cast) u1 t1) H6) in (False_ind (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: 
T).(eq T (THead (Bind Abbr) u2 w) (THead (Flat Cast) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 (THead (Bind Abbr) u2 w))) H7))))))))))))) (\lambda (b: 
B).(\lambda (_: (not (eq B b Abst))).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (_: (pr0 t0 t2)).(\lambda (_: (((eq T t0 (THead (Flat Cast) u1 
t1)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 t2))))).(\lambda (u: 
T).(\lambda (H4: (eq T (THead (Bind b) u (lift (S O) O t0)) (THead (Flat 
Cast) u1 t1))).(let H5 \def (eq_ind T (THead (Bind b) u (lift (S O) O t0)) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | 
(Flat _) \Rightarrow False])])) I (THead (Flat Cast) u1 t1) H4) in (False_ind 
(or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 t2)) H5)))))))))) (\lambda (t0: 
T).(\lambda (t2: T).(\lambda (H1: (pr0 t0 t2)).(\lambda (H2: (((eq T t0 
(THead (Flat Cast) u1 t1)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Flat Cast) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 
t2))))).(\lambda (u: T).(\lambda (H3: (eq T (THead (Flat Cast) u t0) (THead 
(Flat Cast) u1 t1))).(let H4 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow u | (TLRef _) 
\Rightarrow u | (THead _ t _) \Rightarrow t])) (THead (Flat Cast) u t0) 
(THead (Flat Cast) u1 t1) H3) in ((let H5 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | 
(TLRef _) \Rightarrow t0 | (THead _ _ t) \Rightarrow t])) (THead (Flat Cast) 
u t0) (THead (Flat Cast) u1 t1) H3) in (\lambda (_: (eq T u u1)).(let H7 \def 
(eq_ind T t0 (\lambda (t: T).((eq T t (THead (Flat Cast) u1 t1)) \to (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 t2)))) H2 t1 H5) in (let H8 \def 
(eq_ind T t0 (\lambda (t: T).(pr0 t t2)) H1 t1 H5) in (or_intror (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Flat Cast) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))) (pr0 t1 t2) H8))))) H4)))))))) y x H0))) H)))).
(* COMMENTS
Initial nodes: 2911
END *)

theorem pr0_gen_abbr:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Bind Abbr) u1 
t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(u2: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda (y: T).(pr0 t1 y)) 
(\lambda (y: T).(subst0 O u2 y t2))))))) (pr0 t1 (lift (S O) O x))))))
\def
 \lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (H: (pr0 (THead 
(Bind Abbr) u1 t1) x)).(insert_eq T (THead (Bind Abbr) u1 t1) (\lambda (t: 
T).(pr0 t x)) (\lambda (_: T).(or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 
u1 u2))) (\lambda (u2: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda 
(y: T).(pr0 t1 y)) (\lambda (y: T).(subst0 O u2 y t2))))))) (pr0 t1 (lift (S 
O) O x)))) (\lambda (y: T).(\lambda (H0: (pr0 y x)).(pr0_ind (\lambda (t: 
T).(\lambda (t0: T).((eq T t (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Bind Abbr) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t2: 
T).(or (pr0 t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: 
T).(subst0 O u2 y0 t2))))))) (pr0 t1 (lift (S O) O t0)))))) (\lambda (t: 
T).(\lambda (H1: (eq T t (THead (Bind Abbr) u1 t1))).(let H2 \def (f_equal T 
T (\lambda (e: T).e) t (THead (Bind Abbr) u1 t1) H1) in (eq_ind_r T (THead 
(Bind Abbr) u1 t1) (\lambda (t0: T).(or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T t0 (THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T 
(\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 t2))))))) (pr0 
t1 (lift (S O) O t0)))) (or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T (THead (Bind Abbr) u1 t1) (THead (Bind Abbr) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t2: T).(or (pr0 
t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 
t2))))))) (pr0 t1 (lift (S O) O (THead (Bind Abbr) u1 t1))) (ex3_2_intro T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T (THead (Bind Abbr) u1 t1) (THead 
(Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(u2: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t2)))))) u1 t1 (refl_equal T (THead (Bind 
Abbr) u1 t1)) (pr0_refl u1) (or_introl (pr0 t1 t1) (ex2 T (\lambda (y0: 
T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u1 y0 t1))) (pr0_refl t1)))) t 
H2)))) (\lambda (u0: T).(\lambda (u2: T).(\lambda (H1: (pr0 u0 u2)).(\lambda 
(H2: (((eq T u0 (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t2: T).(eq T u2 (THead (Bind Abbr) u3 t2)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t2: T).(or (pr0 
t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u3 y0 
t2))))))) (pr0 t1 (lift (S O) O u2)))))).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (H3: (pr0 t0 t2)).(\lambda (H4: (((eq T t0 (THead (Bind Abbr) u1 
t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(u3: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O 
t2)))))).(\lambda (k: K).(\lambda (H5: (eq T (THead k u0 t0) (THead (Bind 
Abbr) u1 t1))).(let H6 \def (f_equal T K (\lambda (e: T).(match e in T return 
(\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | 
(THead k0 _ _) \Rightarrow k0])) (THead k u0 t0) (THead (Bind Abbr) u1 t1) 
H5) in ((let H7 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow u0 | (TLRef _) \Rightarrow u0 
| (THead _ t _) \Rightarrow t])) (THead k u0 t0) (THead (Bind Abbr) u1 t1) 
H5) in ((let H8 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 
| (THead _ _ t) \Rightarrow t])) (THead k u0 t0) (THead (Bind Abbr) u1 t1) 
H5) in (\lambda (H9: (eq T u0 u1)).(\lambda (H10: (eq K k (Bind 
Abbr))).(eq_ind_r K (Bind Abbr) (\lambda (k0: K).(or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T (THead k0 u2 t2) (THead (Bind Abbr) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: 
T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: 
T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O (THead k0 u2 t2))))) (let 
H11 \def (eq_ind T t0 (\lambda (t: T).((eq T t (THead (Bind Abbr) u1 t1)) \to 
(or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) 
u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O t2))))) H4 
t1 H8) in (let H12 \def (eq_ind T t0 (\lambda (t: T).(pr0 t t2)) H3 t1 H8) in 
(let H13 \def (eq_ind T u0 (\lambda (t: T).((eq T t (THead (Bind Abbr) u1 
t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T u2 (THead 
(Bind Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(u3: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O u2))))) H2 
u1 H9) in (let H14 \def (eq_ind T u0 (\lambda (t: T).(pr0 t u2)) H1 u1 H9) in 
(or_introl (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind 
Abbr) u2 t2) (THead (Bind Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T 
(\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u3 y0 t3))))))) (pr0 
t1 (lift (S O) O (THead (Bind Abbr) u2 t2))) (ex3_2_intro T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T (THead (Bind Abbr) u2 t2) (THead (Bind Abbr) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u3 y0 t3)))))) u2 t2 (refl_equal T (THead (Bind 
Abbr) u2 t2)) H14 (or_introl (pr0 t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t2))) H12))))))) k H10)))) H7)) 
H6)))))))))))) (\lambda (u: T).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: 
(pr0 v1 v2)).(\lambda (_: (((eq T v1 (THead (Bind Abbr) u1 t1)) \to (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T v2 (THead (Bind Abbr) u2 
t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t2))))))) (pr0 t1 (lift (S O) O 
v2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 t2)).(\lambda 
(_: (((eq T t0 (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t3: T).(or (pr0 
t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 
t3))))))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (H5: (eq T (THead (Flat 
Appl) v1 (THead (Bind Abst) u t0)) (THead (Bind Abbr) u1 t1))).(let H6 \def 
(eq_ind T (THead (Flat Appl) v1 (THead (Bind Abst) u t0)) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K 
return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) I (THead (Bind Abbr) u1 t1) H5) in (False_ind (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) v2 t2) 
(THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (u2: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: 
T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 t3))))))) (pr0 t1 (lift (S 
O) O (THead (Bind Abbr) v2 t2)))) H6)))))))))))) (\lambda (b: B).(\lambda (_: 
(not (eq B b Abst))).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (pr0 v1 
v2)).(\lambda (_: (((eq T v1 (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T v2 (THead (Bind Abbr) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t2: 
T).(or (pr0 t1 t2) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: 
T).(subst0 O u2 y0 t2))))))) (pr0 t1 (lift (S O) O v2)))))).(\lambda (u0: 
T).(\lambda (u2: T).(\lambda (_: (pr0 u0 u2)).(\lambda (_: (((eq T u0 (THead 
(Bind Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq 
T u2 (THead (Bind Abbr) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 
u3))) (\lambda (u3: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T (\lambda (y0: 
T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u3 y0 t2))))))) (pr0 t1 (lift (S 
O) O u2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 
t2)).(\lambda (_: (((eq T t0 (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: 
T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: 
T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (H8: (eq 
T (THead (Flat Appl) v1 (THead (Bind b) u0 t0)) (THead (Bind Abbr) u1 
t1))).(let H9 \def (eq_ind T (THead (Flat Appl) v1 (THead (Bind b) u0 t0)) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | 
(Flat _) \Rightarrow True])])) I (THead (Bind Abbr) u1 t1) H8) in (False_ind 
(or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t2)) (THead (Bind Abbr) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: 
T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: 
T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t2))))) H9))))))))))))))))) (\lambda (u0: 
T).(\lambda (u2: T).(\lambda (H1: (pr0 u0 u2)).(\lambda (H2: (((eq T u0 
(THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t2: 
T).(eq T u2 (THead (Bind Abbr) u3 t2)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t2: T).(or (pr0 t1 t2) (ex2 T 
(\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u3 y0 t2))))))) (pr0 
t1 (lift (S O) O u2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H3: 
(pr0 t0 t2)).(\lambda (H4: (((eq T t0 (THead (Bind Abbr) u1 t1)) \to (or 
(ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u3 y0 t3))))))) (pr0 t1 (lift (S O) O 
t2)))))).(\lambda (w: T).(\lambda (H5: (subst0 O u2 t2 w)).(\lambda (H6: (eq 
T (THead (Bind Abbr) u0 t0) (THead (Bind Abbr) u1 t1))).(let H7 \def (f_equal 
T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead _ t _) \Rightarrow t])) 
(THead (Bind Abbr) u0 t0) (THead (Bind Abbr) u1 t1) H6) in ((let H8 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t) 
\Rightarrow t])) (THead (Bind Abbr) u0 t0) (THead (Bind Abbr) u1 t1) H6) in 
(\lambda (H9: (eq T u0 u1)).(let H10 \def (eq_ind T t0 (\lambda (t: T).((eq T 
t (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda 
(t3: T).(eq T t2 (THead (Bind Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T 
(\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u3 y0 t3))))))) (pr0 
t1 (lift (S O) O t2))))) H4 t1 H8) in (let H11 \def (eq_ind T t0 (\lambda (t: 
T).(pr0 t t2)) H3 t1 H8) in (let H12 \def (eq_ind T u0 (\lambda (t: T).((eq T 
t (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda 
(t3: T).(eq T u2 (THead (Bind Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T 
(\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u3 y0 t3))))))) (pr0 
t1 (lift (S O) O u2))))) H2 u1 H9) in (let H13 \def (eq_ind T u0 (\lambda (t: 
T).(pr0 t u2)) H1 u1 H9) in (or_introl (ex3_2 T T (\lambda (u3: T).(\lambda 
(t3: T).(eq T (THead (Bind Abbr) u2 w) (THead (Bind Abbr) u3 t3)))) (\lambda 
(u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (u3: T).(\lambda (t3: T).(or 
(pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O 
u3 y0 t3))))))) (pr0 t1 (lift (S O) O (THead (Bind Abbr) u2 w))) (ex3_2_intro 
T T (\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) u2 w) (THead 
(Bind Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(u3: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u3 y0 t3)))))) u2 w (refl_equal T (THead (Bind 
Abbr) u2 w)) H13 (or_intror (pr0 t1 w) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 w))) (ex_intro2 T (\lambda (y0: T).(pr0 t1 
y0)) (\lambda (y0: T).(subst0 O u2 y0 w)) t2 H11 H5)))))))))) H7))))))))))))) 
(\lambda (b: B).(\lambda (H1: (not (eq B b Abst))).(\lambda (t0: T).(\lambda 
(t2: T).(\lambda (H2: (pr0 t0 t2)).(\lambda (H3: (((eq T t0 (THead (Bind 
Abbr) u1 t1)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 
(THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (u2: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: 
T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 t3))))))) (pr0 t1 (lift (S 
O) O t2)))))).(\lambda (u: T).(\lambda (H4: (eq T (THead (Bind b) u (lift (S 
O) O t0)) (THead (Bind Abbr) u1 t1))).(let H5 \def (f_equal T B (\lambda (e: 
T).(match e in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow b | 
(TLRef _) \Rightarrow b | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow 
b])])) (THead (Bind b) u (lift (S O) O t0)) (THead (Bind Abbr) u1 t1) H4) in 
((let H6 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow u | (TLRef _) \Rightarrow u | (THead _ t _) 
\Rightarrow t])) (THead (Bind b) u (lift (S O) O t0)) (THead (Bind Abbr) u1 
t1) H4) in ((let H7 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map (f: ((nat 
\to nat))) (d: nat) (t: T) on t: T \def (match t with [(TSort n) \Rightarrow 
(TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with [true 
\Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t3) \Rightarrow 
(THead k (lref_map f d u0) (lref_map f (s k d) t3))]) in lref_map) (\lambda 
(x0: nat).(plus x0 (S O))) O t0) | (TLRef _) \Rightarrow ((let rec lref_map 
(f: ((nat \to nat))) (d: nat) (t: T) on t: T \def (match t with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u0 t3) 
\Rightarrow (THead k (lref_map f d u0) (lref_map f (s k d) t3))]) in 
lref_map) (\lambda (x0: nat).(plus x0 (S O))) O t0) | (THead _ _ t) 
\Rightarrow t])) (THead (Bind b) u (lift (S O) O t0)) (THead (Bind Abbr) u1 
t1) H4) in (\lambda (_: (eq T u u1)).(\lambda (H9: (eq B b Abbr)).(let H10 
\def (eq_ind B b (\lambda (b0: B).(not (eq B b0 Abst))) H1 Abbr H9) in (let 
H11 \def (eq_ind_r T t1 (\lambda (t: T).((eq T t0 (THead (Bind Abbr) u1 t)) 
\to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t3: T).(or (pr0 t t3) (ex2 T (\lambda (y0: T).(pr0 t y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t3))))))) (pr0 t (lift (S O) O t2))))) H3 
(lift (S O) O t0) H7) in (eq_ind T (lift (S O) O t0) (\lambda (t: T).(or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t3: T).(or (pr0 t t3) (ex2 T (\lambda (y0: T).(pr0 t y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t3))))))) (pr0 t (lift (S O) O t2)))) 
(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t3: T).(or (pr0 (lift (S O) O t0) t3) (ex2 T (\lambda (y0: 
T).(pr0 (lift (S O) O t0) y0)) (\lambda (y0: T).(subst0 O u2 y0 t3))))))) 
(pr0 (lift (S O) O t0) (lift (S O) O t2)) (pr0_lift t0 t2 H2 (S O) O)) t1 
H7)))))) H6)) H5)))))))))) (\lambda (t0: T).(\lambda (t2: T).(\lambda (_: 
(pr0 t0 t2)).(\lambda (_: (((eq T t0 (THead (Bind Abbr) u1 t1)) \to (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t3))))))) (pr0 t1 (lift (S O) O 
t2)))))).(\lambda (u: T).(\lambda (H3: (eq T (THead (Flat Cast) u t0) (THead 
(Bind Abbr) u1 t1))).(let H4 \def (eq_ind T (THead (Flat Cast) u t0) (\lambda 
(ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | 
(Flat _) \Rightarrow True])])) I (THead (Bind Abbr) u1 t1) H3) in (False_ind 
(or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t3))))))) (pr0 t1 (lift (S O) O t2))) 
H4)))))))) y x H0))) H)))).
(* COMMENTS
Initial nodes: 4711
END *)

theorem pr0_gen_void:
 \forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr0 (THead (Bind Void) u1 
t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T x (THead 
(Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O x))))))
\def
 \lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (H: (pr0 (THead 
(Bind Void) u1 t1) x)).(insert_eq T (THead (Bind Void) u1 t1) (\lambda (t: 
T).(pr0 t x)) (\lambda (_: T).(or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 
u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) 
O x)))) (\lambda (y: T).(\lambda (H0: (pr0 y x)).(pr0_ind (\lambda (t: 
T).(\lambda (t0: T).((eq T t (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Bind Void) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: 
T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O t0)))))) (\lambda (t: T).(\lambda 
(H1: (eq T t (THead (Bind Void) u1 t1))).(let H2 \def (f_equal T T (\lambda 
(e: T).e) t (THead (Bind Void) u1 t1) H1) in (eq_ind_r T (THead (Bind Void) 
u1 t1) (\lambda (t0: T).(or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq 
T t0 (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 
u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O 
t0)))) (or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq T (THead 
(Bind Void) u1 t1) (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 
(lift (S O) O (THead (Bind Void) u1 t1))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T (THead (Bind Void) u1 t1) (THead (Bind Void) u2 
t2)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t2: T).(pr0 t1 t2))) u1 t1 (refl_equal T (THead (Bind Void) u1 
t1)) (pr0_refl u1) (pr0_refl t1))) t H2)))) (\lambda (u0: T).(\lambda (u2: 
T).(\lambda (H1: (pr0 u0 u2)).(\lambda (H2: (((eq T u0 (THead (Bind Void) u1 
t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead 
(Bind Void) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O 
u2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H3: (pr0 t0 
t2)).(\lambda (H4: (((eq T t0 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (k: K).(\lambda 
(H5: (eq T (THead k u0 t0) (THead (Bind Void) u1 t1))).(let H6 \def (f_equal 
T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) with [(TSort _) 
\Rightarrow k | (TLRef _) \Rightarrow k | (THead k0 _ _) \Rightarrow k0])) 
(THead k u0 t0) (THead (Bind Void) u1 t1) H5) in ((let H7 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead _ t _) \Rightarrow t])) 
(THead k u0 t0) (THead (Bind Void) u1 t1) H5) in ((let H8 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t) \Rightarrow t])) 
(THead k u0 t0) (THead (Bind Void) u1 t1) H5) in (\lambda (H9: (eq T u0 
u1)).(\lambda (H10: (eq K k (Bind Void))).(eq_ind_r K (Bind Void) (\lambda 
(k0: K).(or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T (THead k0 u2 
t2) (THead (Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 
u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O 
(THead k0 u2 t2))))) (let H11 \def (eq_ind T t0 (\lambda (t: T).((eq T t 
(THead (Bind Void) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: 
T).(eq T t2 (THead (Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 
(lift (S O) O t2))))) H4 t1 H8) in (let H12 \def (eq_ind T t0 (\lambda (t: 
T).(pr0 t t2)) H3 t1 H8) in (let H13 \def (eq_ind T u0 (\lambda (t: T).((eq T 
t (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda 
(t3: T).(eq T u2 (THead (Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 
(lift (S O) O u2))))) H2 u1 H9) in (let H14 \def (eq_ind T u0 (\lambda (t: 
T).(pr0 t u2)) H1 u1 H9) in (or_introl (ex3_2 T T (\lambda (u3: T).(\lambda 
(t3: T).(eq T (THead (Bind Void) u2 t2) (THead (Bind Void) u3 t3)))) (\lambda 
(u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 
t1 t3)))) (pr0 t1 (lift (S O) O (THead (Bind Void) u2 t2))) (ex3_2_intro T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind Void) u2 t2) (THead 
(Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3))) u2 t2 (refl_equal T (THead (Bind Void) 
u2 t2)) H14 H12)))))) k H10)))) H7)) H6)))))))))))) (\lambda (u: T).(\lambda 
(v1: T).(\lambda (v2: T).(\lambda (_: (pr0 v1 v2)).(\lambda (_: (((eq T v1 
(THead (Bind Void) u1 t1)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T v2 (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 
(lift (S O) O v2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 
t2)).(\lambda (_: (((eq T t0 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (H5: (eq T (THead 
(Flat Appl) v1 (THead (Bind Abst) u t0)) (THead (Bind Void) u1 t1))).(let H6 
\def (eq_ind T (THead (Flat Appl) v1 (THead (Bind Abst) u t0)) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K 
return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) I (THead (Bind Void) u1 t1) H5) in (False_ind (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) v2 t2) 
(THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O (THead 
(Bind Abbr) v2 t2)))) H6)))))))))))) (\lambda (b: B).(\lambda (_: (not (eq B 
b Abst))).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (pr0 v1 
v2)).(\lambda (_: (((eq T v1 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T v2 (THead (Bind Void) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t2: 
T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O v2)))))).(\lambda (u0: T).(\lambda 
(u2: T).(\lambda (_: (pr0 u0 u2)).(\lambda (_: (((eq T u0 (THead (Bind Void) 
u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead 
(Bind Void) u3 t2)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t2: T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O 
u2)))))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (_: (pr0 t0 t2)).(\lambda 
(_: (((eq T t0 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 
t3)))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (H8: (eq T (THead (Flat Appl) 
v1 (THead (Bind b) u0 t0)) (THead (Bind Void) u1 t1))).(let H9 \def (eq_ind T 
(THead (Flat Appl) v1 (THead (Bind b) u0 t0)) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind Void) u1 t1) H8) in (False_ind (or (ex3_2 T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t2)) (THead (Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda 
(_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 
(lift (S O) O (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t2))))) 
H9))))))))))))))))) (\lambda (u0: T).(\lambda (u2: T).(\lambda (_: (pr0 u0 
u2)).(\lambda (_: (((eq T u0 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u3: T).(\lambda (t2: T).(eq T u2 (THead (Bind Void) u3 t2)))) 
(\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda (_: T).(\lambda (t2: 
T).(pr0 t1 t2)))) (pr0 t1 (lift (S O) O u2)))))).(\lambda (t0: T).(\lambda 
(t2: T).(\lambda (_: (pr0 t0 t2)).(\lambda (_: (((eq T t0 (THead (Bind Void) 
u1 t1)) \to (or (ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O 
t2)))))).(\lambda (w: T).(\lambda (_: (subst0 O u2 t2 w)).(\lambda (H6: (eq T 
(THead (Bind Abbr) u0 t0) (THead (Bind Void) u1 t1))).(let H7 \def (eq_ind T 
(THead (Bind Abbr) u0 t0) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind b) \Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr 
\Rightarrow True | Abst \Rightarrow False | Void \Rightarrow False]) | (Flat 
_) \Rightarrow False])])) I (THead (Bind Void) u1 t1) H6) in (False_ind (or 
(ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) u2 w) 
(THead (Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr0 u1 u3))) 
(\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O (THead 
(Bind Abbr) u2 w)))) H7))))))))))))) (\lambda (b: B).(\lambda (H1: (not (eq B 
b Abst))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H2: (pr0 t0 
t2)).(\lambda (H3: (((eq T t0 (THead (Bind Void) u1 t1)) \to (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O t2)))))).(\lambda (u: T).(\lambda 
(H4: (eq T (THead (Bind b) u (lift (S O) O t0)) (THead (Bind Void) u1 
t1))).(let H5 \def (f_equal T B (\lambda (e: T).(match e in T return (\lambda 
(_: T).B) with [(TSort _) \Rightarrow b | (TLRef _) \Rightarrow b | (THead k 
_ _) \Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow b])])) (THead (Bind b) u (lift (S O) O 
t0)) (THead (Bind Void) u1 t1) H4) in ((let H6 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u | 
(TLRef _) \Rightarrow u | (THead _ t _) \Rightarrow t])) (THead (Bind b) u 
(lift (S O) O t0)) (THead (Bind Void) u1 t1) H4) in ((let H7 \def (f_equal T 
T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
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
t1) H4) in (\lambda (_: (eq T u u1)).(\lambda (H9: (eq B b Void)).(let H10 
\def (eq_ind B b (\lambda (b0: B).(not (eq B b0 Abst))) H1 Void H9) in (let 
H11 \def (eq_ind_r T t1 (\lambda (t: T).((eq T t0 (THead (Bind Void) u1 t)) 
\to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t t3)))) (pr0 t (lift (S O) O t2))))) H3 (lift (S O) 
O t0) H7) in (eq_ind T (lift (S O) O t0) (\lambda (t: T).(or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t t3)))) (pr0 t (lift (S O) O t2)))) (or_intror (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 (lift 
(S O) O t0) t3)))) (pr0 (lift (S O) O t0) (lift (S O) O t2)) (pr0_lift t0 t2 
H2 (S O) O)) t1 H7)))))) H6)) H5)))))))))) (\lambda (t0: T).(\lambda (t2: 
T).(\lambda (_: (pr0 t0 t2)).(\lambda (_: (((eq T t0 (THead (Bind Void) u1 
t1)) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O 
t2)))))).(\lambda (u: T).(\lambda (H3: (eq T (THead (Flat Cast) u t0) (THead 
(Bind Void) u1 t1))).(let H4 \def (eq_ind T (THead (Flat Cast) u t0) (\lambda 
(ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | 
(Flat _) \Rightarrow True])])) I (THead (Bind Void) u1 t1) H3) in (False_ind 
(or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O t2))) H4)))))))) y x 
H0))) H)))).
(* COMMENTS
Initial nodes: 3436
END *)

theorem pr0_gen_lift:
 \forall (t1: T).(\forall (x: T).(\forall (h: nat).(\forall (d: nat).((pr0 
(lift h d t1) x) \to (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda 
(t2: T).(pr0 t1 t2)))))))
\def
 \lambda (t1: T).(\lambda (x: T).(\lambda (h: nat).(\lambda (d: nat).(\lambda 
(H: (pr0 (lift h d t1) x)).(insert_eq T (lift h d t1) (\lambda (t: T).(pr0 t 
x)) (\lambda (_: T).(ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda 
(t2: T).(pr0 t1 t2)))) (\lambda (y: T).(\lambda (H0: (pr0 y x)).(unintro nat 
d (\lambda (n: nat).((eq T y (lift h n t1)) \to (ex2 T (\lambda (t2: T).(eq T 
x (lift h n t2))) (\lambda (t2: T).(pr0 t1 t2))))) (unintro T t1 (\lambda (t: 
T).(\forall (x0: nat).((eq T y (lift h x0 t)) \to (ex2 T (\lambda (t2: T).(eq 
T x (lift h x0 t2))) (\lambda (t2: T).(pr0 t t2)))))) (pr0_ind (\lambda (t: 
T).(\lambda (t0: T).(\forall (x0: T).(\forall (x1: nat).((eq T t (lift h x1 
x0)) \to (ex2 T (\lambda (t2: T).(eq T t0 (lift h x1 t2))) (\lambda (t2: 
T).(pr0 x0 t2)))))))) (\lambda (t: T).(\lambda (x0: T).(\lambda (x1: 
nat).(\lambda (H1: (eq T t (lift h x1 x0))).(ex_intro2 T (\lambda (t2: T).(eq 
T t (lift h x1 t2))) (\lambda (t2: T).(pr0 x0 t2)) x0 H1 (pr0_refl x0)))))) 
(\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (pr0 u1 u2)).(\lambda (H2: 
((\forall (x0: T).(\forall (x1: nat).((eq T u1 (lift h x1 x0)) \to (ex2 T 
(\lambda (t2: T).(eq T u2 (lift h x1 t2))) (\lambda (t2: T).(pr0 x0 
t2)))))))).(\lambda (t2: T).(\lambda (t3: T).(\lambda (_: (pr0 t2 
t3)).(\lambda (H4: ((\forall (x0: T).(\forall (x1: nat).((eq T t2 (lift h x1 
x0)) \to (ex2 T (\lambda (t4: T).(eq T t3 (lift h x1 t4))) (\lambda (t4: 
T).(pr0 x0 t4)))))))).(\lambda (k: K).(\lambda (x0: T).(\lambda (x1: 
nat).(\lambda (H5: (eq T (THead k u1 t2) (lift h x1 x0))).(K_ind (\lambda 
(k0: K).((eq T (THead k0 u1 t2) (lift h x1 x0)) \to (ex2 T (\lambda (t4: 
T).(eq T (THead k0 u2 t3) (lift h x1 t4))) (\lambda (t4: T).(pr0 x0 t4))))) 
(\lambda (b: B).(\lambda (H6: (eq T (THead (Bind b) u1 t2) (lift h x1 
x0))).(ex3_2_ind T T (\lambda (y0: T).(\lambda (z: T).(eq T x0 (THead (Bind 
b) y0 z)))) (\lambda (y0: T).(\lambda (_: T).(eq T u1 (lift h x1 y0)))) 
(\lambda (_: T).(\lambda (z: T).(eq T t2 (lift h (S x1) z)))) (ex2 T (\lambda 
(t4: T).(eq T (THead (Bind b) u2 t3) (lift h x1 t4))) (\lambda (t4: T).(pr0 
x0 t4))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H7: (eq T x0 (THead 
(Bind b) x2 x3))).(\lambda (H8: (eq T u1 (lift h x1 x2))).(\lambda (H9: (eq T 
t2 (lift h (S x1) x3))).(eq_ind_r T (THead (Bind b) x2 x3) (\lambda (t: 
T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind b) u2 t3) (lift h x1 t4))) 
(\lambda (t4: T).(pr0 t t4)))) (ex2_ind T (\lambda (t4: T).(eq T t3 (lift h 
(S x1) t4))) (\lambda (t4: T).(pr0 x3 t4)) (ex2 T (\lambda (t4: T).(eq T 
(THead (Bind b) u2 t3) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Bind b) 
x2 x3) t4))) (\lambda (x4: T).(\lambda (H_x: (eq T t3 (lift h (S x1) 
x4))).(\lambda (H10: (pr0 x3 x4)).(eq_ind_r T (lift h (S x1) x4) (\lambda (t: 
T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind b) u2 t) (lift h x1 t4))) 
(\lambda (t4: T).(pr0 (THead (Bind b) x2 x3) t4)))) (ex2_ind T (\lambda (t4: 
T).(eq T u2 (lift h x1 t4))) (\lambda (t4: T).(pr0 x2 t4)) (ex2 T (\lambda 
(t4: T).(eq T (THead (Bind b) u2 (lift h (S x1) x4)) (lift h x1 t4))) 
(\lambda (t4: T).(pr0 (THead (Bind b) x2 x3) t4))) (\lambda (x5: T).(\lambda 
(H_x0: (eq T u2 (lift h x1 x5))).(\lambda (H11: (pr0 x2 x5)).(eq_ind_r T 
(lift h x1 x5) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind b) 
t (lift h (S x1) x4)) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Bind b) 
x2 x3) t4)))) (ex_intro2 T (\lambda (t4: T).(eq T (THead (Bind b) (lift h x1 
x5) (lift h (S x1) x4)) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Bind 
b) x2 x3) t4)) (THead (Bind b) x5 x4) (sym_eq T (lift h x1 (THead (Bind b) x5 
x4)) (THead (Bind b) (lift h x1 x5) (lift h (S x1) x4)) (lift_bind b x5 x4 h 
x1)) (pr0_comp x2 x5 H11 x3 x4 H10 (Bind b))) u2 H_x0)))) (H2 x2 x1 H8)) t3 
H_x)))) (H4 x3 (S x1) H9)) x0 H7)))))) (lift_gen_bind b u1 t2 x0 h x1 H6)))) 
(\lambda (f: F).(\lambda (H6: (eq T (THead (Flat f) u1 t2) (lift h x1 
x0))).(ex3_2_ind T T (\lambda (y0: T).(\lambda (z: T).(eq T x0 (THead (Flat 
f) y0 z)))) (\lambda (y0: T).(\lambda (_: T).(eq T u1 (lift h x1 y0)))) 
(\lambda (_: T).(\lambda (z: T).(eq T t2 (lift h x1 z)))) (ex2 T (\lambda 
(t4: T).(eq T (THead (Flat f) u2 t3) (lift h x1 t4))) (\lambda (t4: T).(pr0 
x0 t4))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H7: (eq T x0 (THead 
(Flat f) x2 x3))).(\lambda (H8: (eq T u1 (lift h x1 x2))).(\lambda (H9: (eq T 
t2 (lift h x1 x3))).(eq_ind_r T (THead (Flat f) x2 x3) (\lambda (t: T).(ex2 T 
(\lambda (t4: T).(eq T (THead (Flat f) u2 t3) (lift h x1 t4))) (\lambda (t4: 
T).(pr0 t t4)))) (ex2_ind T (\lambda (t4: T).(eq T t3 (lift h x1 t4))) 
(\lambda (t4: T).(pr0 x3 t4)) (ex2 T (\lambda (t4: T).(eq T (THead (Flat f) 
u2 t3) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat f) x2 x3) t4))) 
(\lambda (x4: T).(\lambda (H_x: (eq T t3 (lift h x1 x4))).(\lambda (H10: (pr0 
x3 x4)).(eq_ind_r T (lift h x1 x4) (\lambda (t: T).(ex2 T (\lambda (t4: 
T).(eq T (THead (Flat f) u2 t) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead 
(Flat f) x2 x3) t4)))) (ex2_ind T (\lambda (t4: T).(eq T u2 (lift h x1 t4))) 
(\lambda (t4: T).(pr0 x2 t4)) (ex2 T (\lambda (t4: T).(eq T (THead (Flat f) 
u2 (lift h x1 x4)) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat f) x2 
x3) t4))) (\lambda (x5: T).(\lambda (H_x0: (eq T u2 (lift h x1 x5))).(\lambda 
(H11: (pr0 x2 x5)).(eq_ind_r T (lift h x1 x5) (\lambda (t: T).(ex2 T (\lambda 
(t4: T).(eq T (THead (Flat f) t (lift h x1 x4)) (lift h x1 t4))) (\lambda 
(t4: T).(pr0 (THead (Flat f) x2 x3) t4)))) (ex_intro2 T (\lambda (t4: T).(eq 
T (THead (Flat f) (lift h x1 x5) (lift h x1 x4)) (lift h x1 t4))) (\lambda 
(t4: T).(pr0 (THead (Flat f) x2 x3) t4)) (THead (Flat f) x5 x4) (sym_eq T 
(lift h x1 (THead (Flat f) x5 x4)) (THead (Flat f) (lift h x1 x5) (lift h x1 
x4)) (lift_flat f x5 x4 h x1)) (pr0_comp x2 x5 H11 x3 x4 H10 (Flat f))) u2 
H_x0)))) (H2 x2 x1 H8)) t3 H_x)))) (H4 x3 x1 H9)) x0 H7)))))) (lift_gen_flat 
f u1 t2 x0 h x1 H6)))) k H5))))))))))))) (\lambda (u: T).(\lambda (v1: 
T).(\lambda (v2: T).(\lambda (_: (pr0 v1 v2)).(\lambda (H2: ((\forall (x0: 
T).(\forall (x1: nat).((eq T v1 (lift h x1 x0)) \to (ex2 T (\lambda (t2: 
T).(eq T v2 (lift h x1 t2))) (\lambda (t2: T).(pr0 x0 t2)))))))).(\lambda 
(t2: T).(\lambda (t3: T).(\lambda (_: (pr0 t2 t3)).(\lambda (H4: ((\forall 
(x0: T).(\forall (x1: nat).((eq T t2 (lift h x1 x0)) \to (ex2 T (\lambda (t4: 
T).(eq T t3 (lift h x1 t4))) (\lambda (t4: T).(pr0 x0 t4)))))))).(\lambda 
(x0: T).(\lambda (x1: nat).(\lambda (H5: (eq T (THead (Flat Appl) v1 (THead 
(Bind Abst) u t2)) (lift h x1 x0))).(ex3_2_ind T T (\lambda (y0: T).(\lambda 
(z: T).(eq T x0 (THead (Flat Appl) y0 z)))) (\lambda (y0: T).(\lambda (_: 
T).(eq T v1 (lift h x1 y0)))) (\lambda (_: T).(\lambda (z: T).(eq T (THead 
(Bind Abst) u t2) (lift h x1 z)))) (ex2 T (\lambda (t4: T).(eq T (THead (Bind 
Abbr) v2 t3) (lift h x1 t4))) (\lambda (t4: T).(pr0 x0 t4))) (\lambda (x2: 
T).(\lambda (x3: T).(\lambda (H6: (eq T x0 (THead (Flat Appl) x2 
x3))).(\lambda (H7: (eq T v1 (lift h x1 x2))).(\lambda (H8: (eq T (THead 
(Bind Abst) u t2) (lift h x1 x3))).(eq_ind_r T (THead (Flat Appl) x2 x3) 
(\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind Abbr) v2 t3) (lift 
h x1 t4))) (\lambda (t4: T).(pr0 t t4)))) (ex3_2_ind T T (\lambda (y0: 
T).(\lambda (z: T).(eq T x3 (THead (Bind Abst) y0 z)))) (\lambda (y0: 
T).(\lambda (_: T).(eq T u (lift h x1 y0)))) (\lambda (_: T).(\lambda (z: 
T).(eq T t2 (lift h (S x1) z)))) (ex2 T (\lambda (t4: T).(eq T (THead (Bind 
Abbr) v2 t3) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat Appl) x2 x3) 
t4))) (\lambda (x4: T).(\lambda (x5: T).(\lambda (H9: (eq T x3 (THead (Bind 
Abst) x4 x5))).(\lambda (_: (eq T u (lift h x1 x4))).(\lambda (H11: (eq T t2 
(lift h (S x1) x5))).(eq_ind_r T (THead (Bind Abst) x4 x5) (\lambda (t: 
T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind Abbr) v2 t3) (lift h x1 t4))) 
(\lambda (t4: T).(pr0 (THead (Flat Appl) x2 t) t4)))) (ex2_ind T (\lambda 
(t4: T).(eq T t3 (lift h (S x1) t4))) (\lambda (t4: T).(pr0 x5 t4)) (ex2 T 
(\lambda (t4: T).(eq T (THead (Bind Abbr) v2 t3) (lift h x1 t4))) (\lambda 
(t4: T).(pr0 (THead (Flat Appl) x2 (THead (Bind Abst) x4 x5)) t4))) (\lambda 
(x6: T).(\lambda (H_x: (eq T t3 (lift h (S x1) x6))).(\lambda (H12: (pr0 x5 
x6)).(eq_ind_r T (lift h (S x1) x6) (\lambda (t: T).(ex2 T (\lambda (t4: 
T).(eq T (THead (Bind Abbr) v2 t) (lift h x1 t4))) (\lambda (t4: T).(pr0 
(THead (Flat Appl) x2 (THead (Bind Abst) x4 x5)) t4)))) (ex2_ind T (\lambda 
(t4: T).(eq T v2 (lift h x1 t4))) (\lambda (t4: T).(pr0 x2 t4)) (ex2 T 
(\lambda (t4: T).(eq T (THead (Bind Abbr) v2 (lift h (S x1) x6)) (lift h x1 
t4))) (\lambda (t4: T).(pr0 (THead (Flat Appl) x2 (THead (Bind Abst) x4 x5)) 
t4))) (\lambda (x7: T).(\lambda (H_x0: (eq T v2 (lift h x1 x7))).(\lambda 
(H13: (pr0 x2 x7)).(eq_ind_r T (lift h x1 x7) (\lambda (t: T).(ex2 T (\lambda 
(t4: T).(eq T (THead (Bind Abbr) t (lift h (S x1) x6)) (lift h x1 t4))) 
(\lambda (t4: T).(pr0 (THead (Flat Appl) x2 (THead (Bind Abst) x4 x5)) t4)))) 
(ex_intro2 T (\lambda (t4: T).(eq T (THead (Bind Abbr) (lift h x1 x7) (lift h 
(S x1) x6)) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat Appl) x2 
(THead (Bind Abst) x4 x5)) t4)) (THead (Bind Abbr) x7 x6) (sym_eq T (lift h 
x1 (THead (Bind Abbr) x7 x6)) (THead (Bind Abbr) (lift h x1 x7) (lift h (S 
x1) x6)) (lift_bind Abbr x7 x6 h x1)) (pr0_beta x4 x2 x7 H13 x5 x6 H12)) v2 
H_x0)))) (H2 x2 x1 H7)) t3 H_x)))) (H4 x5 (S x1) H11)) x3 H9)))))) 
(lift_gen_bind Abst u t2 x3 h x1 H8)) x0 H6)))))) (lift_gen_flat Appl v1 
(THead (Bind Abst) u t2) x0 h x1 H5)))))))))))))) (\lambda (b: B).(\lambda 
(H1: (not (eq B b Abst))).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (pr0 
v1 v2)).(\lambda (H3: ((\forall (x0: T).(\forall (x1: nat).((eq T v1 (lift h 
x1 x0)) \to (ex2 T (\lambda (t2: T).(eq T v2 (lift h x1 t2))) (\lambda (t2: 
T).(pr0 x0 t2)))))))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (pr0 u1 
u2)).(\lambda (H5: ((\forall (x0: T).(\forall (x1: nat).((eq T u1 (lift h x1 
x0)) \to (ex2 T (\lambda (t2: T).(eq T u2 (lift h x1 t2))) (\lambda (t2: 
T).(pr0 x0 t2)))))))).(\lambda (t2: T).(\lambda (t3: T).(\lambda (_: (pr0 t2 
t3)).(\lambda (H7: ((\forall (x0: T).(\forall (x1: nat).((eq T t2 (lift h x1 
x0)) \to (ex2 T (\lambda (t4: T).(eq T t3 (lift h x1 t4))) (\lambda (t4: 
T).(pr0 x0 t4)))))))).(\lambda (x0: T).(\lambda (x1: nat).(\lambda (H8: (eq T 
(THead (Flat Appl) v1 (THead (Bind b) u1 t2)) (lift h x1 x0))).(ex3_2_ind T T 
(\lambda (y0: T).(\lambda (z: T).(eq T x0 (THead (Flat Appl) y0 z)))) 
(\lambda (y0: T).(\lambda (_: T).(eq T v1 (lift h x1 y0)))) (\lambda (_: 
T).(\lambda (z: T).(eq T (THead (Bind b) u1 t2) (lift h x1 z)))) (ex2 T 
(\lambda (t4: T).(eq T (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O 
v2) t3)) (lift h x1 t4))) (\lambda (t4: T).(pr0 x0 t4))) (\lambda (x2: 
T).(\lambda (x3: T).(\lambda (H9: (eq T x0 (THead (Flat Appl) x2 
x3))).(\lambda (H10: (eq T v1 (lift h x1 x2))).(\lambda (H11: (eq T (THead 
(Bind b) u1 t2) (lift h x1 x3))).(eq_ind_r T (THead (Flat Appl) x2 x3) 
(\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t3)) (lift h x1 t4))) (\lambda (t4: T).(pr0 t t4)))) 
(ex3_2_ind T T (\lambda (y0: T).(\lambda (z: T).(eq T x3 (THead (Bind b) y0 
z)))) (\lambda (y0: T).(\lambda (_: T).(eq T u1 (lift h x1 y0)))) (\lambda 
(_: T).(\lambda (z: T).(eq T t2 (lift h (S x1) z)))) (ex2 T (\lambda (t4: 
T).(eq T (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t3)) (lift h 
x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat Appl) x2 x3) t4))) (\lambda (x4: 
T).(\lambda (x5: T).(\lambda (H12: (eq T x3 (THead (Bind b) x4 x5))).(\lambda 
(H13: (eq T u1 (lift h x1 x4))).(\lambda (H14: (eq T t2 (lift h (S x1) 
x5))).(eq_ind_r T (THead (Bind b) x4 x5) (\lambda (t: T).(ex2 T (\lambda (t4: 
T).(eq T (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t3)) (lift h 
x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat Appl) x2 t) t4)))) (ex2_ind T 
(\lambda (t4: T).(eq T t3 (lift h (S x1) t4))) (\lambda (t4: T).(pr0 x5 t4)) 
(ex2 T (\lambda (t4: T).(eq T (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t3)) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat Appl) x2 
(THead (Bind b) x4 x5)) t4))) (\lambda (x6: T).(\lambda (H_x: (eq T t3 (lift 
h (S x1) x6))).(\lambda (H15: (pr0 x5 x6)).(eq_ind_r T (lift h (S x1) x6) 
(\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t)) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead 
(Flat Appl) x2 (THead (Bind b) x4 x5)) t4)))) (ex2_ind T (\lambda (t4: T).(eq 
T u2 (lift h x1 t4))) (\lambda (t4: T).(pr0 x4 t4)) (ex2 T (\lambda (t4: 
T).(eq T (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) (lift h (S 
x1) x6))) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat Appl) x2 (THead 
(Bind b) x4 x5)) t4))) (\lambda (x7: T).(\lambda (H_x0: (eq T u2 (lift h x1 
x7))).(\lambda (H16: (pr0 x4 x7)).(eq_ind_r T (lift h x1 x7) (\lambda (t: 
T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind b) t (THead (Flat Appl) (lift 
(S O) O v2) (lift h (S x1) x6))) (lift h x1 t4))) (\lambda (t4: T).(pr0 
(THead (Flat Appl) x2 (THead (Bind b) x4 x5)) t4)))) (ex2_ind T (\lambda (t4: 
T).(eq T v2 (lift h x1 t4))) (\lambda (t4: T).(pr0 x2 t4)) (ex2 T (\lambda 
(t4: T).(eq T (THead (Bind b) (lift h x1 x7) (THead (Flat Appl) (lift (S O) O 
v2) (lift h (S x1) x6))) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat 
Appl) x2 (THead (Bind b) x4 x5)) t4))) (\lambda (x8: T).(\lambda (H_x1: (eq T 
v2 (lift h x1 x8))).(\lambda (H17: (pr0 x2 x8)).(eq_ind_r T (lift h x1 x8) 
(\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind b) (lift h x1 x7) 
(THead (Flat Appl) (lift (S O) O t) (lift h (S x1) x6))) (lift h x1 t4))) 
(\lambda (t4: T).(pr0 (THead (Flat Appl) x2 (THead (Bind b) x4 x5)) t4)))) 
(eq_ind T (lift h (plus (S O) x1) (lift (S O) O x8)) (\lambda (t: T).(ex2 T 
(\lambda (t4: T).(eq T (THead (Bind b) (lift h x1 x7) (THead (Flat Appl) t 
(lift h (S x1) x6))) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Flat 
Appl) x2 (THead (Bind b) x4 x5)) t4)))) (eq_ind T (lift h (S x1) (THead (Flat 
Appl) (lift (S O) O x8) x6)) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T 
(THead (Bind b) (lift h x1 x7) t) (lift h x1 t4))) (\lambda (t4: T).(pr0 
(THead (Flat Appl) x2 (THead (Bind b) x4 x5)) t4)))) (ex_intro2 T (\lambda 
(t4: T).(eq T (THead (Bind b) (lift h x1 x7) (lift h (S x1) (THead (Flat 
Appl) (lift (S O) O x8) x6))) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead 
(Flat Appl) x2 (THead (Bind b) x4 x5)) t4)) (THead (Bind b) x7 (THead (Flat 
Appl) (lift (S O) O x8) x6)) (sym_eq T (lift h x1 (THead (Bind b) x7 (THead 
(Flat Appl) (lift (S O) O x8) x6))) (THead (Bind b) (lift h x1 x7) (lift h (S 
x1) (THead (Flat Appl) (lift (S O) O x8) x6))) (lift_bind b x7 (THead (Flat 
Appl) (lift (S O) O x8) x6) h x1)) (pr0_upsilon b H1 x2 x8 H17 x4 x7 H16 x5 
x6 H15)) (THead (Flat Appl) (lift h (S x1) (lift (S O) O x8)) (lift h (S x1) 
x6)) (lift_flat Appl (lift (S O) O x8) x6 h (S x1))) (lift (S O) O (lift h x1 
x8)) (lift_d x8 h (S O) x1 O (le_O_n x1))) v2 H_x1)))) (H3 x2 x1 H10)) u2 
H_x0)))) (H5 x4 x1 H13)) t3 H_x)))) (H7 x5 (S x1) H14)) x3 H12)))))) 
(lift_gen_bind b u1 t2 x3 h x1 H11)) x0 H9)))))) (lift_gen_flat Appl v1 
(THead (Bind b) u1 t2) x0 h x1 H8))))))))))))))))))) (\lambda (u1: 
T).(\lambda (u2: T).(\lambda (_: (pr0 u1 u2)).(\lambda (H2: ((\forall (x0: 
T).(\forall (x1: nat).((eq T u1 (lift h x1 x0)) \to (ex2 T (\lambda (t2: 
T).(eq T u2 (lift h x1 t2))) (\lambda (t2: T).(pr0 x0 t2)))))))).(\lambda 
(t2: T).(\lambda (t3: T).(\lambda (_: (pr0 t2 t3)).(\lambda (H4: ((\forall 
(x0: T).(\forall (x1: nat).((eq T t2 (lift h x1 x0)) \to (ex2 T (\lambda (t4: 
T).(eq T t3 (lift h x1 t4))) (\lambda (t4: T).(pr0 x0 t4)))))))).(\lambda (w: 
T).(\lambda (H5: (subst0 O u2 t3 w)).(\lambda (x0: T).(\lambda (x1: 
nat).(\lambda (H6: (eq T (THead (Bind Abbr) u1 t2) (lift h x1 
x0))).(ex3_2_ind T T (\lambda (y0: T).(\lambda (z: T).(eq T x0 (THead (Bind 
Abbr) y0 z)))) (\lambda (y0: T).(\lambda (_: T).(eq T u1 (lift h x1 y0)))) 
(\lambda (_: T).(\lambda (z: T).(eq T t2 (lift h (S x1) z)))) (ex2 T (\lambda 
(t4: T).(eq T (THead (Bind Abbr) u2 w) (lift h x1 t4))) (\lambda (t4: T).(pr0 
x0 t4))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H7: (eq T x0 (THead 
(Bind Abbr) x2 x3))).(\lambda (H8: (eq T u1 (lift h x1 x2))).(\lambda (H9: 
(eq T t2 (lift h (S x1) x3))).(eq_ind_r T (THead (Bind Abbr) x2 x3) (\lambda 
(t: T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind Abbr) u2 w) (lift h x1 
t4))) (\lambda (t4: T).(pr0 t t4)))) (ex2_ind T (\lambda (t4: T).(eq T t3 
(lift h (S x1) t4))) (\lambda (t4: T).(pr0 x3 t4)) (ex2 T (\lambda (t4: 
T).(eq T (THead (Bind Abbr) u2 w) (lift h x1 t4))) (\lambda (t4: T).(pr0 
(THead (Bind Abbr) x2 x3) t4))) (\lambda (x4: T).(\lambda (H_x: (eq T t3 
(lift h (S x1) x4))).(\lambda (H10: (pr0 x3 x4)).(let H11 \def (eq_ind T t3 
(\lambda (t: T).(subst0 O u2 t w)) H5 (lift h (S x1) x4) H_x) in (ex2_ind T 
(\lambda (t4: T).(eq T u2 (lift h x1 t4))) (\lambda (t4: T).(pr0 x2 t4)) (ex2 
T (\lambda (t4: T).(eq T (THead (Bind Abbr) u2 w) (lift h x1 t4))) (\lambda 
(t4: T).(pr0 (THead (Bind Abbr) x2 x3) t4))) (\lambda (x5: T).(\lambda (H_x0: 
(eq T u2 (lift h x1 x5))).(\lambda (H12: (pr0 x2 x5)).(eq_ind_r T (lift h x1 
x5) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind Abbr) t w) 
(lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Bind Abbr) x2 x3) t4)))) (let 
H13 \def (eq_ind T u2 (\lambda (t: T).(subst0 O t (lift h (S x1) x4) w)) H11 
(lift h x1 x5) H_x0) in (let H14 \def (refl_equal nat (S (plus O x1))) in 
(let H15 \def (eq_ind nat (S x1) (\lambda (n: nat).(subst0 O (lift h x1 x5) 
(lift h n x4) w)) H13 (S (plus O x1)) H14) in (ex2_ind T (\lambda (t4: T).(eq 
T w (lift h (S (plus O x1)) t4))) (\lambda (t4: T).(subst0 O x5 x4 t4)) (ex2 
T (\lambda (t4: T).(eq T (THead (Bind Abbr) (lift h x1 x5) w) (lift h x1 
t4))) (\lambda (t4: T).(pr0 (THead (Bind Abbr) x2 x3) t4))) (\lambda (x6: 
T).(\lambda (H16: (eq T w (lift h (S (plus O x1)) x6))).(\lambda (H17: 
(subst0 O x5 x4 x6)).(eq_ind_r T (lift h (S (plus O x1)) x6) (\lambda (t: 
T).(ex2 T (\lambda (t4: T).(eq T (THead (Bind Abbr) (lift h x1 x5) t) (lift h 
x1 t4))) (\lambda (t4: T).(pr0 (THead (Bind Abbr) x2 x3) t4)))) (ex_intro2 T 
(\lambda (t4: T).(eq T (THead (Bind Abbr) (lift h x1 x5) (lift h (S (plus O 
x1)) x6)) (lift h x1 t4))) (\lambda (t4: T).(pr0 (THead (Bind Abbr) x2 x3) 
t4)) (THead (Bind Abbr) x5 x6) (sym_eq T (lift h x1 (THead (Bind Abbr) x5 
x6)) (THead (Bind Abbr) (lift h x1 x5) (lift h (S (plus O x1)) x6)) 
(lift_bind Abbr x5 x6 h (plus O x1))) (pr0_delta x2 x5 H12 x3 x4 H10 x6 H17)) 
w H16)))) (subst0_gen_lift_lt x5 x4 w O h x1 H15))))) u2 H_x0)))) (H2 x2 x1 
H8)))))) (H4 x3 (S x1) H9)) x0 H7)))))) (lift_gen_bind Abbr u1 t2 x0 h x1 
H6))))))))))))))) (\lambda (b: B).(\lambda (H1: (not (eq B b Abst))).(\lambda 
(t2: T).(\lambda (t3: T).(\lambda (_: (pr0 t2 t3)).(\lambda (H3: ((\forall 
(x0: T).(\forall (x1: nat).((eq T t2 (lift h x1 x0)) \to (ex2 T (\lambda (t4: 
T).(eq T t3 (lift h x1 t4))) (\lambda (t4: T).(pr0 x0 t4)))))))).(\lambda (u: 
T).(\lambda (x0: T).(\lambda (x1: nat).(\lambda (H4: (eq T (THead (Bind b) u 
(lift (S O) O t2)) (lift h x1 x0))).(ex3_2_ind T T (\lambda (y0: T).(\lambda 
(z: T).(eq T x0 (THead (Bind b) y0 z)))) (\lambda (y0: T).(\lambda (_: T).(eq 
T u (lift h x1 y0)))) (\lambda (_: T).(\lambda (z: T).(eq T (lift (S O) O t2) 
(lift h (S x1) z)))) (ex2 T (\lambda (t4: T).(eq T t3 (lift h x1 t4))) 
(\lambda (t4: T).(pr0 x0 t4))) (\lambda (x2: T).(\lambda (x3: T).(\lambda 
(H5: (eq T x0 (THead (Bind b) x2 x3))).(\lambda (_: (eq T u (lift h x1 
x2))).(\lambda (H7: (eq T (lift (S O) O t2) (lift h (S x1) x3))).(eq_ind_r T 
(THead (Bind b) x2 x3) (\lambda (t: T).(ex2 T (\lambda (t4: T).(eq T t3 (lift 
h x1 t4))) (\lambda (t4: T).(pr0 t t4)))) (let H8 \def (eq_ind_r nat (plus (S 
O) x1) (\lambda (n: nat).(eq nat (S x1) n)) (refl_equal nat (plus (S O) x1)) 
(plus x1 (S O)) (plus_sym x1 (S O))) in (let H9 \def (eq_ind nat (S x1) 
(\lambda (n: nat).(eq T (lift (S O) O t2) (lift h n x3))) H7 (plus x1 (S O)) 
H8) in (ex2_ind T (\lambda (t4: T).(eq T x3 (lift (S O) O t4))) (\lambda (t4: 
T).(eq T t2 (lift h x1 t4))) (ex2 T (\lambda (t4: T).(eq T t3 (lift h x1 
t4))) (\lambda (t4: T).(pr0 (THead (Bind b) x2 x3) t4))) (\lambda (x4: 
T).(\lambda (H10: (eq T x3 (lift (S O) O x4))).(\lambda (H11: (eq T t2 (lift 
h x1 x4))).(eq_ind_r T (lift (S O) O x4) (\lambda (t: T).(ex2 T (\lambda (t4: 
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
Cast) x2 x3) t4)) x4 (refl_equal T (lift h x1 x4)) (pr0_tau x3 x4 H7 x2)) t3 
H_x)))) (H2 x3 x1 H6)) x0 H4)))))) (lift_gen_flat Cast u t2 x0 h x1 
H3)))))))))) y x H0))))) H))))).
(* COMMENTS
Initial nodes: 7569
END *)

