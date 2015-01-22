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

include "Basic-1/pc3/props.ma".

include "Basic-1/pr3/fwd.ma".

theorem pc3_gen_sort:
 \forall (c: C).(\forall (m: nat).(\forall (n: nat).((pc3 c (TSort m) (TSort 
n)) \to (eq nat m n))))
\def
 \lambda (c: C).(\lambda (m: nat).(\lambda (n: nat).(\lambda (H: (pc3 c 
(TSort m) (TSort n))).(let H0 \def H in (ex2_ind T (\lambda (t: T).(pr3 c 
(TSort m) t)) (\lambda (t: T).(pr3 c (TSort n) t)) (eq nat m n) (\lambda (x: 
T).(\lambda (H1: (pr3 c (TSort m) x)).(\lambda (H2: (pr3 c (TSort n) x)).(let 
H3 \def (eq_ind T x (\lambda (t: T).(eq T t (TSort n))) (pr3_gen_sort c x n 
H2) (TSort m) (pr3_gen_sort c x m H1)) in (let H4 \def (f_equal T nat 
(\lambda (e: T).(match e in T return (\lambda (_: T).nat) with [(TSort n0) 
\Rightarrow n0 | (TLRef _) \Rightarrow m | (THead _ _ _) \Rightarrow m])) 
(TSort m) (TSort n) H3) in H4))))) H0))))).
(* COMMENTS
Initial nodes: 153
END *)

theorem pc3_gen_abst:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).(\forall (t1: T).(\forall 
(t2: T).((pc3 c (THead (Bind Abst) u1 t1) (THead (Bind Abst) u2 t2)) \to 
(land (pc3 c u1 u2) (\forall (b: B).(\forall (u: T).(pc3 (CHead c (Bind b) u) 
t1 t2)))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (t1: T).(\lambda 
(t2: T).(\lambda (H: (pc3 c (THead (Bind Abst) u1 t1) (THead (Bind Abst) u2 
t2))).(let H0 \def H in (ex2_ind T (\lambda (t: T).(pr3 c (THead (Bind Abst) 
u1 t1) t)) (\lambda (t: T).(pr3 c (THead (Bind Abst) u2 t2) t)) (land (pc3 c 
u1 u2) (\forall (b: B).(\forall (u: T).(pc3 (CHead c (Bind b) u) t1 t2)))) 
(\lambda (x: T).(\lambda (H1: (pr3 c (THead (Bind Abst) u1 t1) x)).(\lambda 
(H2: (pr3 c (THead (Bind Abst) u2 t2) x)).(let H3 \def (pr3_gen_abst c u2 t2 
x H2) in (ex3_2_ind T T (\lambda (u3: T).(\lambda (t3: T).(eq T x (THead 
(Bind Abst) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c u2 u3))) 
(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead 
c (Bind b) u) t2 t3))))) (land (pc3 c u1 u2) (\forall (b: B).(\forall (u: 
T).(pc3 (CHead c (Bind b) u) t1 t2)))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H4: (eq T x (THead (Bind Abst) x0 x1))).(\lambda (H5: (pr3 c u2 
x0)).(\lambda (H6: ((\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
t2 x1))))).(let H7 \def (pr3_gen_abst c u1 t1 x H1) in (ex3_2_ind T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Bind Abst) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr3 c u1 u3))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t1 t3))))) 
(land (pc3 c u1 u2) (\forall (b: B).(\forall (u: T).(pc3 (CHead c (Bind b) u) 
t1 t2)))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H8: (eq T x (THead 
(Bind Abst) x2 x3))).(\lambda (H9: (pr3 c u1 x2)).(\lambda (H10: ((\forall 
(b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t1 x3))))).(let H11 \def 
(eq_ind T x (\lambda (t: T).(eq T t (THead (Bind Abst) x0 x1))) H4 (THead 
(Bind Abst) x2 x3) H8) in (let H12 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x2 | (TLRef _) 
\Rightarrow x2 | (THead _ t _) \Rightarrow t])) (THead (Bind Abst) x2 x3) 
(THead (Bind Abst) x0 x1) H11) in ((let H13 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow x3 | 
(TLRef _) \Rightarrow x3 | (THead _ _ t) \Rightarrow t])) (THead (Bind Abst) 
x2 x3) (THead (Bind Abst) x0 x1) H11) in (\lambda (H14: (eq T x2 x0)).(let 
H15 \def (eq_ind T x3 (\lambda (t: T).(\forall (b: B).(\forall (u: T).(pr3 
(CHead c (Bind b) u) t1 t)))) H10 x1 H13) in (let H16 \def (eq_ind T x2 
(\lambda (t: T).(pr3 c u1 t)) H9 x0 H14) in (conj (pc3 c u1 u2) (\forall (b: 
B).(\forall (u: T).(pc3 (CHead c (Bind b) u) t1 t2))) (pc3_pr3_t c u1 x0 H16 
u2 H5) (\lambda (b: B).(\lambda (u: T).(pc3_pr3_t (CHead c (Bind b) u) t1 x1 
(H15 b u) t2 (H6 b u))))))))) H12)))))))) H7))))))) H3))))) H0))))))).
(* COMMENTS
Initial nodes: 715
END *)

theorem pc3_gen_abst_shift:
 \forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall (t2: T).((pc3 c 
(THead (Bind Abst) u t1) (THead (Bind Abst) u t2)) \to (pc3 (CHead c (Bind 
Abst) u) t1 t2)))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (pc3 c (THead (Bind Abst) u t1) (THead (Bind Abst) u t2))).(let H_x \def 
(pc3_gen_abst c u u t1 t2 H) in (let H0 \def H_x in (land_ind (pc3 c u u) 
(\forall (b: B).(\forall (u0: T).(pc3 (CHead c (Bind b) u0) t1 t2))) (pc3 
(CHead c (Bind Abst) u) t1 t2) (\lambda (_: (pc3 c u u)).(\lambda (H2: 
((\forall (b: B).(\forall (u0: T).(pc3 (CHead c (Bind b) u0) t1 t2))))).(H2 
Abst u))) H0))))))).
(* COMMENTS
Initial nodes: 129
END *)

theorem pc3_gen_lift:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).(\forall (h: nat).(\forall 
(d: nat).((pc3 c (lift h d t1) (lift h d t2)) \to (\forall (e: C).((drop h d 
c e) \to (pc3 e t1 t2))))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (H: (pc3 c (lift h d t1) (lift h d t2))).(\lambda (e: 
C).(\lambda (H0: (drop h d c e)).(let H1 \def H in (ex2_ind T (\lambda (t: 
T).(pr3 c (lift h d t1) t)) (\lambda (t: T).(pr3 c (lift h d t2) t)) (pc3 e 
t1 t2) (\lambda (x: T).(\lambda (H2: (pr3 c (lift h d t1) x)).(\lambda (H3: 
(pr3 c (lift h d t2) x)).(let H4 \def (pr3_gen_lift c t2 x h d H3 e H0) in 
(ex2_ind T (\lambda (t3: T).(eq T x (lift h d t3))) (\lambda (t3: T).(pr3 e 
t2 t3)) (pc3 e t1 t2) (\lambda (x0: T).(\lambda (H5: (eq T x (lift h d 
x0))).(\lambda (H6: (pr3 e t2 x0)).(let H7 \def (pr3_gen_lift c t1 x h d H2 e 
H0) in (ex2_ind T (\lambda (t3: T).(eq T x (lift h d t3))) (\lambda (t3: 
T).(pr3 e t1 t3)) (pc3 e t1 t2) (\lambda (x1: T).(\lambda (H8: (eq T x (lift 
h d x1))).(\lambda (H9: (pr3 e t1 x1)).(let H10 \def (eq_ind T x (\lambda (t: 
T).(eq T t (lift h d x0))) H5 (lift h d x1) H8) in (let H11 \def (eq_ind T x1 
(\lambda (t: T).(pr3 e t1 t)) H9 x0 (lift_inj x1 x0 h d H10)) in (pc3_pr3_t e 
t1 x0 H11 t2 H6)))))) H7))))) H4))))) H1))))))))).
(* COMMENTS
Initial nodes: 363
END *)

theorem pc3_gen_not_abst:
 \forall (b: B).((not (eq B b Abst)) \to (\forall (c: C).(\forall (t1: 
T).(\forall (t2: T).(\forall (u1: T).(\forall (u2: T).((pc3 c (THead (Bind b) 
u1 t1) (THead (Bind Abst) u2 t2)) \to (pc3 (CHead c (Bind b) u1) t1 (lift (S 
O) O (THead (Bind Abst) u2 t2))))))))))
\def
 \lambda (b: B).(B_ind (\lambda (b0: B).((not (eq B b0 Abst)) \to (\forall 
(c: C).(\forall (t1: T).(\forall (t2: T).(\forall (u1: T).(\forall (u2: 
T).((pc3 c (THead (Bind b0) u1 t1) (THead (Bind Abst) u2 t2)) \to (pc3 (CHead 
c (Bind b0) u1) t1 (lift (S O) O (THead (Bind Abst) u2 t2))))))))))) (\lambda 
(_: (not (eq B Abbr Abst))).(\lambda (c: C).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H0: (pc3 c (THead (Bind Abbr) 
u1 t1) (THead (Bind Abst) u2 t2))).(let H1 \def H0 in (ex2_ind T (\lambda (t: 
T).(pr3 c (THead (Bind Abbr) u1 t1) t)) (\lambda (t: T).(pr3 c (THead (Bind 
Abst) u2 t2) t)) (pc3 (CHead c (Bind Abbr) u1) t1 (lift (S O) O (THead (Bind 
Abst) u2 t2))) (\lambda (x: T).(\lambda (H2: (pr3 c (THead (Bind Abbr) u1 t1) 
x)).(\lambda (H3: (pr3 c (THead (Bind Abst) u2 t2) x)).(let H4 \def 
(pr3_gen_abbr c u1 t1 x H2) in (or_ind (ex3_2 T T (\lambda (u3: T).(\lambda 
(t3: T).(eq T x (THead (Bind Abbr) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr3 c u1 u3))) (\lambda (_: T).(\lambda (t3: T).(pr3 (CHead c (Bind Abbr) 
u1) t1 t3)))) (pr3 (CHead c (Bind Abbr) u1) t1 (lift (S O) O x)) (pc3 (CHead 
c (Bind Abbr) u1) t1 (lift (S O) O (THead (Bind Abst) u2 t2))) (\lambda (H5: 
(ex3_2 T T (\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u3 
t3)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c u1 u3))) (\lambda (_: 
T).(\lambda (t3: T).(pr3 (CHead c (Bind Abbr) u1) t1 t3))))).(ex3_2_ind T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Bind Abbr) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr3 c u1 u3))) (\lambda (_: T).(\lambda 
(t3: T).(pr3 (CHead c (Bind Abbr) u1) t1 t3))) (pc3 (CHead c (Bind Abbr) u1) 
t1 (lift (S O) O (THead (Bind Abst) u2 t2))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H6: (eq T x (THead (Bind Abbr) x0 x1))).(\lambda (_: (pr3 c u1 
x0)).(\lambda (_: (pr3 (CHead c (Bind Abbr) u1) t1 x1)).(let H9 \def 
(pr3_gen_abst c u2 t2 x H3) in (ex3_2_ind T T (\lambda (u3: T).(\lambda (t3: 
T).(eq T x (THead (Bind Abst) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr3 
c u2 u3))) (\lambda (_: T).(\lambda (t3: T).(\forall (b0: B).(\forall (u: 
T).(pr3 (CHead c (Bind b0) u) t2 t3))))) (pc3 (CHead c (Bind Abbr) u1) t1 
(lift (S O) O (THead (Bind Abst) u2 t2))) (\lambda (x2: T).(\lambda (x3: 
T).(\lambda (H10: (eq T x (THead (Bind Abst) x2 x3))).(\lambda (_: (pr3 c u2 
x2)).(\lambda (_: ((\forall (b0: B).(\forall (u: T).(pr3 (CHead c (Bind b0) 
u) t2 x3))))).(let H13 \def (eq_ind T x (\lambda (t: T).(eq T t (THead (Bind 
Abbr) x0 x1))) H6 (THead (Bind Abst) x2 x3) H10) in (let H14 \def (eq_ind T 
(THead (Bind Abst) x2 x3) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind b0) \Rightarrow (match b0 in B return (\lambda (_: B).Prop) with [Abbr 
\Rightarrow False | Abst \Rightarrow True | Void \Rightarrow False]) | (Flat 
_) \Rightarrow False])])) I (THead (Bind Abbr) x0 x1) H13) in (False_ind (pc3 
(CHead c (Bind Abbr) u1) t1 (lift (S O) O (THead (Bind Abst) u2 t2))) 
H14)))))))) H9))))))) H5)) (\lambda (H5: (pr3 (CHead c (Bind Abbr) u1) t1 
(lift (S O) O x))).(let H6 \def (pr3_gen_abst c u2 t2 x H3) in (ex3_2_ind T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Bind Abst) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr3 c u2 u3))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b0: B).(\forall (u: T).(pr3 (CHead c (Bind b0) u) t2 
t3))))) (pc3 (CHead c (Bind Abbr) u1) t1 (lift (S O) O (THead (Bind Abst) u2 
t2))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H7: (eq T x (THead (Bind 
Abst) x0 x1))).(\lambda (H8: (pr3 c u2 x0)).(\lambda (H9: ((\forall (b0: 
B).(\forall (u: T).(pr3 (CHead c (Bind b0) u) t2 x1))))).(let H10 \def 
(eq_ind T x (\lambda (t: T).(pr3 (CHead c (Bind Abbr) u1) t1 (lift (S O) O 
t))) H5 (THead (Bind Abst) x0 x1) H7) in (pc3_pr3_t (CHead c (Bind Abbr) u1) 
t1 (lift (S O) O (THead (Bind Abst) x0 x1)) H10 (lift (S O) O (THead (Bind 
Abst) u2 t2)) (pr3_lift (CHead c (Bind Abbr) u1) c (S O) O (drop_drop (Bind 
Abbr) O c c (drop_refl c) u1) (THead (Bind Abst) u2 t2) (THead (Bind Abst) x0 
x1) (pr3_head_12 c u2 x0 H8 (Bind Abst) t2 x1 (H9 Abst x0)))))))))) H6))) 
H4))))) H1))))))))) (\lambda (H: (not (eq B Abst Abst))).(\lambda (c: 
C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (_: (pc3 c (THead (Bind Abst) u1 t1) (THead (Bind Abst) u2 
t2))).(let H1 \def (match (H (refl_equal B Abst)) in False return (\lambda 
(_: False).(pc3 (CHead c (Bind Abst) u1) t1 (lift (S O) O (THead (Bind Abst) 
u2 t2)))) with []) in H1)))))))) (\lambda (_: (not (eq B Void 
Abst))).(\lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (u1: 
T).(\lambda (u2: T).(\lambda (H0: (pc3 c (THead (Bind Void) u1 t1) (THead 
(Bind Abst) u2 t2))).(let H1 \def H0 in (ex2_ind T (\lambda (t: T).(pr3 c 
(THead (Bind Void) u1 t1) t)) (\lambda (t: T).(pr3 c (THead (Bind Abst) u2 
t2) t)) (pc3 (CHead c (Bind Void) u1) t1 (lift (S O) O (THead (Bind Abst) u2 
t2))) (\lambda (x: T).(\lambda (H2: (pr3 c (THead (Bind Void) u1 t1) 
x)).(\lambda (H3: (pr3 c (THead (Bind Abst) u2 t2) x)).(let H4 \def 
(pr3_gen_void c u1 t1 x H2) in (or_ind (ex3_2 T T (\lambda (u3: T).(\lambda 
(t3: T).(eq T x (THead (Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda (_: 
T).(pr3 c u1 u3))) (\lambda (_: T).(\lambda (t3: T).(\forall (b0: B).(\forall 
(u: T).(pr3 (CHead c (Bind b0) u) t1 t3)))))) (pr3 (CHead c (Bind Void) u1) 
t1 (lift (S O) O x)) (pc3 (CHead c (Bind Void) u1) t1 (lift (S O) O (THead 
(Bind Abst) u2 t2))) (\lambda (H5: (ex3_2 T T (\lambda (u3: T).(\lambda (t3: 
T).(eq T x (THead (Bind Void) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr3 
c u1 u3))) (\lambda (_: T).(\lambda (t3: T).(\forall (b0: B).(\forall (u: 
T).(pr3 (CHead c (Bind b0) u) t1 t3))))))).(ex3_2_ind T T (\lambda (u3: 
T).(\lambda (t3: T).(eq T x (THead (Bind Void) u3 t3)))) (\lambda (u3: 
T).(\lambda (_: T).(pr3 c u1 u3))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b0: B).(\forall (u: T).(pr3 (CHead c (Bind b0) u) t1 t3))))) (pc3 (CHead c 
(Bind Void) u1) t1 (lift (S O) O (THead (Bind Abst) u2 t2))) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H6: (eq T x (THead (Bind Void) x0 
x1))).(\lambda (_: (pr3 c u1 x0)).(\lambda (_: ((\forall (b0: B).(\forall (u: 
T).(pr3 (CHead c (Bind b0) u) t1 x1))))).(let H9 \def (pr3_gen_abst c u2 t2 x 
H3) in (ex3_2_ind T T (\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Bind 
Abst) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c u2 u3))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b0: B).(\forall (u: T).(pr3 (CHead c (Bind b0) 
u) t2 t3))))) (pc3 (CHead c (Bind Void) u1) t1 (lift (S O) O (THead (Bind 
Abst) u2 t2))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H10: (eq T x 
(THead (Bind Abst) x2 x3))).(\lambda (_: (pr3 c u2 x2)).(\lambda (_: 
((\forall (b0: B).(\forall (u: T).(pr3 (CHead c (Bind b0) u) t2 x3))))).(let 
H13 \def (eq_ind T x (\lambda (t: T).(eq T t (THead (Bind Void) x0 x1))) H6 
(THead (Bind Abst) x2 x3) H10) in (let H14 \def (eq_ind T (THead (Bind Abst) 
x2 x3) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind b0) 
\Rightarrow (match b0 in B return (\lambda (_: B).Prop) with [Abbr 
\Rightarrow False | Abst \Rightarrow True | Void \Rightarrow False]) | (Flat 
_) \Rightarrow False])])) I (THead (Bind Void) x0 x1) H13) in (False_ind (pc3 
(CHead c (Bind Void) u1) t1 (lift (S O) O (THead (Bind Abst) u2 t2))) 
H14)))))))) H9))))))) H5)) (\lambda (H5: (pr3 (CHead c (Bind Void) u1) t1 
(lift (S O) O x))).(let H6 \def (pr3_gen_abst c u2 t2 x H3) in (ex3_2_ind T T 
(\lambda (u3: T).(\lambda (t3: T).(eq T x (THead (Bind Abst) u3 t3)))) 
(\lambda (u3: T).(\lambda (_: T).(pr3 c u2 u3))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b0: B).(\forall (u: T).(pr3 (CHead c (Bind b0) u) t2 
t3))))) (pc3 (CHead c (Bind Void) u1) t1 (lift (S O) O (THead (Bind Abst) u2 
t2))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H7: (eq T x (THead (Bind 
Abst) x0 x1))).(\lambda (H8: (pr3 c u2 x0)).(\lambda (H9: ((\forall (b0: 
B).(\forall (u: T).(pr3 (CHead c (Bind b0) u) t2 x1))))).(let H10 \def 
(eq_ind T x (\lambda (t: T).(pr3 (CHead c (Bind Void) u1) t1 (lift (S O) O 
t))) H5 (THead (Bind Abst) x0 x1) H7) in (pc3_pr3_t (CHead c (Bind Void) u1) 
t1 (lift (S O) O (THead (Bind Abst) x0 x1)) H10 (lift (S O) O (THead (Bind 
Abst) u2 t2)) (pr3_lift (CHead c (Bind Void) u1) c (S O) O (drop_drop (Bind 
Void) O c c (drop_refl c) u1) (THead (Bind Abst) u2 t2) (THead (Bind Abst) x0 
x1) (pr3_head_12 c u2 x0 H8 (Bind Abst) t2 x1 (H9 Abst x0)))))))))) H6))) 
H4))))) H1))))))))) b).
(* COMMENTS
Initial nodes: 2427
END *)

theorem pc3_gen_lift_abst:
 \forall (c: C).(\forall (t: T).(\forall (t2: T).(\forall (u2: T).(\forall 
(h: nat).(\forall (d: nat).((pc3 c (lift h d t) (THead (Bind Abst) u2 t2)) 
\to (\forall (e: C).((drop h d c e) \to (ex3_2 T T (\lambda (u1: T).(\lambda 
(t1: T).(pr3 e t (THead (Bind Abst) u1 t1)))) (\lambda (u1: T).(\lambda (_: 
T).(pr3 c u2 (lift h d u1)))) (\lambda (_: T).(\lambda (t1: T).(\forall (b: 
B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t2 (lift h (S d) 
t1)))))))))))))))
\def
 \lambda (c: C).(\lambda (t: T).(\lambda (t2: T).(\lambda (u2: T).(\lambda 
(h: nat).(\lambda (d: nat).(\lambda (H: (pc3 c (lift h d t) (THead (Bind 
Abst) u2 t2))).(\lambda (e: C).(\lambda (H0: (drop h d c e)).(let H1 \def H 
in (ex2_ind T (\lambda (t0: T).(pr3 c (lift h d t) t0)) (\lambda (t0: T).(pr3 
c (THead (Bind Abst) u2 t2) t0)) (ex3_2 T T (\lambda (u1: T).(\lambda (t1: 
T).(pr3 e t (THead (Bind Abst) u1 t1)))) (\lambda (u1: T).(\lambda (_: 
T).(pr3 c u2 (lift h d u1)))) (\lambda (_: T).(\lambda (t1: T).(\forall (b: 
B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t2 (lift h (S d) t1))))))) 
(\lambda (x: T).(\lambda (H2: (pr3 c (lift h d t) x)).(\lambda (H3: (pr3 c 
(THead (Bind Abst) u2 t2) x)).(let H4 \def (pr3_gen_lift c t x h d H2 e H0) 
in (ex2_ind T (\lambda (t3: T).(eq T x (lift h d t3))) (\lambda (t3: T).(pr3 
e t t3)) (ex3_2 T T (\lambda (u1: T).(\lambda (t1: T).(pr3 e t (THead (Bind 
Abst) u1 t1)))) (\lambda (u1: T).(\lambda (_: T).(pr3 c u2 (lift h d u1)))) 
(\lambda (_: T).(\lambda (t1: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead 
c (Bind b) u) t2 (lift h (S d) t1))))))) (\lambda (x0: T).(\lambda (H5: (eq T 
x (lift h d x0))).(\lambda (H6: (pr3 e t x0)).(let H7 \def (pr3_gen_abst c u2 
t2 x H3) in (ex3_2_ind T T (\lambda (u3: T).(\lambda (t3: T).(eq T x (THead 
(Bind Abst) u3 t3)))) (\lambda (u3: T).(\lambda (_: T).(pr3 c u2 u3))) 
(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead 
c (Bind b) u) t2 t3))))) (ex3_2 T T (\lambda (u1: T).(\lambda (t1: T).(pr3 e 
t (THead (Bind Abst) u1 t1)))) (\lambda (u1: T).(\lambda (_: T).(pr3 c u2 
(lift h d u1)))) (\lambda (_: T).(\lambda (t1: T).(\forall (b: B).(\forall 
(u: T).(pr3 (CHead c (Bind b) u) t2 (lift h (S d) t1))))))) (\lambda (x1: 
T).(\lambda (x2: T).(\lambda (H8: (eq T x (THead (Bind Abst) x1 
x2))).(\lambda (H9: (pr3 c u2 x1)).(\lambda (H10: ((\forall (b: B).(\forall 
(u: T).(pr3 (CHead c (Bind b) u) t2 x2))))).(let H11 \def (eq_ind T x 
(\lambda (t0: T).(eq T t0 (lift h d x0))) H5 (THead (Bind Abst) x1 x2) H8) in 
(ex3_2_ind T T (\lambda (y: T).(\lambda (z: T).(eq T x0 (THead (Bind Abst) y 
z)))) (\lambda (y: T).(\lambda (_: T).(eq T x1 (lift h d y)))) (\lambda (_: 
T).(\lambda (z: T).(eq T x2 (lift h (S d) z)))) (ex3_2 T T (\lambda (u1: 
T).(\lambda (t1: T).(pr3 e t (THead (Bind Abst) u1 t1)))) (\lambda (u1: 
T).(\lambda (_: T).(pr3 c u2 (lift h d u1)))) (\lambda (_: T).(\lambda (t1: 
T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t2 (lift h (S d) 
t1))))))) (\lambda (x3: T).(\lambda (x4: T).(\lambda (H12: (eq T x0 (THead 
(Bind Abst) x3 x4))).(\lambda (H13: (eq T x1 (lift h d x3))).(\lambda (H14: 
(eq T x2 (lift h (S d) x4))).(let H15 \def (eq_ind T x2 (\lambda (t0: 
T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) t2 t0)))) H10 
(lift h (S d) x4) H14) in (let H16 \def (eq_ind T x1 (\lambda (t0: T).(pr3 c 
u2 t0)) H9 (lift h d x3) H13) in (let H17 \def (eq_ind T x0 (\lambda (t0: 
T).(pr3 e t t0)) H6 (THead (Bind Abst) x3 x4) H12) in (ex3_2_intro T T 
(\lambda (u1: T).(\lambda (t1: T).(pr3 e t (THead (Bind Abst) u1 t1)))) 
(\lambda (u1: T).(\lambda (_: T).(pr3 c u2 (lift h d u1)))) (\lambda (_: 
T).(\lambda (t1: T).(\forall (b: B).(\forall (u: T).(pr3 (CHead c (Bind b) u) 
t2 (lift h (S d) t1)))))) x3 x4 H17 H16 H15))))))))) (lift_gen_bind Abst x1 
x2 x0 h d H11)))))))) H7))))) H4))))) H1)))))))))).
(* COMMENTS
Initial nodes: 973
END *)

theorem pc3_gen_sort_abst:
 \forall (c: C).(\forall (u: T).(\forall (t: T).(\forall (n: nat).((pc3 c 
(TSort n) (THead (Bind Abst) u t)) \to (\forall (P: Prop).P)))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (n: nat).(\lambda 
(H: (pc3 c (TSort n) (THead (Bind Abst) u t))).(\lambda (P: Prop).(let H0 
\def H in (ex2_ind T (\lambda (t0: T).(pr3 c (TSort n) t0)) (\lambda (t0: 
T).(pr3 c (THead (Bind Abst) u t) t0)) P (\lambda (x: T).(\lambda (H1: (pr3 c 
(TSort n) x)).(\lambda (H2: (pr3 c (THead (Bind Abst) u t) x)).(let H3 \def 
(pr3_gen_abst c u t x H2) in (ex3_2_ind T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T x (THead (Bind Abst) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(pr3 
c u u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall (u0: 
T).(pr3 (CHead c (Bind b) u0) t t2))))) P (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H4: (eq T x (THead (Bind Abst) x0 x1))).(\lambda (_: (pr3 c u 
x0)).(\lambda (_: ((\forall (b: B).(\forall (u0: T).(pr3 (CHead c (Bind b) 
u0) t x1))))).(let H7 \def (eq_ind T x (\lambda (t0: T).(eq T t0 (TSort n))) 
(pr3_gen_sort c x n H1) (THead (Bind Abst) x0 x1) H4) in (let H8 \def (eq_ind 
T (THead (Bind Abst) x0 x1) (\lambda (ee: T).(match ee in T return (\lambda 
(_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False 
| (THead _ _ _) \Rightarrow True])) I (TSort n) H7) in (False_ind P 
H8)))))))) H3))))) H0))))))).
(* COMMENTS
Initial nodes: 303
END *)

