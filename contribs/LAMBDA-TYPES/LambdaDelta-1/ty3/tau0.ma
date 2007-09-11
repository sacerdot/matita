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

set "baseuri" "cic:/matita/LAMBDA-TYPES/LambdaDelta-1/ty3/tau0".

include "ty3/pr3_props.ma".

include "tau0/defs.ma".

theorem ty3_tau0:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t1: T).((ty3 g c u 
t1) \to (\forall (t2: T).((tau0 g c u t2) \to (ty3 g c u t2)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda (H: 
(ty3 g c u t1)).(ty3_ind g (\lambda (c0: C).(\lambda (t: T).(\lambda (_: 
T).(\forall (t2: T).((tau0 g c0 t t2) \to (ty3 g c0 t t2)))))) (\lambda (c0: 
C).(\lambda (t2: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 t2 t)).(\lambda 
(_: ((\forall (t3: T).((tau0 g c0 t2 t3) \to (ty3 g c0 t2 t3))))).(\lambda 
(u0: T).(\lambda (t3: T).(\lambda (_: (ty3 g c0 u0 t3)).(\lambda (H3: 
((\forall (t4: T).((tau0 g c0 u0 t4) \to (ty3 g c0 u0 t4))))).(\lambda (_: 
(pc3 c0 t3 t2)).(\lambda (t0: T).(\lambda (H5: (tau0 g c0 u0 t0)).(H3 t0 
H5))))))))))))) (\lambda (c0: C).(\lambda (m: nat).(\lambda (t2: T).(\lambda 
(H0: (tau0 g c0 (TSort m) t2)).(let H1 \def (match H0 in tau0 return (\lambda 
(c1: C).(\lambda (t: T).(\lambda (t0: T).(\lambda (_: (tau0 ? c1 t t0)).((eq 
C c1 c0) \to ((eq T t (TSort m)) \to ((eq T t0 t2) \to (ty3 g c0 (TSort m) 
t2)))))))) with [(tau0_sort c1 n) \Rightarrow (\lambda (H1: (eq C c1 
c0)).(\lambda (H2: (eq T (TSort n) (TSort m))).(\lambda (H3: (eq T (TSort 
(next g n)) t2)).(eq_ind C c0 (\lambda (_: C).((eq T (TSort n) (TSort m)) \to 
((eq T (TSort (next g n)) t2) \to (ty3 g c0 (TSort m) t2)))) (\lambda (H4: 
(eq T (TSort n) (TSort m))).(let H5 \def (f_equal T nat (\lambda (e: 
T).(match e in T return (\lambda (_: T).nat) with [(TSort n0) \Rightarrow n0 
| (TLRef _) \Rightarrow n | (THead _ _ _) \Rightarrow n])) (TSort n) (TSort 
m) H4) in (eq_ind nat m (\lambda (n0: nat).((eq T (TSort (next g n0)) t2) \to 
(ty3 g c0 (TSort m) t2))) (\lambda (H6: (eq T (TSort (next g m)) t2)).(eq_ind 
T (TSort (next g m)) (\lambda (t: T).(ty3 g c0 (TSort m) t)) (ty3_sort g c0 
m) t2 H6)) n (sym_eq nat n m H5)))) c1 (sym_eq C c1 c0 H1) H2 H3)))) | 
(tau0_abbr c1 d v i H1 w H2) \Rightarrow (\lambda (H3: (eq C c1 c0)).(\lambda 
(H4: (eq T (TLRef i) (TSort m))).(\lambda (H5: (eq T (lift (S i) O w) 
t2)).(eq_ind C c0 (\lambda (c2: C).((eq T (TLRef i) (TSort m)) \to ((eq T 
(lift (S i) O w) t2) \to ((getl i c2 (CHead d (Bind Abbr) v)) \to ((tau0 g d 
v w) \to (ty3 g c0 (TSort m) t2)))))) (\lambda (H6: (eq T (TLRef i) (TSort 
m))).(let H7 \def (eq_ind T (TLRef i) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (TSort m) H6) in 
(False_ind ((eq T (lift (S i) O w) t2) \to ((getl i c0 (CHead d (Bind Abbr) 
v)) \to ((tau0 g d v w) \to (ty3 g c0 (TSort m) t2)))) H7))) c1 (sym_eq C c1 
c0 H3) H4 H5 H1 H2)))) | (tau0_abst c1 d v i H1 w H2) \Rightarrow (\lambda 
(H3: (eq C c1 c0)).(\lambda (H4: (eq T (TLRef i) (TSort m))).(\lambda (H5: 
(eq T (lift (S i) O v) t2)).(eq_ind C c0 (\lambda (c2: C).((eq T (TLRef i) 
(TSort m)) \to ((eq T (lift (S i) O v) t2) \to ((getl i c2 (CHead d (Bind 
Abst) v)) \to ((tau0 g d v w) \to (ty3 g c0 (TSort m) t2)))))) (\lambda (H6: 
(eq T (TLRef i) (TSort m))).(let H7 \def (eq_ind T (TLRef i) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) I 
(TSort m) H6) in (False_ind ((eq T (lift (S i) O v) t2) \to ((getl i c0 
(CHead d (Bind Abst) v)) \to ((tau0 g d v w) \to (ty3 g c0 (TSort m) t2)))) 
H7))) c1 (sym_eq C c1 c0 H3) H4 H5 H1 H2)))) | (tau0_bind b c1 v t0 t3 H1) 
\Rightarrow (\lambda (H2: (eq C c1 c0)).(\lambda (H3: (eq T (THead (Bind b) v 
t0) (TSort m))).(\lambda (H4: (eq T (THead (Bind b) v t3) t2)).(eq_ind C c0 
(\lambda (c2: C).((eq T (THead (Bind b) v t0) (TSort m)) \to ((eq T (THead 
(Bind b) v t3) t2) \to ((tau0 g (CHead c2 (Bind b) v) t0 t3) \to (ty3 g c0 
(TSort m) t2))))) (\lambda (H5: (eq T (THead (Bind b) v t0) (TSort m))).(let 
H6 \def (eq_ind T (THead (Bind b) v t0) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort m) H5) in 
(False_ind ((eq T (THead (Bind b) v t3) t2) \to ((tau0 g (CHead c0 (Bind b) 
v) t0 t3) \to (ty3 g c0 (TSort m) t2))) H6))) c1 (sym_eq C c1 c0 H2) H3 H4 
H1)))) | (tau0_appl c1 v t0 t3 H1) \Rightarrow (\lambda (H2: (eq C c1 
c0)).(\lambda (H3: (eq T (THead (Flat Appl) v t0) (TSort m))).(\lambda (H4: 
(eq T (THead (Flat Appl) v t3) t2)).(eq_ind C c0 (\lambda (c2: C).((eq T 
(THead (Flat Appl) v t0) (TSort m)) \to ((eq T (THead (Flat Appl) v t3) t2) 
\to ((tau0 g c2 t0 t3) \to (ty3 g c0 (TSort m) t2))))) (\lambda (H5: (eq T 
(THead (Flat Appl) v t0) (TSort m))).(let H6 \def (eq_ind T (THead (Flat 
Appl) v t0) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) I (TSort m) H5) in (False_ind ((eq T (THead (Flat Appl) v 
t3) t2) \to ((tau0 g c0 t0 t3) \to (ty3 g c0 (TSort m) t2))) H6))) c1 (sym_eq 
C c1 c0 H2) H3 H4 H1)))) | (tau0_cast c1 v1 v2 H1 t0 t3 H2) \Rightarrow 
(\lambda (H3: (eq C c1 c0)).(\lambda (H4: (eq T (THead (Flat Cast) v1 t0) 
(TSort m))).(\lambda (H5: (eq T (THead (Flat Cast) v2 t3) t2)).(eq_ind C c0 
(\lambda (c2: C).((eq T (THead (Flat Cast) v1 t0) (TSort m)) \to ((eq T 
(THead (Flat Cast) v2 t3) t2) \to ((tau0 g c2 v1 v2) \to ((tau0 g c2 t0 t3) 
\to (ty3 g c0 (TSort m) t2)))))) (\lambda (H6: (eq T (THead (Flat Cast) v1 
t0) (TSort m))).(let H7 \def (eq_ind T (THead (Flat Cast) v1 t0) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(TSort m) H6) in (False_ind ((eq T (THead (Flat Cast) v2 t3) t2) \to ((tau0 g 
c0 v1 v2) \to ((tau0 g c0 t0 t3) \to (ty3 g c0 (TSort m) t2)))) H7))) c1 
(sym_eq C c1 c0 H3) H4 H5 H1 H2))))]) in (H1 (refl_equal C c0) (refl_equal T 
(TSort m)) (refl_equal T t2))))))) (\lambda (n: nat).(\lambda (c0: 
C).(\lambda (d: C).(\lambda (u0: T).(\lambda (H0: (getl n c0 (CHead d (Bind 
Abbr) u0))).(\lambda (t: T).(\lambda (_: (ty3 g d u0 t)).(\lambda (H2: 
((\forall (t2: T).((tau0 g d u0 t2) \to (ty3 g d u0 t2))))).(\lambda (t2: 
T).(\lambda (H3: (tau0 g c0 (TLRef n) t2)).(let H4 \def (match H3 in tau0 
return (\lambda (c1: C).(\lambda (t0: T).(\lambda (t3: T).(\lambda (_: (tau0 
? c1 t0 t3)).((eq C c1 c0) \to ((eq T t0 (TLRef n)) \to ((eq T t3 t2) \to 
(ty3 g c0 (TLRef n) t2)))))))) with [(tau0_sort c1 n0) \Rightarrow (\lambda 
(H4: (eq C c1 c0)).(\lambda (H5: (eq T (TSort n0) (TLRef n))).(\lambda (H6: 
(eq T (TSort (next g n0)) t2)).(eq_ind C c0 (\lambda (_: C).((eq T (TSort n0) 
(TLRef n)) \to ((eq T (TSort (next g n0)) t2) \to (ty3 g c0 (TLRef n) t2)))) 
(\lambda (H7: (eq T (TSort n0) (TLRef n))).(let H8 \def (eq_ind T (TSort n0) 
(\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
False])) I (TLRef n) H7) in (False_ind ((eq T (TSort (next g n0)) t2) \to 
(ty3 g c0 (TLRef n) t2)) H8))) c1 (sym_eq C c1 c0 H4) H5 H6)))) | (tau0_abbr 
c1 d0 v i H4 w H5) \Rightarrow (\lambda (H6: (eq C c1 c0)).(\lambda (H7: (eq 
T (TLRef i) (TLRef n))).(\lambda (H8: (eq T (lift (S i) O w) t2)).(eq_ind C 
c0 (\lambda (c2: C).((eq T (TLRef i) (TLRef n)) \to ((eq T (lift (S i) O w) 
t2) \to ((getl i c2 (CHead d0 (Bind Abbr) v)) \to ((tau0 g d0 v w) \to (ty3 g 
c0 (TLRef n) t2)))))) (\lambda (H9: (eq T (TLRef i) (TLRef n))).(let H10 \def 
(f_equal T nat (\lambda (e: T).(match e in T return (\lambda (_: T).nat) with 
[(TSort _) \Rightarrow i | (TLRef n0) \Rightarrow n0 | (THead _ _ _) 
\Rightarrow i])) (TLRef i) (TLRef n) H9) in (eq_ind nat n (\lambda (n0: 
nat).((eq T (lift (S n0) O w) t2) \to ((getl n0 c0 (CHead d0 (Bind Abbr) v)) 
\to ((tau0 g d0 v w) \to (ty3 g c0 (TLRef n) t2))))) (\lambda (H11: (eq T 
(lift (S n) O w) t2)).(eq_ind T (lift (S n) O w) (\lambda (t0: T).((getl n c0 
(CHead d0 (Bind Abbr) v)) \to ((tau0 g d0 v w) \to (ty3 g c0 (TLRef n) t0)))) 
(\lambda (H12: (getl n c0 (CHead d0 (Bind Abbr) v))).(\lambda (H13: (tau0 g 
d0 v w)).(let H14 \def (eq_ind C (CHead d (Bind Abbr) u0) (\lambda (c2: 
C).(getl n c0 c2)) H0 (CHead d0 (Bind Abbr) v) (getl_mono c0 (CHead d (Bind 
Abbr) u0) n H0 (CHead d0 (Bind Abbr) v) H12)) in (let H15 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow d | (CHead c2 _ _) \Rightarrow c2])) (CHead d (Bind Abbr) u0) 
(CHead d0 (Bind Abbr) v) (getl_mono c0 (CHead d (Bind Abbr) u0) n H0 (CHead 
d0 (Bind Abbr) v) H12)) in ((let H16 \def (f_equal C T (\lambda (e: C).(match 
e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | (CHead _ _ 
t0) \Rightarrow t0])) (CHead d (Bind Abbr) u0) (CHead d0 (Bind Abbr) v) 
(getl_mono c0 (CHead d (Bind Abbr) u0) n H0 (CHead d0 (Bind Abbr) v) H12)) in 
(\lambda (H17: (eq C d d0)).(let H18 \def (eq_ind_r T v (\lambda (t0: 
T).(getl n c0 (CHead d0 (Bind Abbr) t0))) H14 u0 H16) in (let H19 \def 
(eq_ind_r T v (\lambda (t0: T).(tau0 g d0 t0 w)) H13 u0 H16) in (let H20 \def 
(eq_ind_r C d0 (\lambda (c2: C).(getl n c0 (CHead c2 (Bind Abbr) u0))) H18 d 
H17) in (let H21 \def (eq_ind_r C d0 (\lambda (c2: C).(tau0 g c2 u0 w)) H19 d 
H17) in (ty3_abbr g n c0 d u0 H20 w (H2 w H21)))))))) H15))))) t2 H11)) i 
(sym_eq nat i n H10)))) c1 (sym_eq C c1 c0 H6) H7 H8 H4 H5)))) | (tau0_abst 
c1 d0 v i H4 w H5) \Rightarrow (\lambda (H6: (eq C c1 c0)).(\lambda (H7: (eq 
T (TLRef i) (TLRef n))).(\lambda (H8: (eq T (lift (S i) O v) t2)).(eq_ind C 
c0 (\lambda (c2: C).((eq T (TLRef i) (TLRef n)) \to ((eq T (lift (S i) O v) 
t2) \to ((getl i c2 (CHead d0 (Bind Abst) v)) \to ((tau0 g d0 v w) \to (ty3 g 
c0 (TLRef n) t2)))))) (\lambda (H9: (eq T (TLRef i) (TLRef n))).(let H10 \def 
(f_equal T nat (\lambda (e: T).(match e in T return (\lambda (_: T).nat) with 
[(TSort _) \Rightarrow i | (TLRef n0) \Rightarrow n0 | (THead _ _ _) 
\Rightarrow i])) (TLRef i) (TLRef n) H9) in (eq_ind nat n (\lambda (n0: 
nat).((eq T (lift (S n0) O v) t2) \to ((getl n0 c0 (CHead d0 (Bind Abst) v)) 
\to ((tau0 g d0 v w) \to (ty3 g c0 (TLRef n) t2))))) (\lambda (H11: (eq T 
(lift (S n) O v) t2)).(eq_ind T (lift (S n) O v) (\lambda (t0: T).((getl n c0 
(CHead d0 (Bind Abst) v)) \to ((tau0 g d0 v w) \to (ty3 g c0 (TLRef n) t0)))) 
(\lambda (H12: (getl n c0 (CHead d0 (Bind Abst) v))).(\lambda (_: (tau0 g d0 
v w)).(let H14 \def (eq_ind C (CHead d (Bind Abbr) u0) (\lambda (c2: C).(getl 
n c0 c2)) H0 (CHead d0 (Bind Abst) v) (getl_mono c0 (CHead d (Bind Abbr) u0) 
n H0 (CHead d0 (Bind Abst) v) H12)) in (let H15 \def (eq_ind C (CHead d (Bind 
Abbr) u0) (\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with 
[(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind b) \Rightarrow (match b in B return 
(\lambda (_: B).Prop) with [Abbr \Rightarrow True | Abst \Rightarrow False | 
Void \Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead d0 (Bind 
Abst) v) (getl_mono c0 (CHead d (Bind Abbr) u0) n H0 (CHead d0 (Bind Abst) v) 
H12)) in (False_ind (ty3 g c0 (TLRef n) (lift (S n) O v)) H15))))) t2 H11)) i 
(sym_eq nat i n H10)))) c1 (sym_eq C c1 c0 H6) H7 H8 H4 H5)))) | (tau0_bind b 
c1 v t0 t3 H4) \Rightarrow (\lambda (H5: (eq C c1 c0)).(\lambda (H6: (eq T 
(THead (Bind b) v t0) (TLRef n))).(\lambda (H7: (eq T (THead (Bind b) v t3) 
t2)).(eq_ind C c0 (\lambda (c2: C).((eq T (THead (Bind b) v t0) (TLRef n)) 
\to ((eq T (THead (Bind b) v t3) t2) \to ((tau0 g (CHead c2 (Bind b) v) t0 
t3) \to (ty3 g c0 (TLRef n) t2))))) (\lambda (H8: (eq T (THead (Bind b) v t0) 
(TLRef n))).(let H9 \def (eq_ind T (THead (Bind b) v t0) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(TLRef n) H8) in (False_ind ((eq T (THead (Bind b) v t3) t2) \to ((tau0 g 
(CHead c0 (Bind b) v) t0 t3) \to (ty3 g c0 (TLRef n) t2))) H9))) c1 (sym_eq C 
c1 c0 H5) H6 H7 H4)))) | (tau0_appl c1 v t0 t3 H4) \Rightarrow (\lambda (H5: 
(eq C c1 c0)).(\lambda (H6: (eq T (THead (Flat Appl) v t0) (TLRef 
n))).(\lambda (H7: (eq T (THead (Flat Appl) v t3) t2)).(eq_ind C c0 (\lambda 
(c2: C).((eq T (THead (Flat Appl) v t0) (TLRef n)) \to ((eq T (THead (Flat 
Appl) v t3) t2) \to ((tau0 g c2 t0 t3) \to (ty3 g c0 (TLRef n) t2))))) 
(\lambda (H8: (eq T (THead (Flat Appl) v t0) (TLRef n))).(let H9 \def (eq_ind 
T (THead (Flat Appl) v t0) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow True])) I (TLRef n) H8) in (False_ind ((eq T (THead 
(Flat Appl) v t3) t2) \to ((tau0 g c0 t0 t3) \to (ty3 g c0 (TLRef n) t2))) 
H9))) c1 (sym_eq C c1 c0 H5) H6 H7 H4)))) | (tau0_cast c1 v1 v2 H4 t0 t3 H5) 
\Rightarrow (\lambda (H6: (eq C c1 c0)).(\lambda (H7: (eq T (THead (Flat 
Cast) v1 t0) (TLRef n))).(\lambda (H8: (eq T (THead (Flat Cast) v2 t3) 
t2)).(eq_ind C c0 (\lambda (c2: C).((eq T (THead (Flat Cast) v1 t0) (TLRef 
n)) \to ((eq T (THead (Flat Cast) v2 t3) t2) \to ((tau0 g c2 v1 v2) \to 
((tau0 g c2 t0 t3) \to (ty3 g c0 (TLRef n) t2)))))) (\lambda (H9: (eq T 
(THead (Flat Cast) v1 t0) (TLRef n))).(let H10 \def (eq_ind T (THead (Flat 
Cast) v1 t0) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) I (TLRef n) H9) in (False_ind ((eq T (THead (Flat Cast) 
v2 t3) t2) \to ((tau0 g c0 v1 v2) \to ((tau0 g c0 t0 t3) \to (ty3 g c0 (TLRef 
n) t2)))) H10))) c1 (sym_eq C c1 c0 H6) H7 H8 H4 H5))))]) in (H4 (refl_equal 
C c0) (refl_equal T (TLRef n)) (refl_equal T t2))))))))))))) (\lambda (n: 
nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u0: T).(\lambda (H0: (getl n 
c0 (CHead d (Bind Abst) u0))).(\lambda (t: T).(\lambda (H1: (ty3 g d u0 
t)).(\lambda (_: ((\forall (t2: T).((tau0 g d u0 t2) \to (ty3 g d u0 
t2))))).(\lambda (t2: T).(\lambda (H3: (tau0 g c0 (TLRef n) t2)).(let H4 \def 
(match H3 in tau0 return (\lambda (c1: C).(\lambda (t0: T).(\lambda (t3: 
T).(\lambda (_: (tau0 ? c1 t0 t3)).((eq C c1 c0) \to ((eq T t0 (TLRef n)) \to 
((eq T t3 t2) \to (ty3 g c0 (TLRef n) t2)))))))) with [(tau0_sort c1 n0) 
\Rightarrow (\lambda (H4: (eq C c1 c0)).(\lambda (H5: (eq T (TSort n0) (TLRef 
n))).(\lambda (H6: (eq T (TSort (next g n0)) t2)).(eq_ind C c0 (\lambda (_: 
C).((eq T (TSort n0) (TLRef n)) \to ((eq T (TSort (next g n0)) t2) \to (ty3 g 
c0 (TLRef n) t2)))) (\lambda (H7: (eq T (TSort n0) (TLRef n))).(let H8 \def 
(eq_ind T (TSort n0) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow False])) I (TLRef n) H7) in (False_ind ((eq T 
(TSort (next g n0)) t2) \to (ty3 g c0 (TLRef n) t2)) H8))) c1 (sym_eq C c1 c0 
H4) H5 H6)))) | (tau0_abbr c1 d0 v i H4 w H5) \Rightarrow (\lambda (H6: (eq C 
c1 c0)).(\lambda (H7: (eq T (TLRef i) (TLRef n))).(\lambda (H8: (eq T (lift 
(S i) O w) t2)).(eq_ind C c0 (\lambda (c2: C).((eq T (TLRef i) (TLRef n)) \to 
((eq T (lift (S i) O w) t2) \to ((getl i c2 (CHead d0 (Bind Abbr) v)) \to 
((tau0 g d0 v w) \to (ty3 g c0 (TLRef n) t2)))))) (\lambda (H9: (eq T (TLRef 
i) (TLRef n))).(let H10 \def (f_equal T nat (\lambda (e: T).(match e in T 
return (\lambda (_: T).nat) with [(TSort _) \Rightarrow i | (TLRef n0) 
\Rightarrow n0 | (THead _ _ _) \Rightarrow i])) (TLRef i) (TLRef n) H9) in 
(eq_ind nat n (\lambda (n0: nat).((eq T (lift (S n0) O w) t2) \to ((getl n0 
c0 (CHead d0 (Bind Abbr) v)) \to ((tau0 g d0 v w) \to (ty3 g c0 (TLRef n) 
t2))))) (\lambda (H11: (eq T (lift (S n) O w) t2)).(eq_ind T (lift (S n) O w) 
(\lambda (t0: T).((getl n c0 (CHead d0 (Bind Abbr) v)) \to ((tau0 g d0 v w) 
\to (ty3 g c0 (TLRef n) t0)))) (\lambda (H12: (getl n c0 (CHead d0 (Bind 
Abbr) v))).(\lambda (_: (tau0 g d0 v w)).(let H14 \def (eq_ind C (CHead d 
(Bind Abst) u0) (\lambda (c2: C).(getl n c0 c2)) H0 (CHead d0 (Bind Abbr) v) 
(getl_mono c0 (CHead d (Bind Abst) u0) n H0 (CHead d0 (Bind Abbr) v) H12)) in 
(let H15 \def (eq_ind C (CHead d (Bind Abst) u0) (\lambda (ee: C).(match ee 
in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead 
_ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind b) 
\Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow 
False | Abst \Rightarrow True | Void \Rightarrow False]) | (Flat _) 
\Rightarrow False])])) I (CHead d0 (Bind Abbr) v) (getl_mono c0 (CHead d 
(Bind Abst) u0) n H0 (CHead d0 (Bind Abbr) v) H12)) in (False_ind (ty3 g c0 
(TLRef n) (lift (S n) O w)) H15))))) t2 H11)) i (sym_eq nat i n H10)))) c1 
(sym_eq C c1 c0 H6) H7 H8 H4 H5)))) | (tau0_abst c1 d0 v i H4 w H5) 
\Rightarrow (\lambda (H6: (eq C c1 c0)).(\lambda (H7: (eq T (TLRef i) (TLRef 
n))).(\lambda (H8: (eq T (lift (S i) O v) t2)).(eq_ind C c0 (\lambda (c2: 
C).((eq T (TLRef i) (TLRef n)) \to ((eq T (lift (S i) O v) t2) \to ((getl i 
c2 (CHead d0 (Bind Abst) v)) \to ((tau0 g d0 v w) \to (ty3 g c0 (TLRef n) 
t2)))))) (\lambda (H9: (eq T (TLRef i) (TLRef n))).(let H10 \def (f_equal T 
nat (\lambda (e: T).(match e in T return (\lambda (_: T).nat) with [(TSort _) 
\Rightarrow i | (TLRef n0) \Rightarrow n0 | (THead _ _ _) \Rightarrow i])) 
(TLRef i) (TLRef n) H9) in (eq_ind nat n (\lambda (n0: nat).((eq T (lift (S 
n0) O v) t2) \to ((getl n0 c0 (CHead d0 (Bind Abst) v)) \to ((tau0 g d0 v w) 
\to (ty3 g c0 (TLRef n) t2))))) (\lambda (H11: (eq T (lift (S n) O v) 
t2)).(eq_ind T (lift (S n) O v) (\lambda (t0: T).((getl n c0 (CHead d0 (Bind 
Abst) v)) \to ((tau0 g d0 v w) \to (ty3 g c0 (TLRef n) t0)))) (\lambda (H12: 
(getl n c0 (CHead d0 (Bind Abst) v))).(\lambda (H13: (tau0 g d0 v w)).(let 
H14 \def (eq_ind C (CHead d (Bind Abst) u0) (\lambda (c2: C).(getl n c0 c2)) 
H0 (CHead d0 (Bind Abst) v) (getl_mono c0 (CHead d (Bind Abst) u0) n H0 
(CHead d0 (Bind Abst) v) H12)) in (let H15 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | 
(CHead c2 _ _) \Rightarrow c2])) (CHead d (Bind Abst) u0) (CHead d0 (Bind 
Abst) v) (getl_mono c0 (CHead d (Bind Abst) u0) n H0 (CHead d0 (Bind Abst) v) 
H12)) in ((let H16 \def (f_equal C T (\lambda (e: C).(match e in C return 
(\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | (CHead _ _ t0) 
\Rightarrow t0])) (CHead d (Bind Abst) u0) (CHead d0 (Bind Abst) v) 
(getl_mono c0 (CHead d (Bind Abst) u0) n H0 (CHead d0 (Bind Abst) v) H12)) in 
(\lambda (H17: (eq C d d0)).(let H18 \def (eq_ind_r T v (\lambda (t0: 
T).(getl n c0 (CHead d0 (Bind Abst) t0))) H14 u0 H16) in (let H19 \def 
(eq_ind_r T v (\lambda (t0: T).(tau0 g d0 t0 w)) H13 u0 H16) in (eq_ind T u0 
(\lambda (t0: T).(ty3 g c0 (TLRef n) (lift (S n) O t0))) (let H20 \def 
(eq_ind_r C d0 (\lambda (c2: C).(getl n c0 (CHead c2 (Bind Abst) u0))) H18 d 
H17) in (let H21 \def (eq_ind_r C d0 (\lambda (c2: C).(tau0 g c2 u0 w)) H19 d 
H17) in (ty3_abst g n c0 d u0 H20 t H1))) v H16))))) H15))))) t2 H11)) i 
(sym_eq nat i n H10)))) c1 (sym_eq C c1 c0 H6) H7 H8 H4 H5)))) | (tau0_bind b 
c1 v t0 t3 H4) \Rightarrow (\lambda (H5: (eq C c1 c0)).(\lambda (H6: (eq T 
(THead (Bind b) v t0) (TLRef n))).(\lambda (H7: (eq T (THead (Bind b) v t3) 
t2)).(eq_ind C c0 (\lambda (c2: C).((eq T (THead (Bind b) v t0) (TLRef n)) 
\to ((eq T (THead (Bind b) v t3) t2) \to ((tau0 g (CHead c2 (Bind b) v) t0 
t3) \to (ty3 g c0 (TLRef n) t2))))) (\lambda (H8: (eq T (THead (Bind b) v t0) 
(TLRef n))).(let H9 \def (eq_ind T (THead (Bind b) v t0) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I 
(TLRef n) H8) in (False_ind ((eq T (THead (Bind b) v t3) t2) \to ((tau0 g 
(CHead c0 (Bind b) v) t0 t3) \to (ty3 g c0 (TLRef n) t2))) H9))) c1 (sym_eq C 
c1 c0 H5) H6 H7 H4)))) | (tau0_appl c1 v t0 t3 H4) \Rightarrow (\lambda (H5: 
(eq C c1 c0)).(\lambda (H6: (eq T (THead (Flat Appl) v t0) (TLRef 
n))).(\lambda (H7: (eq T (THead (Flat Appl) v t3) t2)).(eq_ind C c0 (\lambda 
(c2: C).((eq T (THead (Flat Appl) v t0) (TLRef n)) \to ((eq T (THead (Flat 
Appl) v t3) t2) \to ((tau0 g c2 t0 t3) \to (ty3 g c0 (TLRef n) t2))))) 
(\lambda (H8: (eq T (THead (Flat Appl) v t0) (TLRef n))).(let H9 \def (eq_ind 
T (THead (Flat Appl) v t0) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow True])) I (TLRef n) H8) in (False_ind ((eq T (THead 
(Flat Appl) v t3) t2) \to ((tau0 g c0 t0 t3) \to (ty3 g c0 (TLRef n) t2))) 
H9))) c1 (sym_eq C c1 c0 H5) H6 H7 H4)))) | (tau0_cast c1 v1 v2 H4 t0 t3 H5) 
\Rightarrow (\lambda (H6: (eq C c1 c0)).(\lambda (H7: (eq T (THead (Flat 
Cast) v1 t0) (TLRef n))).(\lambda (H8: (eq T (THead (Flat Cast) v2 t3) 
t2)).(eq_ind C c0 (\lambda (c2: C).((eq T (THead (Flat Cast) v1 t0) (TLRef 
n)) \to ((eq T (THead (Flat Cast) v2 t3) t2) \to ((tau0 g c2 v1 v2) \to 
((tau0 g c2 t0 t3) \to (ty3 g c0 (TLRef n) t2)))))) (\lambda (H9: (eq T 
(THead (Flat Cast) v1 t0) (TLRef n))).(let H10 \def (eq_ind T (THead (Flat 
Cast) v1 t0) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ _) 
\Rightarrow True])) I (TLRef n) H9) in (False_ind ((eq T (THead (Flat Cast) 
v2 t3) t2) \to ((tau0 g c0 v1 v2) \to ((tau0 g c0 t0 t3) \to (ty3 g c0 (TLRef 
n) t2)))) H10))) c1 (sym_eq C c1 c0 H6) H7 H8 H4 H5))))]) in (H4 (refl_equal 
C c0) (refl_equal T (TLRef n)) (refl_equal T t2))))))))))))) (\lambda (c0: 
C).(\lambda (u0: T).(\lambda (t: T).(\lambda (H0: (ty3 g c0 u0 t)).(\lambda 
(_: ((\forall (t2: T).((tau0 g c0 u0 t2) \to (ty3 g c0 u0 t2))))).(\lambda 
(b: B).(\lambda (t2: T).(\lambda (t3: T).(\lambda (_: (ty3 g (CHead c0 (Bind 
b) u0) t2 t3)).(\lambda (H3: ((\forall (t4: T).((tau0 g (CHead c0 (Bind b) 
u0) t2 t4) \to (ty3 g (CHead c0 (Bind b) u0) t2 t4))))).(\lambda (t0: 
T).(\lambda (_: (ty3 g (CHead c0 (Bind b) u0) t3 t0)).(\lambda (_: ((\forall 
(t4: T).((tau0 g (CHead c0 (Bind b) u0) t3 t4) \to (ty3 g (CHead c0 (Bind b) 
u0) t3 t4))))).(\lambda (t4: T).(\lambda (H6: (tau0 g c0 (THead (Bind b) u0 
t2) t4)).(let H7 \def (match H6 in tau0 return (\lambda (c1: C).(\lambda (t5: 
T).(\lambda (t6: T).(\lambda (_: (tau0 ? c1 t5 t6)).((eq C c1 c0) \to ((eq T 
t5 (THead (Bind b) u0 t2)) \to ((eq T t6 t4) \to (ty3 g c0 (THead (Bind b) u0 
t2) t4)))))))) with [(tau0_sort c1 n) \Rightarrow (\lambda (H7: (eq C c1 
c0)).(\lambda (H8: (eq T (TSort n) (THead (Bind b) u0 t2))).(\lambda (H9: (eq 
T (TSort (next g n)) t4)).(eq_ind C c0 (\lambda (_: C).((eq T (TSort n) 
(THead (Bind b) u0 t2)) \to ((eq T (TSort (next g n)) t4) \to (ty3 g c0 
(THead (Bind b) u0 t2) t4)))) (\lambda (H10: (eq T (TSort n) (THead (Bind b) 
u0 t2))).(let H11 \def (eq_ind T (TSort n) (\lambda (e: T).(match e in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow True | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow False])) I (THead (Bind b) u0 
t2) H10) in (False_ind ((eq T (TSort (next g n)) t4) \to (ty3 g c0 (THead 
(Bind b) u0 t2) t4)) H11))) c1 (sym_eq C c1 c0 H7) H8 H9)))) | (tau0_abbr c1 
d v i H7 w H8) \Rightarrow (\lambda (H9: (eq C c1 c0)).(\lambda (H10: (eq T 
(TLRef i) (THead (Bind b) u0 t2))).(\lambda (H11: (eq T (lift (S i) O w) 
t4)).(eq_ind C c0 (\lambda (c2: C).((eq T (TLRef i) (THead (Bind b) u0 t2)) 
\to ((eq T (lift (S i) O w) t4) \to ((getl i c2 (CHead d (Bind Abbr) v)) \to 
((tau0 g d v w) \to (ty3 g c0 (THead (Bind b) u0 t2) t4)))))) (\lambda (H12: 
(eq T (TLRef i) (THead (Bind b) u0 t2))).(let H13 \def (eq_ind T (TLRef i) 
(\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow 
False])) I (THead (Bind b) u0 t2) H12) in (False_ind ((eq T (lift (S i) O w) 
t4) \to ((getl i c0 (CHead d (Bind Abbr) v)) \to ((tau0 g d v w) \to (ty3 g 
c0 (THead (Bind b) u0 t2) t4)))) H13))) c1 (sym_eq C c1 c0 H9) H10 H11 H7 
H8)))) | (tau0_abst c1 d v i H7 w H8) \Rightarrow (\lambda (H9: (eq C c1 
c0)).(\lambda (H10: (eq T (TLRef i) (THead (Bind b) u0 t2))).(\lambda (H11: 
(eq T (lift (S i) O v) t4)).(eq_ind C c0 (\lambda (c2: C).((eq T (TLRef i) 
(THead (Bind b) u0 t2)) \to ((eq T (lift (S i) O v) t4) \to ((getl i c2 
(CHead d (Bind Abst) v)) \to ((tau0 g d v w) \to (ty3 g c0 (THead (Bind b) u0 
t2) t4)))))) (\lambda (H12: (eq T (TLRef i) (THead (Bind b) u0 t2))).(let H13 
\def (eq_ind T (TLRef i) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | 
(THead _ _ _) \Rightarrow False])) I (THead (Bind b) u0 t2) H12) in 
(False_ind ((eq T (lift (S i) O v) t4) \to ((getl i c0 (CHead d (Bind Abst) 
v)) \to ((tau0 g d v w) \to (ty3 g c0 (THead (Bind b) u0 t2) t4)))) H13))) c1 
(sym_eq C c1 c0 H9) H10 H11 H7 H8)))) | (tau0_bind b0 c1 v t5 t6 H7) 
\Rightarrow (\lambda (H8: (eq C c1 c0)).(\lambda (H9: (eq T (THead (Bind b0) 
v t5) (THead (Bind b) u0 t2))).(\lambda (H10: (eq T (THead (Bind b0) v t6) 
t4)).(eq_ind C c0 (\lambda (c2: C).((eq T (THead (Bind b0) v t5) (THead (Bind 
b) u0 t2)) \to ((eq T (THead (Bind b0) v t6) t4) \to ((tau0 g (CHead c2 (Bind 
b0) v) t5 t6) \to (ty3 g c0 (THead (Bind b) u0 t2) t4))))) (\lambda (H11: (eq 
T (THead (Bind b0) v t5) (THead (Bind b) u0 t2))).(let H12 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t5 | (TLRef _) \Rightarrow t5 | (THead _ _ t7) \Rightarrow t7])) 
(THead (Bind b0) v t5) (THead (Bind b) u0 t2) H11) in ((let H13 \def (f_equal 
T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow v | (TLRef _) \Rightarrow v | (THead _ t7 _) \Rightarrow t7])) 
(THead (Bind b0) v t5) (THead (Bind b) u0 t2) H11) in ((let H14 \def (f_equal 
T B (\lambda (e: T).(match e in T return (\lambda (_: T).B) with [(TSort _) 
\Rightarrow b0 | (TLRef _) \Rightarrow b0 | (THead k _ _) \Rightarrow (match 
k in K return (\lambda (_: K).B) with [(Bind b1) \Rightarrow b1 | (Flat _) 
\Rightarrow b0])])) (THead (Bind b0) v t5) (THead (Bind b) u0 t2) H11) in 
(eq_ind B b (\lambda (b1: B).((eq T v u0) \to ((eq T t5 t2) \to ((eq T (THead 
(Bind b1) v t6) t4) \to ((tau0 g (CHead c0 (Bind b1) v) t5 t6) \to (ty3 g c0 
(THead (Bind b) u0 t2) t4)))))) (\lambda (H15: (eq T v u0)).(eq_ind T u0 
(\lambda (t7: T).((eq T t5 t2) \to ((eq T (THead (Bind b) t7 t6) t4) \to 
((tau0 g (CHead c0 (Bind b) t7) t5 t6) \to (ty3 g c0 (THead (Bind b) u0 t2) 
t4))))) (\lambda (H16: (eq T t5 t2)).(eq_ind T t2 (\lambda (t7: T).((eq T 
(THead (Bind b) u0 t6) t4) \to ((tau0 g (CHead c0 (Bind b) u0) t7 t6) \to 
(ty3 g c0 (THead (Bind b) u0 t2) t4)))) (\lambda (H17: (eq T (THead (Bind b) 
u0 t6) t4)).(eq_ind T (THead (Bind b) u0 t6) (\lambda (t7: T).((tau0 g (CHead 
c0 (Bind b) u0) t2 t6) \to (ty3 g c0 (THead (Bind b) u0 t2) t7))) (\lambda 
(H18: (tau0 g (CHead c0 (Bind b) u0) t2 t6)).(let H_y \def (H3 t6 H18) in 
(ex_ind T (\lambda (t7: T).(ty3 g (CHead c0 (Bind b) u0) t6 t7)) (ty3 g c0 
(THead (Bind b) u0 t2) (THead (Bind b) u0 t6)) (\lambda (x: T).(\lambda (H19: 
(ty3 g (CHead c0 (Bind b) u0) t6 x)).(ty3_bind g c0 u0 t H0 b t2 t6 H_y x 
H19))) (ty3_correct g (CHead c0 (Bind b) u0) t2 t6 H_y)))) t4 H17)) t5 
(sym_eq T t5 t2 H16))) v (sym_eq T v u0 H15))) b0 (sym_eq B b0 b H14))) H13)) 
H12))) c1 (sym_eq C c1 c0 H8) H9 H10 H7)))) | (tau0_appl c1 v t5 t6 H7) 
\Rightarrow (\lambda (H8: (eq C c1 c0)).(\lambda (H9: (eq T (THead (Flat 
Appl) v t5) (THead (Bind b) u0 t2))).(\lambda (H10: (eq T (THead (Flat Appl) 
v t6) t4)).(eq_ind C c0 (\lambda (c2: C).((eq T (THead (Flat Appl) v t5) 
(THead (Bind b) u0 t2)) \to ((eq T (THead (Flat Appl) v t6) t4) \to ((tau0 g 
c2 t5 t6) \to (ty3 g c0 (THead (Bind b) u0 t2) t4))))) (\lambda (H11: (eq T 
(THead (Flat Appl) v t5) (THead (Bind b) u0 t2))).(let H12 \def (eq_ind T 
(THead (Flat Appl) v t5) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind 
b) u0 t2) H11) in (False_ind ((eq T (THead (Flat Appl) v t6) t4) \to ((tau0 g 
c0 t5 t6) \to (ty3 g c0 (THead (Bind b) u0 t2) t4))) H12))) c1 (sym_eq C c1 
c0 H8) H9 H10 H7)))) | (tau0_cast c1 v1 v2 H7 t5 t6 H8) \Rightarrow (\lambda 
(H9: (eq C c1 c0)).(\lambda (H10: (eq T (THead (Flat Cast) v1 t5) (THead 
(Bind b) u0 t2))).(\lambda (H11: (eq T (THead (Flat Cast) v2 t6) t4)).(eq_ind 
C c0 (\lambda (c2: C).((eq T (THead (Flat Cast) v1 t5) (THead (Bind b) u0 
t2)) \to ((eq T (THead (Flat Cast) v2 t6) t4) \to ((tau0 g c2 v1 v2) \to 
((tau0 g c2 t5 t6) \to (ty3 g c0 (THead (Bind b) u0 t2) t4)))))) (\lambda 
(H12: (eq T (THead (Flat Cast) v1 t5) (THead (Bind b) u0 t2))).(let H13 \def 
(eq_ind T (THead (Flat Cast) v1 t5) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind b) u0 t2) H12) in (False_ind ((eq T (THead (Flat 
Cast) v2 t6) t4) \to ((tau0 g c0 v1 v2) \to ((tau0 g c0 t5 t6) \to (ty3 g c0 
(THead (Bind b) u0 t2) t4)))) H13))) c1 (sym_eq C c1 c0 H9) H10 H11 H7 
H8))))]) in (H7 (refl_equal C c0) (refl_equal T (THead (Bind b) u0 t2)) 
(refl_equal T t4)))))))))))))))))) (\lambda (c0: C).(\lambda (w: T).(\lambda 
(u0: T).(\lambda (H0: (ty3 g c0 w u0)).(\lambda (_: ((\forall (t2: T).((tau0 
g c0 w t2) \to (ty3 g c0 w t2))))).(\lambda (v: T).(\lambda (t: T).(\lambda 
(H2: (ty3 g c0 v (THead (Bind Abst) u0 t))).(\lambda (H3: ((\forall (t2: 
T).((tau0 g c0 v t2) \to (ty3 g c0 v t2))))).(\lambda (t2: T).(\lambda (H4: 
(tau0 g c0 (THead (Flat Appl) w v) t2)).(let H5 \def (match H4 in tau0 return 
(\lambda (c1: C).(\lambda (t0: T).(\lambda (t3: T).(\lambda (_: (tau0 ? c1 t0 
t3)).((eq C c1 c0) \to ((eq T t0 (THead (Flat Appl) w v)) \to ((eq T t3 t2) 
\to (ty3 g c0 (THead (Flat Appl) w v) t2)))))))) with [(tau0_sort c1 n) 
\Rightarrow (\lambda (H5: (eq C c1 c0)).(\lambda (H6: (eq T (TSort n) (THead 
(Flat Appl) w v))).(\lambda (H7: (eq T (TSort (next g n)) t2)).(eq_ind C c0 
(\lambda (_: C).((eq T (TSort n) (THead (Flat Appl) w v)) \to ((eq T (TSort 
(next g n)) t2) \to (ty3 g c0 (THead (Flat Appl) w v) t2)))) (\lambda (H8: 
(eq T (TSort n) (THead (Flat Appl) w v))).(let H9 \def (eq_ind T (TSort n) 
(\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
False])) I (THead (Flat Appl) w v) H8) in (False_ind ((eq T (TSort (next g 
n)) t2) \to (ty3 g c0 (THead (Flat Appl) w v) t2)) H9))) c1 (sym_eq C c1 c0 
H5) H6 H7)))) | (tau0_abbr c1 d v0 i H5 w0 H6) \Rightarrow (\lambda (H7: (eq 
C c1 c0)).(\lambda (H8: (eq T (TLRef i) (THead (Flat Appl) w v))).(\lambda 
(H9: (eq T (lift (S i) O w0) t2)).(eq_ind C c0 (\lambda (c2: C).((eq T (TLRef 
i) (THead (Flat Appl) w v)) \to ((eq T (lift (S i) O w0) t2) \to ((getl i c2 
(CHead d (Bind Abbr) v0)) \to ((tau0 g d v0 w0) \to (ty3 g c0 (THead (Flat 
Appl) w v) t2)))))) (\lambda (H10: (eq T (TLRef i) (THead (Flat Appl) w 
v))).(let H11 \def (eq_ind T (TLRef i) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead (Flat Appl) w 
v) H10) in (False_ind ((eq T (lift (S i) O w0) t2) \to ((getl i c0 (CHead d 
(Bind Abbr) v0)) \to ((tau0 g d v0 w0) \to (ty3 g c0 (THead (Flat Appl) w v) 
t2)))) H11))) c1 (sym_eq C c1 c0 H7) H8 H9 H5 H6)))) | (tau0_abst c1 d v0 i 
H5 w0 H6) \Rightarrow (\lambda (H7: (eq C c1 c0)).(\lambda (H8: (eq T (TLRef 
i) (THead (Flat Appl) w v))).(\lambda (H9: (eq T (lift (S i) O v0) 
t2)).(eq_ind C c0 (\lambda (c2: C).((eq T (TLRef i) (THead (Flat Appl) w v)) 
\to ((eq T (lift (S i) O v0) t2) \to ((getl i c2 (CHead d (Bind Abst) v0)) 
\to ((tau0 g d v0 w0) \to (ty3 g c0 (THead (Flat Appl) w v) t2)))))) (\lambda 
(H10: (eq T (TLRef i) (THead (Flat Appl) w v))).(let H11 \def (eq_ind T 
(TLRef i) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) 
\Rightarrow False])) I (THead (Flat Appl) w v) H10) in (False_ind ((eq T 
(lift (S i) O v0) t2) \to ((getl i c0 (CHead d (Bind Abst) v0)) \to ((tau0 g 
d v0 w0) \to (ty3 g c0 (THead (Flat Appl) w v) t2)))) H11))) c1 (sym_eq C c1 
c0 H7) H8 H9 H5 H6)))) | (tau0_bind b c1 v0 t0 t3 H5) \Rightarrow (\lambda 
(H6: (eq C c1 c0)).(\lambda (H7: (eq T (THead (Bind b) v0 t0) (THead (Flat 
Appl) w v))).(\lambda (H8: (eq T (THead (Bind b) v0 t3) t2)).(eq_ind C c0 
(\lambda (c2: C).((eq T (THead (Bind b) v0 t0) (THead (Flat Appl) w v)) \to 
((eq T (THead (Bind b) v0 t3) t2) \to ((tau0 g (CHead c2 (Bind b) v0) t0 t3) 
\to (ty3 g c0 (THead (Flat Appl) w v) t2))))) (\lambda (H9: (eq T (THead 
(Bind b) v0 t0) (THead (Flat Appl) w v))).(let H10 \def (eq_ind T (THead 
(Bind b) v0 t0) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ 
_) \Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat Appl) w v) 
H9) in (False_ind ((eq T (THead (Bind b) v0 t3) t2) \to ((tau0 g (CHead c0 
(Bind b) v0) t0 t3) \to (ty3 g c0 (THead (Flat Appl) w v) t2))) H10))) c1 
(sym_eq C c1 c0 H6) H7 H8 H5)))) | (tau0_appl c1 v0 t0 t3 H5) \Rightarrow 
(\lambda (H6: (eq C c1 c0)).(\lambda (H7: (eq T (THead (Flat Appl) v0 t0) 
(THead (Flat Appl) w v))).(\lambda (H8: (eq T (THead (Flat Appl) v0 t3) 
t2)).(eq_ind C c0 (\lambda (c2: C).((eq T (THead (Flat Appl) v0 t0) (THead 
(Flat Appl) w v)) \to ((eq T (THead (Flat Appl) v0 t3) t2) \to ((tau0 g c2 t0 
t3) \to (ty3 g c0 (THead (Flat Appl) w v) t2))))) (\lambda (H9: (eq T (THead 
(Flat Appl) v0 t0) (THead (Flat Appl) w v))).(let H10 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t4) \Rightarrow t4])) 
(THead (Flat Appl) v0 t0) (THead (Flat Appl) w v) H9) in ((let H11 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow v0 | (TLRef _) \Rightarrow v0 | (THead _ t4 _) 
\Rightarrow t4])) (THead (Flat Appl) v0 t0) (THead (Flat Appl) w v) H9) in 
(eq_ind T w (\lambda (t4: T).((eq T t0 v) \to ((eq T (THead (Flat Appl) t4 
t3) t2) \to ((tau0 g c0 t0 t3) \to (ty3 g c0 (THead (Flat Appl) w v) t2))))) 
(\lambda (H12: (eq T t0 v)).(eq_ind T v (\lambda (t4: T).((eq T (THead (Flat 
Appl) w t3) t2) \to ((tau0 g c0 t4 t3) \to (ty3 g c0 (THead (Flat Appl) w v) 
t2)))) (\lambda (H13: (eq T (THead (Flat Appl) w t3) t2)).(eq_ind T (THead 
(Flat Appl) w t3) (\lambda (t4: T).((tau0 g c0 v t3) \to (ty3 g c0 (THead 
(Flat Appl) w v) t4))) (\lambda (H14: (tau0 g c0 v t3)).(let H_y \def (H3 t3 
H14) in (let H15 \def (ty3_unique g c0 v t3 H_y (THead (Bind Abst) u0 t) H2) 
in (ex_ind T (\lambda (t4: T).(ty3 g c0 t3 t4)) (ty3 g c0 (THead (Flat Appl) 
w v) (THead (Flat Appl) w t3)) (\lambda (x: T).(\lambda (H16: (ty3 g c0 t3 
x)).(ex_ind T (\lambda (t4: T).(ty3 g c0 u0 t4)) (ty3 g c0 (THead (Flat Appl) 
w v) (THead (Flat Appl) w t3)) (\lambda (x0: T).(\lambda (_: (ty3 g c0 u0 
x0)).(ex_ind T (\lambda (t4: T).(ty3 g c0 (THead (Bind Abst) u0 t) t4)) (ty3 
g c0 (THead (Flat Appl) w v) (THead (Flat Appl) w t3)) (\lambda (x1: 
T).(\lambda (H18: (ty3 g c0 (THead (Bind Abst) u0 t) x1)).(ex4_3_ind T T T 
(\lambda (t4: T).(\lambda (_: T).(\lambda (_: T).(pc3 c0 (THead (Bind Abst) 
u0 t4) x1)))) (\lambda (_: T).(\lambda (t5: T).(\lambda (_: T).(ty3 g c0 u0 
t5)))) (\lambda (t4: T).(\lambda (_: T).(\lambda (_: T).(ty3 g (CHead c0 
(Bind Abst) u0) t t4)))) (\lambda (t4: T).(\lambda (_: T).(\lambda (t6: 
T).(ty3 g (CHead c0 (Bind Abst) u0) t4 t6)))) (ty3 g c0 (THead (Flat Appl) w 
v) (THead (Flat Appl) w t3)) (\lambda (x2: T).(\lambda (x3: T).(\lambda (x4: 
T).(\lambda (_: (pc3 c0 (THead (Bind Abst) u0 x2) x1)).(\lambda (H20: (ty3 g 
c0 u0 x3)).(\lambda (H21: (ty3 g (CHead c0 (Bind Abst) u0) t x2)).(\lambda 
(H22: (ty3 g (CHead c0 (Bind Abst) u0) x2 x4)).(ty3_conv g c0 (THead (Flat 
Appl) w t3) (THead (Flat Appl) w (THead (Bind Abst) u0 x2)) (ty3_appl g c0 w 
u0 H0 t3 x2 (ty3_sconv g c0 t3 x H16 (THead (Bind Abst) u0 t) (THead (Bind 
Abst) u0 x2) (ty3_bind g c0 u0 x3 H20 Abst t x2 H21 x4 H22) H15)) (THead 
(Flat Appl) w v) (THead (Flat Appl) w (THead (Bind Abst) u0 t)) (ty3_appl g 
c0 w u0 H0 v t H2) (pc3_s c0 (THead (Flat Appl) w (THead (Bind Abst) u0 t)) 
(THead (Flat Appl) w t3) (pc3_thin_dx c0 t3 (THead (Bind Abst) u0 t) H15 w 
Appl)))))))))) (ty3_gen_bind g Abst c0 u0 t x1 H18)))) (ty3_correct g c0 v 
(THead (Bind Abst) u0 t) H2)))) (ty3_correct g c0 w u0 H0)))) (ty3_correct g 
c0 v t3 H_y))))) t2 H13)) t0 (sym_eq T t0 v H12))) v0 (sym_eq T v0 w H11))) 
H10))) c1 (sym_eq C c1 c0 H6) H7 H8 H5)))) | (tau0_cast c1 v1 v2 H5 t0 t3 H6) 
\Rightarrow (\lambda (H7: (eq C c1 c0)).(\lambda (H8: (eq T (THead (Flat 
Cast) v1 t0) (THead (Flat Appl) w v))).(\lambda (H9: (eq T (THead (Flat Cast) 
v2 t3) t2)).(eq_ind C c0 (\lambda (c2: C).((eq T (THead (Flat Cast) v1 t0) 
(THead (Flat Appl) w v)) \to ((eq T (THead (Flat Cast) v2 t3) t2) \to ((tau0 
g c2 v1 v2) \to ((tau0 g c2 t0 t3) \to (ty3 g c0 (THead (Flat Appl) w v) 
t2)))))) (\lambda (H10: (eq T (THead (Flat Cast) v1 t0) (THead (Flat Appl) w 
v))).(let H11 \def (eq_ind T (THead (Flat Cast) v1 t0) (\lambda (e: T).(match 
e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat f) \Rightarrow 
(match f in F return (\lambda (_: F).Prop) with [Appl \Rightarrow False | 
Cast \Rightarrow True])])])) I (THead (Flat Appl) w v) H10) in (False_ind 
((eq T (THead (Flat Cast) v2 t3) t2) \to ((tau0 g c0 v1 v2) \to ((tau0 g c0 
t0 t3) \to (ty3 g c0 (THead (Flat Appl) w v) t2)))) H11))) c1 (sym_eq C c1 c0 
H7) H8 H9 H5 H6))))]) in (H5 (refl_equal C c0) (refl_equal T (THead (Flat 
Appl) w v)) (refl_equal T t2)))))))))))))) (\lambda (c0: C).(\lambda (t2: 
T).(\lambda (t3: T).(\lambda (H0: (ty3 g c0 t2 t3)).(\lambda (H1: ((\forall 
(t4: T).((tau0 g c0 t2 t4) \to (ty3 g c0 t2 t4))))).(\lambda (t0: T).(\lambda 
(_: (ty3 g c0 t3 t0)).(\lambda (H3: ((\forall (t4: T).((tau0 g c0 t3 t4) \to 
(ty3 g c0 t3 t4))))).(\lambda (t4: T).(\lambda (H4: (tau0 g c0 (THead (Flat 
Cast) t3 t2) t4)).(let H5 \def (match H4 in tau0 return (\lambda (c1: 
C).(\lambda (t: T).(\lambda (t5: T).(\lambda (_: (tau0 ? c1 t t5)).((eq C c1 
c0) \to ((eq T t (THead (Flat Cast) t3 t2)) \to ((eq T t5 t4) \to (ty3 g c0 
(THead (Flat Cast) t3 t2) t4)))))))) with [(tau0_sort c1 n) \Rightarrow 
(\lambda (H5: (eq C c1 c0)).(\lambda (H6: (eq T (TSort n) (THead (Flat Cast) 
t3 t2))).(\lambda (H7: (eq T (TSort (next g n)) t4)).(eq_ind C c0 (\lambda 
(_: C).((eq T (TSort n) (THead (Flat Cast) t3 t2)) \to ((eq T (TSort (next g 
n)) t4) \to (ty3 g c0 (THead (Flat Cast) t3 t2) t4)))) (\lambda (H8: (eq T 
(TSort n) (THead (Flat Cast) t3 t2))).(let H9 \def (eq_ind T (TSort n) 
(\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow True | (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow 
False])) I (THead (Flat Cast) t3 t2) H8) in (False_ind ((eq T (TSort (next g 
n)) t4) \to (ty3 g c0 (THead (Flat Cast) t3 t2) t4)) H9))) c1 (sym_eq C c1 c0 
H5) H6 H7)))) | (tau0_abbr c1 d v i H5 w H6) \Rightarrow (\lambda (H7: (eq C 
c1 c0)).(\lambda (H8: (eq T (TLRef i) (THead (Flat Cast) t3 t2))).(\lambda 
(H9: (eq T (lift (S i) O w) t4)).(eq_ind C c0 (\lambda (c2: C).((eq T (TLRef 
i) (THead (Flat Cast) t3 t2)) \to ((eq T (lift (S i) O w) t4) \to ((getl i c2 
(CHead d (Bind Abbr) v)) \to ((tau0 g d v w) \to (ty3 g c0 (THead (Flat Cast) 
t3 t2) t4)))))) (\lambda (H10: (eq T (TLRef i) (THead (Flat Cast) t3 
t2))).(let H11 \def (eq_ind T (TLRef i) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) I (THead (Flat Cast) t3 
t2) H10) in (False_ind ((eq T (lift (S i) O w) t4) \to ((getl i c0 (CHead d 
(Bind Abbr) v)) \to ((tau0 g d v w) \to (ty3 g c0 (THead (Flat Cast) t3 t2) 
t4)))) H11))) c1 (sym_eq C c1 c0 H7) H8 H9 H5 H6)))) | (tau0_abst c1 d v i H5 
w H6) \Rightarrow (\lambda (H7: (eq C c1 c0)).(\lambda (H8: (eq T (TLRef i) 
(THead (Flat Cast) t3 t2))).(\lambda (H9: (eq T (lift (S i) O v) t4)).(eq_ind 
C c0 (\lambda (c2: C).((eq T (TLRef i) (THead (Flat Cast) t3 t2)) \to ((eq T 
(lift (S i) O v) t4) \to ((getl i c2 (CHead d (Bind Abst) v)) \to ((tau0 g d 
v w) \to (ty3 g c0 (THead (Flat Cast) t3 t2) t4)))))) (\lambda (H10: (eq T 
(TLRef i) (THead (Flat Cast) t3 t2))).(let H11 \def (eq_ind T (TLRef i) 
(\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow 
False])) I (THead (Flat Cast) t3 t2) H10) in (False_ind ((eq T (lift (S i) O 
v) t4) \to ((getl i c0 (CHead d (Bind Abst) v)) \to ((tau0 g d v w) \to (ty3 
g c0 (THead (Flat Cast) t3 t2) t4)))) H11))) c1 (sym_eq C c1 c0 H7) H8 H9 H5 
H6)))) | (tau0_bind b c1 v t5 t6 H5) \Rightarrow (\lambda (H6: (eq C c1 
c0)).(\lambda (H7: (eq T (THead (Bind b) v t5) (THead (Flat Cast) t3 
t2))).(\lambda (H8: (eq T (THead (Bind b) v t6) t4)).(eq_ind C c0 (\lambda 
(c2: C).((eq T (THead (Bind b) v t5) (THead (Flat Cast) t3 t2)) \to ((eq T 
(THead (Bind b) v t6) t4) \to ((tau0 g (CHead c2 (Bind b) v) t5 t6) \to (ty3 
g c0 (THead (Flat Cast) t3 t2) t4))))) (\lambda (H9: (eq T (THead (Bind b) v 
t5) (THead (Flat Cast) t3 t2))).(let H10 \def (eq_ind T (THead (Bind b) v t5) 
(\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | 
(Flat _) \Rightarrow False])])) I (THead (Flat Cast) t3 t2) H9) in (False_ind 
((eq T (THead (Bind b) v t6) t4) \to ((tau0 g (CHead c0 (Bind b) v) t5 t6) 
\to (ty3 g c0 (THead (Flat Cast) t3 t2) t4))) H10))) c1 (sym_eq C c1 c0 H6) 
H7 H8 H5)))) | (tau0_appl c1 v t5 t6 H5) \Rightarrow (\lambda (H6: (eq C c1 
c0)).(\lambda (H7: (eq T (THead (Flat Appl) v t5) (THead (Flat Cast) t3 
t2))).(\lambda (H8: (eq T (THead (Flat Appl) v t6) t4)).(eq_ind C c0 (\lambda 
(c2: C).((eq T (THead (Flat Appl) v t5) (THead (Flat Cast) t3 t2)) \to ((eq T 
(THead (Flat Appl) v t6) t4) \to ((tau0 g c2 t5 t6) \to (ty3 g c0 (THead 
(Flat Cast) t3 t2) t4))))) (\lambda (H9: (eq T (THead (Flat Appl) v t5) 
(THead (Flat Cast) t3 t2))).(let H10 \def (eq_ind T (THead (Flat Appl) v t5) 
(\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | 
(Flat f) \Rightarrow (match f in F return (\lambda (_: F).Prop) with [Appl 
\Rightarrow True | Cast \Rightarrow False])])])) I (THead (Flat Cast) t3 t2) 
H9) in (False_ind ((eq T (THead (Flat Appl) v t6) t4) \to ((tau0 g c0 t5 t6) 
\to (ty3 g c0 (THead (Flat Cast) t3 t2) t4))) H10))) c1 (sym_eq C c1 c0 H6) 
H7 H8 H5)))) | (tau0_cast c1 v1 v2 H5 t5 t6 H6) \Rightarrow (\lambda (H7: (eq 
C c1 c0)).(\lambda (H8: (eq T (THead (Flat Cast) v1 t5) (THead (Flat Cast) t3 
t2))).(\lambda (H9: (eq T (THead (Flat Cast) v2 t6) t4)).(eq_ind C c0 
(\lambda (c2: C).((eq T (THead (Flat Cast) v1 t5) (THead (Flat Cast) t3 t2)) 
\to ((eq T (THead (Flat Cast) v2 t6) t4) \to ((tau0 g c2 v1 v2) \to ((tau0 g 
c2 t5 t6) \to (ty3 g c0 (THead (Flat Cast) t3 t2) t4)))))) (\lambda (H10: (eq 
T (THead (Flat Cast) v1 t5) (THead (Flat Cast) t3 t2))).(let H11 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow t5 | (TLRef _) \Rightarrow t5 | (THead _ _ t) 
\Rightarrow t])) (THead (Flat Cast) v1 t5) (THead (Flat Cast) t3 t2) H10) in 
((let H12 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow v1 | (TLRef _) \Rightarrow v1 | (THead _ t 
_) \Rightarrow t])) (THead (Flat Cast) v1 t5) (THead (Flat Cast) t3 t2) H10) 
in (eq_ind T t3 (\lambda (t: T).((eq T t5 t2) \to ((eq T (THead (Flat Cast) 
v2 t6) t4) \to ((tau0 g c0 t v2) \to ((tau0 g c0 t5 t6) \to (ty3 g c0 (THead 
(Flat Cast) t3 t2) t4)))))) (\lambda (H13: (eq T t5 t2)).(eq_ind T t2 
(\lambda (t: T).((eq T (THead (Flat Cast) v2 t6) t4) \to ((tau0 g c0 t3 v2) 
\to ((tau0 g c0 t t6) \to (ty3 g c0 (THead (Flat Cast) t3 t2) t4))))) 
(\lambda (H14: (eq T (THead (Flat Cast) v2 t6) t4)).(eq_ind T (THead (Flat 
Cast) v2 t6) (\lambda (t: T).((tau0 g c0 t3 v2) \to ((tau0 g c0 t2 t6) \to 
(ty3 g c0 (THead (Flat Cast) t3 t2) t)))) (\lambda (H15: (tau0 g c0 t3 
v2)).(\lambda (H16: (tau0 g c0 t2 t6)).(let H_y \def (H1 t6 H16) in (let H_y0 
\def (H3 v2 H15) in (let H17 \def (ty3_unique g c0 t2 t6 H_y t3 H0) in 
(ex_ind T (\lambda (t: T).(ty3 g c0 v2 t)) (ty3 g c0 (THead (Flat Cast) t3 
t2) (THead (Flat Cast) v2 t6)) (\lambda (x: T).(\lambda (H18: (ty3 g c0 v2 
x)).(ex_ind T (\lambda (t: T).(ty3 g c0 t6 t)) (ty3 g c0 (THead (Flat Cast) 
t3 t2) (THead (Flat Cast) v2 t6)) (\lambda (x0: T).(\lambda (H19: (ty3 g c0 
t6 x0)).(ty3_conv g c0 (THead (Flat Cast) v2 t6) (THead (Flat Cast) x v2) 
(ty3_cast g c0 t6 v2 (ty3_sconv g c0 t6 x0 H19 t3 v2 H_y0 H17) x H18) (THead 
(Flat Cast) t3 t2) (THead (Flat Cast) v2 t3) (ty3_cast g c0 t2 t3 H0 v2 H_y0) 
(pc3_s c0 (THead (Flat Cast) v2 t3) (THead (Flat Cast) v2 t6) (pc3_thin_dx c0 
t6 t3 H17 v2 Cast))))) (ty3_correct g c0 t2 t6 H_y)))) (ty3_correct g c0 t3 
v2 H_y0))))))) t4 H14)) t5 (sym_eq T t5 t2 H13))) v1 (sym_eq T v1 t3 H12))) 
H11))) c1 (sym_eq C c1 c0 H7) H8 H9 H5 H6))))]) in (H5 (refl_equal C c0) 
(refl_equal T (THead (Flat Cast) t3 t2)) (refl_equal T t4))))))))))))) c u t1 
H))))).

