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

include "Basic-1/csuba/arity.ma".

include "Basic-1/pr3/defs.ma".

include "Basic-1/pr1/defs.ma".

include "Basic-1/wcpr0/getl.ma".

include "Basic-1/pr0/fwd.ma".

include "Basic-1/arity/subst0.ma".

theorem arity_sred_wcpr0_pr0:
 \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (a: A).((arity g 
c1 t1 a) \to (\forall (c2: C).((wcpr0 c1 c2) \to (\forall (t2: T).((pr0 t1 
t2) \to (arity g c2 t2 a)))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t1: T).(\lambda (a: A).(\lambda 
(H: (arity g c1 t1 a)).(arity_ind g (\lambda (c: C).(\lambda (t: T).(\lambda 
(a0: A).(\forall (c2: C).((wcpr0 c c2) \to (\forall (t2: T).((pr0 t t2) \to 
(arity g c2 t2 a0)))))))) (\lambda (c: C).(\lambda (n: nat).(\lambda (c2: 
C).(\lambda (_: (wcpr0 c c2)).(\lambda (t2: T).(\lambda (H1: (pr0 (TSort n) 
t2)).(eq_ind_r T (TSort n) (\lambda (t: T).(arity g c2 t (ASort O n))) 
(arity_sort g c2 n) t2 (pr0_gen_sort t2 n H1)))))))) (\lambda (c: C).(\lambda 
(d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c (CHead d 
(Bind Abbr) u))).(\lambda (a0: A).(\lambda (_: (arity g d u a0)).(\lambda 
(H2: ((\forall (c2: C).((wcpr0 d c2) \to (\forall (t2: T).((pr0 u t2) \to 
(arity g c2 t2 a0))))))).(\lambda (c2: C).(\lambda (H3: (wcpr0 c 
c2)).(\lambda (t2: T).(\lambda (H4: (pr0 (TLRef i) t2)).(eq_ind_r T (TLRef i) 
(\lambda (t: T).(arity g c2 t a0)) (ex3_2_ind C T (\lambda (e2: C).(\lambda 
(u2: T).(getl i c2 (CHead e2 (Bind Abbr) u2)))) (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 d e2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u u2))) (arity g c2 
(TLRef i) a0) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H5: (getl i c2 
(CHead x0 (Bind Abbr) x1))).(\lambda (H6: (wcpr0 d x0)).(\lambda (H7: (pr0 u 
x1)).(arity_abbr g c2 x0 x1 i H5 a0 (H2 x0 H6 x1 H7))))))) (wcpr0_getl c c2 
H3 i d u (Bind Abbr) H0)) t2 (pr0_gen_lref t2 i H4)))))))))))))) (\lambda (c: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c 
(CHead d (Bind Abst) u))).(\lambda (a0: A).(\lambda (_: (arity g d u (asucc g 
a0))).(\lambda (H2: ((\forall (c2: C).((wcpr0 d c2) \to (\forall (t2: 
T).((pr0 u t2) \to (arity g c2 t2 (asucc g a0)))))))).(\lambda (c2: 
C).(\lambda (H3: (wcpr0 c c2)).(\lambda (t2: T).(\lambda (H4: (pr0 (TLRef i) 
t2)).(eq_ind_r T (TLRef i) (\lambda (t: T).(arity g c2 t a0)) (ex3_2_ind C T 
(\lambda (e2: C).(\lambda (u2: T).(getl i c2 (CHead e2 (Bind Abst) u2)))) 
(\lambda (e2: C).(\lambda (_: T).(wcpr0 d e2))) (\lambda (_: C).(\lambda (u2: 
T).(pr0 u u2))) (arity g c2 (TLRef i) a0) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H5: (getl i c2 (CHead x0 (Bind Abst) x1))).(\lambda (H6: (wcpr0 
d x0)).(\lambda (H7: (pr0 u x1)).(arity_abst g c2 x0 x1 i H5 a0 (H2 x0 H6 x1 
H7))))))) (wcpr0_getl c c2 H3 i d u (Bind Abst) H0)) t2 (pr0_gen_lref t2 i 
H4)))))))))))))) (\lambda (b: B).(\lambda (H0: (not (eq B b Abst))).(\lambda 
(c: C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: (arity g c u 
a1)).(\lambda (H2: ((\forall (c2: C).((wcpr0 c c2) \to (\forall (t2: T).((pr0 
u t2) \to (arity g c2 t2 a1))))))).(\lambda (t: T).(\lambda (a2: A).(\lambda 
(H3: (arity g (CHead c (Bind b) u) t a2)).(\lambda (H4: ((\forall (c2: 
C).((wcpr0 (CHead c (Bind b) u) c2) \to (\forall (t2: T).((pr0 t t2) \to 
(arity g c2 t2 a2))))))).(\lambda (c2: C).(\lambda (H5: (wcpr0 c 
c2)).(\lambda (t2: T).(\lambda (H6: (pr0 (THead (Bind b) u t) t2)).(insert_eq 
T (THead (Bind b) u t) (\lambda (t0: T).(pr0 t0 t2)) (\lambda (_: T).(arity g 
c2 t2 a2)) (\lambda (y: T).(\lambda (H7: (pr0 y t2)).(pr0_ind (\lambda (t0: 
T).(\lambda (t3: T).((eq T t0 (THead (Bind b) u t)) \to (arity g c2 t3 a2)))) 
(\lambda (t0: T).(\lambda (H8: (eq T t0 (THead (Bind b) u t))).(let H9 \def 
(f_equal T T (\lambda (e: T).e) t0 (THead (Bind b) u t) H8) in (eq_ind_r T 
(THead (Bind b) u t) (\lambda (t3: T).(arity g c2 t3 a2)) (arity_bind g b H0 
c2 u a1 (H2 c2 H5 u (pr0_refl u)) t a2 (H4 (CHead c2 (Bind b) u) (wcpr0_comp 
c c2 H5 u u (pr0_refl u) (Bind b)) t (pr0_refl t))) t0 H9)))) (\lambda (u1: 
T).(\lambda (u2: T).(\lambda (H8: (pr0 u1 u2)).(\lambda (H9: (((eq T u1 
(THead (Bind b) u t)) \to (arity g c2 u2 a2)))).(\lambda (t3: T).(\lambda 
(t4: T).(\lambda (H10: (pr0 t3 t4)).(\lambda (H11: (((eq T t3 (THead (Bind b) 
u t)) \to (arity g c2 t4 a2)))).(\lambda (k: K).(\lambda (H12: (eq T (THead k 
u1 t3) (THead (Bind b) u t))).(let H13 \def (f_equal T K (\lambda (e: 
T).(match e in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | 
(TLRef _) \Rightarrow k | (THead k0 _ _) \Rightarrow k0])) (THead k u1 t3) 
(THead (Bind b) u t) H12) in ((let H14 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u1 | 
(TLRef _) \Rightarrow u1 | (THead _ t0 _) \Rightarrow t0])) (THead k u1 t3) 
(THead (Bind b) u t) H12) in ((let H15 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t3 | 
(TLRef _) \Rightarrow t3 | (THead _ _ t0) \Rightarrow t0])) (THead k u1 t3) 
(THead (Bind b) u t) H12) in (\lambda (H16: (eq T u1 u)).(\lambda (H17: (eq K 
k (Bind b))).(eq_ind_r K (Bind b) (\lambda (k0: K).(arity g c2 (THead k0 u2 
t4) a2)) (let H18 \def (eq_ind T t3 (\lambda (t0: T).((eq T t0 (THead (Bind 
b) u t)) \to (arity g c2 t4 a2))) H11 t H15) in (let H19 \def (eq_ind T t3 
(\lambda (t0: T).(pr0 t0 t4)) H10 t H15) in (let H20 \def (eq_ind T u1 
(\lambda (t0: T).((eq T t0 (THead (Bind b) u t)) \to (arity g c2 u2 a2))) H9 
u H16) in (let H21 \def (eq_ind T u1 (\lambda (t0: T).(pr0 t0 u2)) H8 u H16) 
in (arity_bind g b H0 c2 u2 a1 (H2 c2 H5 u2 H21) t4 a2 (H4 (CHead c2 (Bind b) 
u2) (wcpr0_comp c c2 H5 u u2 H21 (Bind b)) t4 H19)))))) k H17)))) H14)) 
H13)))))))))))) (\lambda (u0: T).(\lambda (v1: T).(\lambda (v2: T).(\lambda 
(_: (pr0 v1 v2)).(\lambda (_: (((eq T v1 (THead (Bind b) u t)) \to (arity g 
c2 v2 a2)))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (pr0 t3 
t4)).(\lambda (_: (((eq T t3 (THead (Bind b) u t)) \to (arity g c2 t4 
a2)))).(\lambda (H12: (eq T (THead (Flat Appl) v1 (THead (Bind Abst) u0 t3)) 
(THead (Bind b) u t))).(let H13 \def (eq_ind T (THead (Flat Appl) v1 (THead 
(Bind Abst) u0 t3)) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind 
b) u t) H12) in (False_ind (arity g c2 (THead (Bind Abbr) v2 t4) a2) 
H13)))))))))))) (\lambda (b0: B).(\lambda (_: (not (eq B b0 Abst))).(\lambda 
(v1: T).(\lambda (v2: T).(\lambda (_: (pr0 v1 v2)).(\lambda (_: (((eq T v1 
(THead (Bind b) u t)) \to (arity g c2 v2 a2)))).(\lambda (u1: T).(\lambda 
(u2: T).(\lambda (_: (pr0 u1 u2)).(\lambda (_: (((eq T u1 (THead (Bind b) u 
t)) \to (arity g c2 u2 a2)))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: 
(pr0 t3 t4)).(\lambda (_: (((eq T t3 (THead (Bind b) u t)) \to (arity g c2 t4 
a2)))).(\lambda (H15: (eq T (THead (Flat Appl) v1 (THead (Bind b0) u1 t3)) 
(THead (Bind b) u t))).(let H16 \def (eq_ind T (THead (Flat Appl) v1 (THead 
(Bind b0) u1 t3)) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind 
b) u t) H15) in (False_ind (arity g c2 (THead (Bind b0) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4)) a2) H16))))))))))))))))) (\lambda (u1: T).(\lambda 
(u2: T).(\lambda (H8: (pr0 u1 u2)).(\lambda (H9: (((eq T u1 (THead (Bind b) u 
t)) \to (arity g c2 u2 a2)))).(\lambda (t3: T).(\lambda (t4: T).(\lambda 
(H10: (pr0 t3 t4)).(\lambda (H11: (((eq T t3 (THead (Bind b) u t)) \to (arity 
g c2 t4 a2)))).(\lambda (w: T).(\lambda (H12: (subst0 O u2 t4 w)).(\lambda 
(H13: (eq T (THead (Bind Abbr) u1 t3) (THead (Bind b) u t))).(let H14 \def 
(f_equal T B (\lambda (e: T).(match e in T return (\lambda (_: T).B) with 
[(TSort _) \Rightarrow Abbr | (TLRef _) \Rightarrow Abbr | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) (THead (Bind Abbr) u1 t3) 
(THead (Bind b) u t) H13) in ((let H15 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u1 | 
(TLRef _) \Rightarrow u1 | (THead _ t0 _) \Rightarrow t0])) (THead (Bind 
Abbr) u1 t3) (THead (Bind b) u t) H13) in ((let H16 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead _ _ t0) \Rightarrow t0])) 
(THead (Bind Abbr) u1 t3) (THead (Bind b) u t) H13) in (\lambda (H17: (eq T 
u1 u)).(\lambda (H18: (eq B Abbr b)).(let H19 \def (eq_ind T t3 (\lambda (t0: 
T).((eq T t0 (THead (Bind b) u t)) \to (arity g c2 t4 a2))) H11 t H16) in 
(let H20 \def (eq_ind T t3 (\lambda (t0: T).(pr0 t0 t4)) H10 t H16) in (let 
H21 \def (eq_ind T u1 (\lambda (t0: T).((eq T t0 (THead (Bind b) u t)) \to 
(arity g c2 u2 a2))) H9 u H17) in (let H22 \def (eq_ind T u1 (\lambda (t0: 
T).(pr0 t0 u2)) H8 u H17) in (let H23 \def (eq_ind_r B b (\lambda (b0: 
B).((eq T t (THead (Bind b0) u t)) \to (arity g c2 t4 a2))) H19 Abbr H18) in 
(let H24 \def (eq_ind_r B b (\lambda (b0: B).((eq T u (THead (Bind b0) u t)) 
\to (arity g c2 u2 a2))) H21 Abbr H18) in (let H25 \def (eq_ind_r B b 
(\lambda (b0: B).(\forall (c3: C).((wcpr0 (CHead c (Bind b0) u) c3) \to 
(\forall (t5: T).((pr0 t t5) \to (arity g c3 t5 a2)))))) H4 Abbr H18) in (let 
H26 \def (eq_ind_r B b (\lambda (b0: B).(arity g (CHead c (Bind b0) u) t a2)) 
H3 Abbr H18) in (let H27 \def (eq_ind_r B b (\lambda (b0: B).(not (eq B b0 
Abst))) H0 Abbr H18) in (arity_bind g Abbr H27 c2 u2 a1 (H2 c2 H5 u2 H22) w 
a2 (arity_subst0 g (CHead c2 (Bind Abbr) u2) t4 a2 (H25 (CHead c2 (Bind Abbr) 
u2) (wcpr0_comp c c2 H5 u u2 H22 (Bind Abbr)) t4 H20) c2 u2 O (getl_refl Abbr 
c2 u2) w H12)))))))))))))) H15)) H14))))))))))))) (\lambda (b0: B).(\lambda 
(H8: (not (eq B b0 Abst))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H9: 
(pr0 t3 t4)).(\lambda (H10: (((eq T t3 (THead (Bind b) u t)) \to (arity g c2 
t4 a2)))).(\lambda (u0: T).(\lambda (H11: (eq T (THead (Bind b0) u0 (lift (S 
O) O t3)) (THead (Bind b) u t))).(let H12 \def (f_equal T B (\lambda (e: 
T).(match e in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow b0 | 
(TLRef _) \Rightarrow b0 | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow 
b0])])) (THead (Bind b0) u0 (lift (S O) O t3)) (THead (Bind b) u t) H11) in 
((let H13 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow u0 | (TLRef _) \Rightarrow u0 | (THead _ t0 
_) \Rightarrow t0])) (THead (Bind b0) u0 (lift (S O) O t3)) (THead (Bind b) u 
t) H11) in ((let H14 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map (f: ((nat 
\to nat))) (d: nat) (t0: T) on t0: T \def (match t0 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u1 t5) 
\Rightarrow (THead k (lref_map f d u1) (lref_map f (s k d) t5))]) in 
lref_map) (\lambda (x: nat).(plus x (S O))) O t3) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t0: T) on t0: T \def (match 
t0 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k u1 t5) \Rightarrow (THead k (lref_map f d u1) (lref_map f (s k d) 
t5))]) in lref_map) (\lambda (x: nat).(plus x (S O))) O t3) | (THead _ _ t0) 
\Rightarrow t0])) (THead (Bind b0) u0 (lift (S O) O t3)) (THead (Bind b) u t) 
H11) in (\lambda (_: (eq T u0 u)).(\lambda (H16: (eq B b0 b)).(let H17 \def 
(eq_ind B b0 (\lambda (b1: B).(not (eq B b1 Abst))) H8 b H16) in (let H18 
\def (eq_ind_r T t (\lambda (t0: T).((eq T t3 (THead (Bind b) u t0)) \to 
(arity g c2 t4 a2))) H10 (lift (S O) O t3) H14) in (let H19 \def (eq_ind_r T 
t (\lambda (t0: T).(\forall (c3: C).((wcpr0 (CHead c (Bind b) u) c3) \to 
(\forall (t5: T).((pr0 t0 t5) \to (arity g c3 t5 a2)))))) H4 (lift (S O) O 
t3) H14) in (let H20 \def (eq_ind_r T t (\lambda (t0: T).(arity g (CHead c 
(Bind b) u) t0 a2)) H3 (lift (S O) O t3) H14) in (arity_gen_lift g (CHead c2 
(Bind b) u) t4 a2 (S O) O (H19 (CHead c2 (Bind b) u) (wcpr0_comp c c2 H5 u u 
(pr0_refl u) (Bind b)) (lift (S O) O t4) (pr0_lift t3 t4 H9 (S O) O)) c2 
(drop_drop (Bind b) O c2 c2 (drop_refl c2) u))))))))) H13)) H12)))))))))) 
(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (pr0 t3 t4)).(\lambda (_: 
(((eq T t3 (THead (Bind b) u t)) \to (arity g c2 t4 a2)))).(\lambda (u0: 
T).(\lambda (H10: (eq T (THead (Flat Cast) u0 t3) (THead (Bind b) u t))).(let 
H11 \def (eq_ind T (THead (Flat Cast) u0 t3) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind b) u t) H10) in (False_ind (arity g c2 t4 a2) 
H11)))))))) y t2 H7))) H6)))))))))))))))) (\lambda (c: C).(\lambda (u: 
T).(\lambda (a1: A).(\lambda (_: (arity g c u (asucc g a1))).(\lambda (H1: 
((\forall (c2: C).((wcpr0 c c2) \to (\forall (t2: T).((pr0 u t2) \to (arity g 
c2 t2 (asucc g a1)))))))).(\lambda (t: T).(\lambda (a2: A).(\lambda (H2: 
(arity g (CHead c (Bind Abst) u) t a2)).(\lambda (H3: ((\forall (c2: 
C).((wcpr0 (CHead c (Bind Abst) u) c2) \to (\forall (t2: T).((pr0 t t2) \to 
(arity g c2 t2 a2))))))).(\lambda (c2: C).(\lambda (H4: (wcpr0 c 
c2)).(\lambda (t2: T).(\lambda (H5: (pr0 (THead (Bind Abst) u t) 
t2)).(insert_eq T (THead (Bind Abst) u t) (\lambda (t0: T).(pr0 t0 t2)) 
(\lambda (_: T).(arity g c2 t2 (AHead a1 a2))) (\lambda (y: T).(\lambda (H6: 
(pr0 y t2)).(pr0_ind (\lambda (t0: T).(\lambda (t3: T).((eq T t0 (THead (Bind 
Abst) u t)) \to (arity g c2 t3 (AHead a1 a2))))) (\lambda (t0: T).(\lambda 
(H7: (eq T t0 (THead (Bind Abst) u t))).(let H8 \def (f_equal T T (\lambda 
(e: T).e) t0 (THead (Bind Abst) u t) H7) in (eq_ind_r T (THead (Bind Abst) u 
t) (\lambda (t3: T).(arity g c2 t3 (AHead a1 a2))) (arity_head g c2 u a1 (H1 
c2 H4 u (pr0_refl u)) t a2 (H3 (CHead c2 (Bind Abst) u) (wcpr0_comp c c2 H4 u 
u (pr0_refl u) (Bind Abst)) t (pr0_refl t))) t0 H8)))) (\lambda (u1: 
T).(\lambda (u2: T).(\lambda (H7: (pr0 u1 u2)).(\lambda (H8: (((eq T u1 
(THead (Bind Abst) u t)) \to (arity g c2 u2 (AHead a1 a2))))).(\lambda (t3: 
T).(\lambda (t4: T).(\lambda (H9: (pr0 t3 t4)).(\lambda (H10: (((eq T t3 
(THead (Bind Abst) u t)) \to (arity g c2 t4 (AHead a1 a2))))).(\lambda (k: 
K).(\lambda (H11: (eq T (THead k u1 t3) (THead (Bind Abst) u t))).(let H12 
\def (f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) 
with [(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | (THead k0 _ _) 
\Rightarrow k0])) (THead k u1 t3) (THead (Bind Abst) u t) H11) in ((let H13 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow u1 | (TLRef _) \Rightarrow u1 | (THead _ t0 _) 
\Rightarrow t0])) (THead k u1 t3) (THead (Bind Abst) u t) H11) in ((let H14 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead _ _ t0) 
\Rightarrow t0])) (THead k u1 t3) (THead (Bind Abst) u t) H11) in (\lambda 
(H15: (eq T u1 u)).(\lambda (H16: (eq K k (Bind Abst))).(eq_ind_r K (Bind 
Abst) (\lambda (k0: K).(arity g c2 (THead k0 u2 t4) (AHead a1 a2))) (let H17 
\def (eq_ind T t3 (\lambda (t0: T).((eq T t0 (THead (Bind Abst) u t)) \to 
(arity g c2 t4 (AHead a1 a2)))) H10 t H14) in (let H18 \def (eq_ind T t3 
(\lambda (t0: T).(pr0 t0 t4)) H9 t H14) in (let H19 \def (eq_ind T u1 
(\lambda (t0: T).((eq T t0 (THead (Bind Abst) u t)) \to (arity g c2 u2 (AHead 
a1 a2)))) H8 u H15) in (let H20 \def (eq_ind T u1 (\lambda (t0: T).(pr0 t0 
u2)) H7 u H15) in (arity_head g c2 u2 a1 (H1 c2 H4 u2 H20) t4 a2 (H3 (CHead 
c2 (Bind Abst) u2) (wcpr0_comp c c2 H4 u u2 H20 (Bind Abst)) t4 H18)))))) k 
H16)))) H13)) H12)))))))))))) (\lambda (u0: T).(\lambda (v1: T).(\lambda (v2: 
T).(\lambda (_: (pr0 v1 v2)).(\lambda (_: (((eq T v1 (THead (Bind Abst) u t)) 
\to (arity g c2 v2 (AHead a1 a2))))).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (_: (pr0 t3 t4)).(\lambda (_: (((eq T t3 (THead (Bind Abst) u t)) 
\to (arity g c2 t4 (AHead a1 a2))))).(\lambda (H11: (eq T (THead (Flat Appl) 
v1 (THead (Bind Abst) u0 t3)) (THead (Bind Abst) u t))).(let H12 \def (eq_ind 
T (THead (Flat Appl) v1 (THead (Bind Abst) u0 t3)) (\lambda (ee: T).(match ee 
in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef 
_) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind Abst) u t) H11) in (False_ind (arity g c2 (THead 
(Bind Abbr) v2 t4) (AHead a1 a2)) H12)))))))))))) (\lambda (b: B).(\lambda 
(_: (not (eq B b Abst))).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (pr0 
v1 v2)).(\lambda (_: (((eq T v1 (THead (Bind Abst) u t)) \to (arity g c2 v2 
(AHead a1 a2))))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (pr0 u1 
u2)).(\lambda (_: (((eq T u1 (THead (Bind Abst) u t)) \to (arity g c2 u2 
(AHead a1 a2))))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (pr0 t3 
t4)).(\lambda (_: (((eq T t3 (THead (Bind Abst) u t)) \to (arity g c2 t4 
(AHead a1 a2))))).(\lambda (H14: (eq T (THead (Flat Appl) v1 (THead (Bind b) 
u1 t3)) (THead (Bind Abst) u t))).(let H15 \def (eq_ind T (THead (Flat Appl) 
v1 (THead (Bind b) u1 t3)) (\lambda (ee: T).(match ee in T return (\lambda 
(_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False 
| (THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind 
Abst) u t) H14) in (False_ind (arity g c2 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t4)) (AHead a1 a2)) H15))))))))))))))))) (\lambda 
(u1: T).(\lambda (u2: T).(\lambda (_: (pr0 u1 u2)).(\lambda (_: (((eq T u1 
(THead (Bind Abst) u t)) \to (arity g c2 u2 (AHead a1 a2))))).(\lambda (t3: 
T).(\lambda (t4: T).(\lambda (_: (pr0 t3 t4)).(\lambda (_: (((eq T t3 (THead 
(Bind Abst) u t)) \to (arity g c2 t4 (AHead a1 a2))))).(\lambda (w: 
T).(\lambda (_: (subst0 O u2 t4 w)).(\lambda (H12: (eq T (THead (Bind Abbr) 
u1 t3) (THead (Bind Abst) u t))).(let H13 \def (eq_ind T (THead (Bind Abbr) 
u1 t3) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind b) 
\Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow 
True | Abst \Rightarrow False | Void \Rightarrow False]) | (Flat _) 
\Rightarrow False])])) I (THead (Bind Abst) u t) H12) in (False_ind (arity g 
c2 (THead (Bind Abbr) u2 w) (AHead a1 a2)) H13))))))))))))) (\lambda (b: 
B).(\lambda (H7: (not (eq B b Abst))).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (_: (pr0 t3 t4)).(\lambda (H9: (((eq T t3 (THead (Bind Abst) u 
t)) \to (arity g c2 t4 (AHead a1 a2))))).(\lambda (u0: T).(\lambda (H10: (eq 
T (THead (Bind b) u0 (lift (S O) O t3)) (THead (Bind Abst) u t))).(let H11 
\def (f_equal T B (\lambda (e: T).(match e in T return (\lambda (_: T).B) 
with [(TSort _) \Rightarrow b | (TLRef _) \Rightarrow b | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow b])])) (THead (Bind b) u0 (lift (S O) O 
t3)) (THead (Bind Abst) u t) H10) in ((let H12 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u0 | 
(TLRef _) \Rightarrow u0 | (THead _ t0 _) \Rightarrow t0])) (THead (Bind b) 
u0 (lift (S O) O t3)) (THead (Bind Abst) u t) H10) in ((let H13 \def (f_equal 
T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow ((let rec lref_map (f: ((nat \to nat))) (d: nat) (t0: T) on t0: T 
\def (match t0 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow 
(TLRef (match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) 
| (THead k u1 t5) \Rightarrow (THead k (lref_map f d u1) (lref_map f (s k d) 
t5))]) in lref_map) (\lambda (x: nat).(plus x (S O))) O t3) | (TLRef _) 
\Rightarrow ((let rec lref_map (f: ((nat \to nat))) (d: nat) (t0: T) on t0: T 
\def (match t0 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow 
(TLRef (match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) 
| (THead k u1 t5) \Rightarrow (THead k (lref_map f d u1) (lref_map f (s k d) 
t5))]) in lref_map) (\lambda (x: nat).(plus x (S O))) O t3) | (THead _ _ t0) 
\Rightarrow t0])) (THead (Bind b) u0 (lift (S O) O t3)) (THead (Bind Abst) u 
t) H10) in (\lambda (_: (eq T u0 u)).(\lambda (H15: (eq B b Abst)).(let H16 
\def (eq_ind B b (\lambda (b0: B).(not (eq B b0 Abst))) H7 Abst H15) in (let 
H17 \def (eq_ind_r T t (\lambda (t0: T).((eq T t3 (THead (Bind Abst) u t0)) 
\to (arity g c2 t4 (AHead a1 a2)))) H9 (lift (S O) O t3) H13) in (let H18 
\def (eq_ind_r T t (\lambda (t0: T).(\forall (c3: C).((wcpr0 (CHead c (Bind 
Abst) u) c3) \to (\forall (t5: T).((pr0 t0 t5) \to (arity g c3 t5 a2)))))) H3 
(lift (S O) O t3) H13) in (let H19 \def (eq_ind_r T t (\lambda (t0: T).(arity 
g (CHead c (Bind Abst) u) t0 a2)) H2 (lift (S O) O t3) H13) in (let H20 \def 
(match (H16 (refl_equal B Abst)) in False return (\lambda (_: False).(arity g 
c2 t4 (AHead a1 a2))) with []) in H20)))))))) H12)) H11)))))))))) (\lambda 
(t3: T).(\lambda (t4: T).(\lambda (_: (pr0 t3 t4)).(\lambda (_: (((eq T t3 
(THead (Bind Abst) u t)) \to (arity g c2 t4 (AHead a1 a2))))).(\lambda (u0: 
T).(\lambda (H9: (eq T (THead (Flat Cast) u0 t3) (THead (Bind Abst) u 
t))).(let H10 \def (eq_ind T (THead (Flat Cast) u0 t3) (\lambda (ee: 
T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K 
return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) I (THead (Bind Abst) u t) H9) in (False_ind (arity g c2 
t4 (AHead a1 a2)) H10)))))))) y t2 H6))) H5)))))))))))))) (\lambda (c: 
C).(\lambda (u: T).(\lambda (a1: A).(\lambda (_: (arity g c u a1)).(\lambda 
(H1: ((\forall (c2: C).((wcpr0 c c2) \to (\forall (t2: T).((pr0 u t2) \to 
(arity g c2 t2 a1))))))).(\lambda (t: T).(\lambda (a2: A).(\lambda (H2: 
(arity g c t (AHead a1 a2))).(\lambda (H3: ((\forall (c2: C).((wcpr0 c c2) 
\to (\forall (t2: T).((pr0 t t2) \to (arity g c2 t2 (AHead a1 
a2)))))))).(\lambda (c2: C).(\lambda (H4: (wcpr0 c c2)).(\lambda (t2: 
T).(\lambda (H5: (pr0 (THead (Flat Appl) u t) t2)).(insert_eq T (THead (Flat 
Appl) u t) (\lambda (t0: T).(pr0 t0 t2)) (\lambda (_: T).(arity g c2 t2 a2)) 
(\lambda (y: T).(\lambda (H6: (pr0 y t2)).(pr0_ind (\lambda (t0: T).(\lambda 
(t3: T).((eq T t0 (THead (Flat Appl) u t)) \to (arity g c2 t3 a2)))) (\lambda 
(t0: T).(\lambda (H7: (eq T t0 (THead (Flat Appl) u t))).(let H8 \def 
(f_equal T T (\lambda (e: T).e) t0 (THead (Flat Appl) u t) H7) in (eq_ind_r T 
(THead (Flat Appl) u t) (\lambda (t3: T).(arity g c2 t3 a2)) (arity_appl g c2 
u a1 (H1 c2 H4 u (pr0_refl u)) t a2 (H3 c2 H4 t (pr0_refl t))) t0 H8)))) 
(\lambda (u1: T).(\lambda (u2: T).(\lambda (H7: (pr0 u1 u2)).(\lambda (H8: 
(((eq T u1 (THead (Flat Appl) u t)) \to (arity g c2 u2 a2)))).(\lambda (t3: 
T).(\lambda (t4: T).(\lambda (H9: (pr0 t3 t4)).(\lambda (H10: (((eq T t3 
(THead (Flat Appl) u t)) \to (arity g c2 t4 a2)))).(\lambda (k: K).(\lambda 
(H11: (eq T (THead k u1 t3) (THead (Flat Appl) u t))).(let H12 \def (f_equal 
T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) with [(TSort _) 
\Rightarrow k | (TLRef _) \Rightarrow k | (THead k0 _ _) \Rightarrow k0])) 
(THead k u1 t3) (THead (Flat Appl) u t) H11) in ((let H13 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u1 | (TLRef _) \Rightarrow u1 | (THead _ t0 _) \Rightarrow t0])) 
(THead k u1 t3) (THead (Flat Appl) u t) H11) in ((let H14 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead _ _ t0) \Rightarrow t0])) 
(THead k u1 t3) (THead (Flat Appl) u t) H11) in (\lambda (H15: (eq T u1 
u)).(\lambda (H16: (eq K k (Flat Appl))).(eq_ind_r K (Flat Appl) (\lambda 
(k0: K).(arity g c2 (THead k0 u2 t4) a2)) (let H17 \def (eq_ind T t3 (\lambda 
(t0: T).((eq T t0 (THead (Flat Appl) u t)) \to (arity g c2 t4 a2))) H10 t 
H14) in (let H18 \def (eq_ind T t3 (\lambda (t0: T).(pr0 t0 t4)) H9 t H14) in 
(let H19 \def (eq_ind T u1 (\lambda (t0: T).((eq T t0 (THead (Flat Appl) u 
t)) \to (arity g c2 u2 a2))) H8 u H15) in (let H20 \def (eq_ind T u1 (\lambda 
(t0: T).(pr0 t0 u2)) H7 u H15) in (arity_appl g c2 u2 a1 (H1 c2 H4 u2 H20) t4 
a2 (H3 c2 H4 t4 H18)))))) k H16)))) H13)) H12)))))))))))) (\lambda (u0: 
T).(\lambda (v1: T).(\lambda (v2: T).(\lambda (H7: (pr0 v1 v2)).(\lambda (H8: 
(((eq T v1 (THead (Flat Appl) u t)) \to (arity g c2 v2 a2)))).(\lambda (t3: 
T).(\lambda (t4: T).(\lambda (H9: (pr0 t3 t4)).(\lambda (H10: (((eq T t3 
(THead (Flat Appl) u t)) \to (arity g c2 t4 a2)))).(\lambda (H11: (eq T 
(THead (Flat Appl) v1 (THead (Bind Abst) u0 t3)) (THead (Flat Appl) u 
t))).(let H12 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda 
(_: T).T) with [(TSort _) \Rightarrow v1 | (TLRef _) \Rightarrow v1 | (THead 
_ t0 _) \Rightarrow t0])) (THead (Flat Appl) v1 (THead (Bind Abst) u0 t3)) 
(THead (Flat Appl) u t) H11) in ((let H13 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow (THead 
(Bind Abst) u0 t3) | (TLRef _) \Rightarrow (THead (Bind Abst) u0 t3) | (THead 
_ _ t0) \Rightarrow t0])) (THead (Flat Appl) v1 (THead (Bind Abst) u0 t3)) 
(THead (Flat Appl) u t) H11) in (\lambda (H14: (eq T v1 u)).(let H15 \def 
(eq_ind T v1 (\lambda (t0: T).((eq T t0 (THead (Flat Appl) u t)) \to (arity g 
c2 v2 a2))) H8 u H14) in (let H16 \def (eq_ind T v1 (\lambda (t0: T).(pr0 t0 
v2)) H7 u H14) in (let H17 \def (eq_ind_r T t (\lambda (t0: T).((eq T t3 
(THead (Flat Appl) u t0)) \to (arity g c2 t4 a2))) H10 (THead (Bind Abst) u0 
t3) H13) in (let H18 \def (eq_ind_r T t (\lambda (t0: T).((eq T u (THead 
(Flat Appl) u t0)) \to (arity g c2 v2 a2))) H15 (THead (Bind Abst) u0 t3) 
H13) in (let H19 \def (eq_ind_r T t (\lambda (t0: T).(\forall (c3: C).((wcpr0 
c c3) \to (\forall (t5: T).((pr0 t0 t5) \to (arity g c3 t5 (AHead a1 
a2))))))) H3 (THead (Bind Abst) u0 t3) H13) in (let H20 \def (eq_ind_r T t 
(\lambda (t0: T).(arity g c t0 (AHead a1 a2))) H2 (THead (Bind Abst) u0 t3) 
H13) in (let H21 \def (H1 c2 H4 v2 H16) in (let H22 \def (H19 c2 H4 (THead 
(Bind Abst) u0 t4) (pr0_comp u0 u0 (pr0_refl u0) t3 t4 H9 (Bind Abst))) in 
(let H23 \def (arity_gen_abst g c2 u0 t4 (AHead a1 a2) H22) in (ex3_2_ind A A 
(\lambda (a3: A).(\lambda (a4: A).(eq A (AHead a1 a2) (AHead a3 a4)))) 
(\lambda (a3: A).(\lambda (_: A).(arity g c2 u0 (asucc g a3)))) (\lambda (_: 
A).(\lambda (a4: A).(arity g (CHead c2 (Bind Abst) u0) t4 a4))) (arity g c2 
(THead (Bind Abbr) v2 t4) a2) (\lambda (x0: A).(\lambda (x1: A).(\lambda 
(H24: (eq A (AHead a1 a2) (AHead x0 x1))).(\lambda (H25: (arity g c2 u0 
(asucc g x0))).(\lambda (H26: (arity g (CHead c2 (Bind Abst) u0) t4 x1)).(let 
H27 \def (f_equal A A (\lambda (e: A).(match e in A return (\lambda (_: A).A) 
with [(ASort _ _) \Rightarrow a1 | (AHead a0 _) \Rightarrow a0])) (AHead a1 
a2) (AHead x0 x1) H24) in ((let H28 \def (f_equal A A (\lambda (e: A).(match 
e in A return (\lambda (_: A).A) with [(ASort _ _) \Rightarrow a2 | (AHead _ 
a0) \Rightarrow a0])) (AHead a1 a2) (AHead x0 x1) H24) in (\lambda (H29: (eq 
A a1 x0)).(let H30 \def (eq_ind_r A x1 (\lambda (a0: A).(arity g (CHead c2 
(Bind Abst) u0) t4 a0)) H26 a2 H28) in (let H31 \def (eq_ind_r A x0 (\lambda 
(a0: A).(arity g c2 u0 (asucc g a0))) H25 a1 H29) in (arity_bind g Abbr 
not_abbr_abst c2 v2 a1 H21 t4 a2 (csuba_arity g (CHead c2 (Bind Abst) u0) t4 
a2 H30 (CHead c2 (Bind Abbr) v2) (csuba_abst g c2 c2 (csuba_refl g c2) u0 a1 
H31 v2 H21))))))) H27))))))) H23)))))))))))) H12)))))))))))) (\lambda (b: 
B).(\lambda (H7: (not (eq B b Abst))).(\lambda (v1: T).(\lambda (v2: 
T).(\lambda (H8: (pr0 v1 v2)).(\lambda (H9: (((eq T v1 (THead (Flat Appl) u 
t)) \to (arity g c2 v2 a2)))).(\lambda (u1: T).(\lambda (u2: T).(\lambda 
(H10: (pr0 u1 u2)).(\lambda (H11: (((eq T u1 (THead (Flat Appl) u t)) \to 
(arity g c2 u2 a2)))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H12: (pr0 
t3 t4)).(\lambda (H13: (((eq T t3 (THead (Flat Appl) u t)) \to (arity g c2 t4 
a2)))).(\lambda (H14: (eq T (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) 
(THead (Flat Appl) u t))).(let H15 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow v1 | (TLRef _) 
\Rightarrow v1 | (THead _ t0 _) \Rightarrow t0])) (THead (Flat Appl) v1 
(THead (Bind b) u1 t3)) (THead (Flat Appl) u t) H14) in ((let H16 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow (THead (Bind b) u1 t3) | (TLRef _) \Rightarrow (THead 
(Bind b) u1 t3) | (THead _ _ t0) \Rightarrow t0])) (THead (Flat Appl) v1 
(THead (Bind b) u1 t3)) (THead (Flat Appl) u t) H14) in (\lambda (H17: (eq T 
v1 u)).(let H18 \def (eq_ind T v1 (\lambda (t0: T).((eq T t0 (THead (Flat 
Appl) u t)) \to (arity g c2 v2 a2))) H9 u H17) in (let H19 \def (eq_ind T v1 
(\lambda (t0: T).(pr0 t0 v2)) H8 u H17) in (let H20 \def (eq_ind_r T t 
(\lambda (t0: T).((eq T t3 (THead (Flat Appl) u t0)) \to (arity g c2 t4 a2))) 
H13 (THead (Bind b) u1 t3) H16) in (let H21 \def (eq_ind_r T t (\lambda (t0: 
T).((eq T u1 (THead (Flat Appl) u t0)) \to (arity g c2 u2 a2))) H11 (THead 
(Bind b) u1 t3) H16) in (let H22 \def (eq_ind_r T t (\lambda (t0: T).((eq T u 
(THead (Flat Appl) u t0)) \to (arity g c2 v2 a2))) H18 (THead (Bind b) u1 t3) 
H16) in (let H23 \def (eq_ind_r T t (\lambda (t0: T).(\forall (c3: C).((wcpr0 
c c3) \to (\forall (t5: T).((pr0 t0 t5) \to (arity g c3 t5 (AHead a1 
a2))))))) H3 (THead (Bind b) u1 t3) H16) in (let H24 \def (eq_ind_r T t 
(\lambda (t0: T).(arity g c t0 (AHead a1 a2))) H2 (THead (Bind b) u1 t3) H16) 
in (let H25 \def (H1 c2 H4 v2 H19) in (let H26 \def (H23 c2 H4 (THead (Bind 
b) u2 t4) (pr0_comp u1 u2 H10 t3 t4 H12 (Bind b))) in (let H27 \def 
(arity_gen_bind b H7 g c2 u2 t4 (AHead a1 a2) H26) in (ex2_ind A (\lambda 
(a3: A).(arity g c2 u2 a3)) (\lambda (_: A).(arity g (CHead c2 (Bind b) u2) 
t4 (AHead a1 a2))) (arity g c2 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) a2) (\lambda (x: A).(\lambda (H28: (arity g c2 u2 x)).(\lambda 
(H29: (arity g (CHead c2 (Bind b) u2) t4 (AHead a1 a2))).(arity_bind g b H7 
c2 u2 x H28 (THead (Flat Appl) (lift (S O) O v2) t4) a2 (arity_appl g (CHead 
c2 (Bind b) u2) (lift (S O) O v2) a1 (arity_lift g c2 v2 a1 H25 (CHead c2 
(Bind b) u2) (S O) O (drop_drop (Bind b) O c2 c2 (drop_refl c2) u2)) t4 a2 
H29))))) H27))))))))))))) H15))))))))))))))))) (\lambda (u1: T).(\lambda (u2: 
T).(\lambda (_: (pr0 u1 u2)).(\lambda (_: (((eq T u1 (THead (Flat Appl) u t)) 
\to (arity g c2 u2 a2)))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (pr0 
t3 t4)).(\lambda (_: (((eq T t3 (THead (Flat Appl) u t)) \to (arity g c2 t4 
a2)))).(\lambda (w: T).(\lambda (_: (subst0 O u2 t4 w)).(\lambda (H12: (eq T 
(THead (Bind Abbr) u1 t3) (THead (Flat Appl) u t))).(let H13 \def (eq_ind T 
(THead (Bind Abbr) u1 t3) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat 
Appl) u t) H12) in (False_ind (arity g c2 (THead (Bind Abbr) u2 w) a2) 
H13))))))))))))) (\lambda (b: B).(\lambda (_: (not (eq B b Abst))).(\lambda 
(t3: T).(\lambda (t4: T).(\lambda (_: (pr0 t3 t4)).(\lambda (_: (((eq T t3 
(THead (Flat Appl) u t)) \to (arity g c2 t4 a2)))).(\lambda (u0: T).(\lambda 
(H10: (eq T (THead (Bind b) u0 (lift (S O) O t3)) (THead (Flat Appl) u 
t))).(let H11 \def (eq_ind T (THead (Bind b) u0 (lift (S O) O t3)) (\lambda 
(ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | 
(Flat _) \Rightarrow False])])) I (THead (Flat Appl) u t) H10) in (False_ind 
(arity g c2 t4 a2) H11)))))))))) (\lambda (t3: T).(\lambda (t4: T).(\lambda 
(_: (pr0 t3 t4)).(\lambda (_: (((eq T t3 (THead (Flat Appl) u t)) \to (arity 
g c2 t4 a2)))).(\lambda (u0: T).(\lambda (H9: (eq T (THead (Flat Cast) u0 t3) 
(THead (Flat Appl) u t))).(let H10 \def (eq_ind T (THead (Flat Cast) u0 t3) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | 
(Flat f) \Rightarrow (match f in F return (\lambda (_: F).Prop) with [Appl 
\Rightarrow False | Cast \Rightarrow True])])])) I (THead (Flat Appl) u t) 
H9) in (False_ind (arity g c2 t4 a2) H10)))))))) y t2 H6))) H5)))))))))))))) 
(\lambda (c: C).(\lambda (u: T).(\lambda (a0: A).(\lambda (_: (arity g c u 
(asucc g a0))).(\lambda (H1: ((\forall (c2: C).((wcpr0 c c2) \to (\forall 
(t2: T).((pr0 u t2) \to (arity g c2 t2 (asucc g a0)))))))).(\lambda (t: 
T).(\lambda (_: (arity g c t a0)).(\lambda (H3: ((\forall (c2: C).((wcpr0 c 
c2) \to (\forall (t2: T).((pr0 t t2) \to (arity g c2 t2 a0))))))).(\lambda 
(c2: C).(\lambda (H4: (wcpr0 c c2)).(\lambda (t2: T).(\lambda (H5: (pr0 
(THead (Flat Cast) u t) t2)).(insert_eq T (THead (Flat Cast) u t) (\lambda 
(t0: T).(pr0 t0 t2)) (\lambda (_: T).(arity g c2 t2 a0)) (\lambda (y: 
T).(\lambda (H6: (pr0 y t2)).(pr0_ind (\lambda (t0: T).(\lambda (t3: T).((eq 
T t0 (THead (Flat Cast) u t)) \to (arity g c2 t3 a0)))) (\lambda (t0: 
T).(\lambda (H7: (eq T t0 (THead (Flat Cast) u t))).(let H8 \def (f_equal T T 
(\lambda (e: T).e) t0 (THead (Flat Cast) u t) H7) in (eq_ind_r T (THead (Flat 
Cast) u t) (\lambda (t3: T).(arity g c2 t3 a0)) (arity_cast g c2 u a0 (H1 c2 
H4 u (pr0_refl u)) t (H3 c2 H4 t (pr0_refl t))) t0 H8)))) (\lambda (u1: 
T).(\lambda (u2: T).(\lambda (H7: (pr0 u1 u2)).(\lambda (H8: (((eq T u1 
(THead (Flat Cast) u t)) \to (arity g c2 u2 a0)))).(\lambda (t3: T).(\lambda 
(t4: T).(\lambda (H9: (pr0 t3 t4)).(\lambda (H10: (((eq T t3 (THead (Flat 
Cast) u t)) \to (arity g c2 t4 a0)))).(\lambda (k: K).(\lambda (H11: (eq T 
(THead k u1 t3) (THead (Flat Cast) u t))).(let H12 \def (f_equal T K (\lambda 
(e: T).(match e in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k 
| (TLRef _) \Rightarrow k | (THead k0 _ _) \Rightarrow k0])) (THead k u1 t3) 
(THead (Flat Cast) u t) H11) in ((let H13 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u1 | 
(TLRef _) \Rightarrow u1 | (THead _ t0 _) \Rightarrow t0])) (THead k u1 t3) 
(THead (Flat Cast) u t) H11) in ((let H14 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t3 | 
(TLRef _) \Rightarrow t3 | (THead _ _ t0) \Rightarrow t0])) (THead k u1 t3) 
(THead (Flat Cast) u t) H11) in (\lambda (H15: (eq T u1 u)).(\lambda (H16: 
(eq K k (Flat Cast))).(eq_ind_r K (Flat Cast) (\lambda (k0: K).(arity g c2 
(THead k0 u2 t4) a0)) (let H17 \def (eq_ind T t3 (\lambda (t0: T).((eq T t0 
(THead (Flat Cast) u t)) \to (arity g c2 t4 a0))) H10 t H14) in (let H18 \def 
(eq_ind T t3 (\lambda (t0: T).(pr0 t0 t4)) H9 t H14) in (let H19 \def (eq_ind 
T u1 (\lambda (t0: T).((eq T t0 (THead (Flat Cast) u t)) \to (arity g c2 u2 
a0))) H8 u H15) in (let H20 \def (eq_ind T u1 (\lambda (t0: T).(pr0 t0 u2)) 
H7 u H15) in (arity_cast g c2 u2 a0 (H1 c2 H4 u2 H20) t4 (H3 c2 H4 t4 
H18)))))) k H16)))) H13)) H12)))))))))))) (\lambda (u0: T).(\lambda (v1: 
T).(\lambda (v2: T).(\lambda (_: (pr0 v1 v2)).(\lambda (_: (((eq T v1 (THead 
(Flat Cast) u t)) \to (arity g c2 v2 a0)))).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (_: (pr0 t3 t4)).(\lambda (_: (((eq T t3 (THead (Flat Cast) u t)) 
\to (arity g c2 t4 a0)))).(\lambda (H11: (eq T (THead (Flat Appl) v1 (THead 
(Bind Abst) u0 t3)) (THead (Flat Cast) u t))).(let H12 \def (eq_ind T (THead 
(Flat Appl) v1 (THead (Bind Abst) u0 t3)) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat f) \Rightarrow (match f 
in F return (\lambda (_: F).Prop) with [Appl \Rightarrow True | Cast 
\Rightarrow False])])])) I (THead (Flat Cast) u t) H11) in (False_ind (arity 
g c2 (THead (Bind Abbr) v2 t4) a0) H12)))))))))))) (\lambda (b: B).(\lambda 
(_: (not (eq B b Abst))).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (pr0 
v1 v2)).(\lambda (_: (((eq T v1 (THead (Flat Cast) u t)) \to (arity g c2 v2 
a0)))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (pr0 u1 u2)).(\lambda 
(_: (((eq T u1 (THead (Flat Cast) u t)) \to (arity g c2 u2 a0)))).(\lambda 
(t3: T).(\lambda (t4: T).(\lambda (_: (pr0 t3 t4)).(\lambda (_: (((eq T t3 
(THead (Flat Cast) u t)) \to (arity g c2 t4 a0)))).(\lambda (H14: (eq T 
(THead (Flat Appl) v1 (THead (Bind b) u1 t3)) (THead (Flat Cast) u t))).(let 
H15 \def (eq_ind T (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) (\lambda 
(ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | 
(Flat f) \Rightarrow (match f in F return (\lambda (_: F).Prop) with [Appl 
\Rightarrow True | Cast \Rightarrow False])])])) I (THead (Flat Cast) u t) 
H14) in (False_ind (arity g c2 (THead (Bind b) u2 (THead (Flat Appl) (lift (S 
O) O v2) t4)) a0) H15))))))))))))))))) (\lambda (u1: T).(\lambda (u2: 
T).(\lambda (_: (pr0 u1 u2)).(\lambda (_: (((eq T u1 (THead (Flat Cast) u t)) 
\to (arity g c2 u2 a0)))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (pr0 
t3 t4)).(\lambda (_: (((eq T t3 (THead (Flat Cast) u t)) \to (arity g c2 t4 
a0)))).(\lambda (w: T).(\lambda (_: (subst0 O u2 t4 w)).(\lambda (H12: (eq T 
(THead (Bind Abbr) u1 t3) (THead (Flat Cast) u t))).(let H13 \def (eq_ind T 
(THead (Bind Abbr) u1 t3) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat 
Cast) u t) H12) in (False_ind (arity g c2 (THead (Bind Abbr) u2 w) a0) 
H13))))))))))))) (\lambda (b: B).(\lambda (_: (not (eq B b Abst))).(\lambda 
(t3: T).(\lambda (t4: T).(\lambda (_: (pr0 t3 t4)).(\lambda (_: (((eq T t3 
(THead (Flat Cast) u t)) \to (arity g c2 t4 a0)))).(\lambda (u0: T).(\lambda 
(H10: (eq T (THead (Bind b) u0 (lift (S O) O t3)) (THead (Flat Cast) u 
t))).(let H11 \def (eq_ind T (THead (Bind b) u0 (lift (S O) O t3)) (\lambda 
(ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow True | 
(Flat _) \Rightarrow False])])) I (THead (Flat Cast) u t) H10) in (False_ind 
(arity g c2 t4 a0) H11)))))))))) (\lambda (t3: T).(\lambda (t4: T).(\lambda 
(H7: (pr0 t3 t4)).(\lambda (H8: (((eq T t3 (THead (Flat Cast) u t)) \to 
(arity g c2 t4 a0)))).(\lambda (u0: T).(\lambda (H9: (eq T (THead (Flat Cast) 
u0 t3) (THead (Flat Cast) u t))).(let H10 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u0 | 
(TLRef _) \Rightarrow u0 | (THead _ t0 _) \Rightarrow t0])) (THead (Flat 
Cast) u0 t3) (THead (Flat Cast) u t) H9) in ((let H11 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead _ _ t0) \Rightarrow t0])) 
(THead (Flat Cast) u0 t3) (THead (Flat Cast) u t) H9) in (\lambda (_: (eq T 
u0 u)).(let H13 \def (eq_ind T t3 (\lambda (t0: T).((eq T t0 (THead (Flat 
Cast) u t)) \to (arity g c2 t4 a0))) H8 t H11) in (let H14 \def (eq_ind T t3 
(\lambda (t0: T).(pr0 t0 t4)) H7 t H11) in (H3 c2 H4 t4 H14))))) H10)))))))) 
y t2 H6))) H5))))))))))))) (\lambda (c: C).(\lambda (t: T).(\lambda (a1: 
A).(\lambda (_: (arity g c t a1)).(\lambda (H1: ((\forall (c2: C).((wcpr0 c 
c2) \to (\forall (t2: T).((pr0 t t2) \to (arity g c2 t2 a1))))))).(\lambda 
(a2: A).(\lambda (H2: (leq g a1 a2)).(\lambda (c2: C).(\lambda (H3: (wcpr0 c 
c2)).(\lambda (t2: T).(\lambda (H4: (pr0 t t2)).(arity_repl g c2 t2 a1 (H1 c2 
H3 t2 H4) a2 H2)))))))))))) c1 t1 a H))))).
(* COMMENTS
Initial nodes: 10246
END *)

theorem arity_sred_wcpr0_pr1:
 \forall (t1: T).(\forall (t2: T).((pr1 t1 t2) \to (\forall (g: G).(\forall 
(c1: C).(\forall (a: A).((arity g c1 t1 a) \to (\forall (c2: C).((wcpr0 c1 
c2) \to (arity g c2 t2 a)))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr1 t1 t2)).(pr1_ind (\lambda 
(t: T).(\lambda (t0: T).(\forall (g: G).(\forall (c1: C).(\forall (a: 
A).((arity g c1 t a) \to (\forall (c2: C).((wcpr0 c1 c2) \to (arity g c2 t0 
a))))))))) (\lambda (t: T).(\lambda (g: G).(\lambda (c1: C).(\lambda (a: 
A).(\lambda (H0: (arity g c1 t a)).(\lambda (c2: C).(\lambda (H1: (wcpr0 c1 
c2)).(arity_sred_wcpr0_pr0 g c1 t a H0 c2 H1 t (pr0_refl t))))))))) (\lambda 
(t3: T).(\lambda (t4: T).(\lambda (H0: (pr0 t4 t3)).(\lambda (t5: T).(\lambda 
(_: (pr1 t3 t5)).(\lambda (H2: ((\forall (g: G).(\forall (c1: C).(\forall (a: 
A).((arity g c1 t3 a) \to (\forall (c2: C).((wcpr0 c1 c2) \to (arity g c2 t5 
a))))))))).(\lambda (g: G).(\lambda (c1: C).(\lambda (a: A).(\lambda (H3: 
(arity g c1 t4 a)).(\lambda (c2: C).(\lambda (H4: (wcpr0 c1 c2)).(H2 g c2 a 
(arity_sred_wcpr0_pr0 g c1 t4 a H3 c2 H4 t3 H0) c2 (wcpr0_refl 
c2)))))))))))))) t1 t2 H))).
(* COMMENTS
Initial nodes: 213
END *)

theorem arity_sred_pr2:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall 
(g: G).(\forall (a: A).((arity g c t1 a) \to (arity g c t2 a)))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr2 c t1 
t2)).(pr2_ind (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).(\forall (g: 
G).(\forall (a: A).((arity g c0 t a) \to (arity g c0 t0 a))))))) (\lambda 
(c0: C).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H0: (pr0 t3 t4)).(\lambda 
(g: G).(\lambda (a: A).(\lambda (H1: (arity g c0 t3 a)).(arity_sred_wcpr0_pr0 
g c0 t3 a H1 c0 (wcpr0_refl c0) t4 H0)))))))) (\lambda (c0: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind 
Abbr) u))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H1: (pr0 t3 
t4)).(\lambda (t: T).(\lambda (H2: (subst0 i u t4 t)).(\lambda (g: 
G).(\lambda (a: A).(\lambda (H3: (arity g c0 t3 a)).(arity_subst0 g c0 t4 a 
(arity_sred_wcpr0_pr0 g c0 t3 a H3 c0 (wcpr0_refl c0) t4 H1) d u i H0 t 
H2)))))))))))))) c t1 t2 H)))).
(* COMMENTS
Initial nodes: 205
END *)

theorem arity_sred_pr3:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (\forall 
(g: G).(\forall (a: A).((arity g c t1 a) \to (arity g c t2 a)))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr3 c t1 
t2)).(pr3_ind c (\lambda (t: T).(\lambda (t0: T).(\forall (g: G).(\forall (a: 
A).((arity g c t a) \to (arity g c t0 a)))))) (\lambda (t: T).(\lambda (g: 
G).(\lambda (a: A).(\lambda (H0: (arity g c t a)).H0)))) (\lambda (t3: 
T).(\lambda (t4: T).(\lambda (H0: (pr2 c t4 t3)).(\lambda (t5: T).(\lambda 
(_: (pr3 c t3 t5)).(\lambda (H2: ((\forall (g: G).(\forall (a: A).((arity g c 
t3 a) \to (arity g c t5 a)))))).(\lambda (g: G).(\lambda (a: A).(\lambda (H3: 
(arity g c t4 a)).(H2 g a (arity_sred_pr2 c t4 t3 H0 g a H3))))))))))) t1 t2 
H)))).
(* COMMENTS
Initial nodes: 151
END *)

