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

include "Basic-1/csubt/ty3.ma".

include "Basic-1/ty3/subst1.ma".

include "Basic-1/ty3/fsubst0.ma".

include "Basic-1/pc3/pc1.ma".

include "Basic-1/pc3/wcpr0.ma".

include "Basic-1/pc1/props.ma".

theorem ty3_sred_wcpr0_pr0:
 \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t: T).((ty3 g c1 
t1 t) \to (\forall (c2: C).((wcpr0 c1 c2) \to (\forall (t2: T).((pr0 t1 t2) 
\to (ty3 g c2 t2 t)))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t1: T).(\lambda (t: T).(\lambda 
(H: (ty3 g c1 t1 t)).(ty3_ind g (\lambda (c: C).(\lambda (t0: T).(\lambda 
(t2: T).(\forall (c2: C).((wcpr0 c c2) \to (\forall (t3: T).((pr0 t0 t3) \to 
(ty3 g c2 t3 t2)))))))) (\lambda (c: C).(\lambda (t2: T).(\lambda (t0: 
T).(\lambda (_: (ty3 g c t2 t0)).(\lambda (H1: ((\forall (c2: C).((wcpr0 c 
c2) \to (\forall (t3: T).((pr0 t2 t3) \to (ty3 g c2 t3 t0))))))).(\lambda (u: 
T).(\lambda (t3: T).(\lambda (_: (ty3 g c u t3)).(\lambda (H3: ((\forall (c2: 
C).((wcpr0 c c2) \to (\forall (t4: T).((pr0 u t4) \to (ty3 g c2 t4 
t3))))))).(\lambda (H4: (pc3 c t3 t2)).(\lambda (c2: C).(\lambda (H5: (wcpr0 
c c2)).(\lambda (t4: T).(\lambda (H6: (pr0 u t4)).(ty3_conv g c2 t2 t0 (H1 c2 
H5 t2 (pr0_refl t2)) t4 t3 (H3 c2 H5 t4 H6) (pc3_wcpr0 c c2 H5 t3 t2 
H4)))))))))))))))) (\lambda (c: C).(\lambda (m: nat).(\lambda (c2: 
C).(\lambda (_: (wcpr0 c c2)).(\lambda (t2: T).(\lambda (H1: (pr0 (TSort m) 
t2)).(eq_ind_r T (TSort m) (\lambda (t0: T).(ty3 g c2 t0 (TSort (next g m)))) 
(ty3_sort g c2 m) t2 (pr0_gen_sort t2 m H1)))))))) (\lambda (n: nat).(\lambda 
(c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (H0: (getl n c (CHead d (Bind 
Abbr) u))).(\lambda (t0: T).(\lambda (_: (ty3 g d u t0)).(\lambda (H2: 
((\forall (c2: C).((wcpr0 d c2) \to (\forall (t2: T).((pr0 u t2) \to (ty3 g 
c2 t2 t0))))))).(\lambda (c2: C).(\lambda (H3: (wcpr0 c c2)).(\lambda (t2: 
T).(\lambda (H4: (pr0 (TLRef n) t2)).(eq_ind_r T (TLRef n) (\lambda (t3: 
T).(ty3 g c2 t3 (lift (S n) O t0))) (ex3_2_ind C T (\lambda (e2: C).(\lambda 
(u2: T).(getl n c2 (CHead e2 (Bind Abbr) u2)))) (\lambda (e2: C).(\lambda (_: 
T).(wcpr0 d e2))) (\lambda (_: C).(\lambda (u2: T).(pr0 u u2))) (ty3 g c2 
(TLRef n) (lift (S n) O t0)) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H5: 
(getl n c2 (CHead x0 (Bind Abbr) x1))).(\lambda (H6: (wcpr0 d x0)).(\lambda 
(H7: (pr0 u x1)).(ty3_abbr g n c2 x0 x1 H5 t0 (H2 x0 H6 x1 H7))))))) 
(wcpr0_getl c c2 H3 n d u (Bind Abbr) H0)) t2 (pr0_gen_lref t2 n 
H4)))))))))))))) (\lambda (n: nat).(\lambda (c: C).(\lambda (d: C).(\lambda 
(u: T).(\lambda (H0: (getl n c (CHead d (Bind Abst) u))).(\lambda (t0: 
T).(\lambda (_: (ty3 g d u t0)).(\lambda (H2: ((\forall (c2: C).((wcpr0 d c2) 
\to (\forall (t2: T).((pr0 u t2) \to (ty3 g c2 t2 t0))))))).(\lambda (c2: 
C).(\lambda (H3: (wcpr0 c c2)).(\lambda (t2: T).(\lambda (H4: (pr0 (TLRef n) 
t2)).(eq_ind_r T (TLRef n) (\lambda (t3: T).(ty3 g c2 t3 (lift (S n) O u))) 
(ex3_2_ind C T (\lambda (e2: C).(\lambda (u2: T).(getl n c2 (CHead e2 (Bind 
Abst) u2)))) (\lambda (e2: C).(\lambda (_: T).(wcpr0 d e2))) (\lambda (_: 
C).(\lambda (u2: T).(pr0 u u2))) (ty3 g c2 (TLRef n) (lift (S n) O u)) 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (H5: (getl n c2 (CHead x0 (Bind 
Abst) x1))).(\lambda (H6: (wcpr0 d x0)).(\lambda (H7: (pr0 u x1)).(ty3_conv g 
c2 (lift (S n) O u) (lift (S n) O t0) (ty3_lift g x0 u t0 (H2 x0 H6 u 
(pr0_refl u)) c2 O (S n) (getl_drop Abst c2 x0 x1 n H5)) (TLRef n) (lift (S 
n) O x1) (ty3_abst g n c2 x0 x1 H5 t0 (H2 x0 H6 x1 H7)) (pc3_lift c2 x0 (S n) 
O (getl_drop Abst c2 x0 x1 n H5) x1 u (pc3_pr2_x x0 x1 u (pr2_free x0 u x1 
H7))))))))) (wcpr0_getl c c2 H3 n d u (Bind Abst) H0)) t2 (pr0_gen_lref t2 n 
H4)))))))))))))) (\lambda (c: C).(\lambda (u: T).(\lambda (t0: T).(\lambda 
(_: (ty3 g c u t0)).(\lambda (H1: ((\forall (c2: C).((wcpr0 c c2) \to 
(\forall (t2: T).((pr0 u t2) \to (ty3 g c2 t2 t0))))))).(\lambda (b: 
B).(\lambda (t2: T).(\lambda (t3: T).(\lambda (H2: (ty3 g (CHead c (Bind b) 
u) t2 t3)).(\lambda (H3: ((\forall (c2: C).((wcpr0 (CHead c (Bind b) u) c2) 
\to (\forall (t4: T).((pr0 t2 t4) \to (ty3 g c2 t4 t3))))))).(\lambda (c2: 
C).(\lambda (H4: (wcpr0 c c2)).(\lambda (t4: T).(\lambda (H5: (pr0 (THead 
(Bind b) u t2) t4)).(let H6 \def (match H5 in pr0 return (\lambda (t5: 
T).(\lambda (t6: T).(\lambda (_: (pr0 t5 t6)).((eq T t5 (THead (Bind b) u 
t2)) \to ((eq T t6 t4) \to (ty3 g c2 t4 (THead (Bind b) u t3))))))) with 
[(pr0_refl t5) \Rightarrow (\lambda (H6: (eq T t5 (THead (Bind b) u 
t2))).(\lambda (H7: (eq T t5 t4)).(eq_ind T (THead (Bind b) u t2) (\lambda 
(t6: T).((eq T t6 t4) \to (ty3 g c2 t4 (THead (Bind b) u t3)))) (\lambda (H8: 
(eq T (THead (Bind b) u t2) t4)).(eq_ind T (THead (Bind b) u t2) (\lambda 
(t6: T).(ty3 g c2 t6 (THead (Bind b) u t3))) (ty3_bind g c2 u t0 (H1 c2 H4 u 
(pr0_refl u)) b t2 t3 (H3 (CHead c2 (Bind b) u) (wcpr0_comp c c2 H4 u u 
(pr0_refl u) (Bind b)) t2 (pr0_refl t2))) t4 H8)) t5 (sym_eq T t5 (THead 
(Bind b) u t2) H6) H7))) | (pr0_comp u1 u2 H6 t5 t6 H7 k) \Rightarrow 
(\lambda (H8: (eq T (THead k u1 t5) (THead (Bind b) u t2))).(\lambda (H9: (eq 
T (THead k u2 t6) t4)).((let H10 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t5 | (TLRef _) 
\Rightarrow t5 | (THead _ _ t7) \Rightarrow t7])) (THead k u1 t5) (THead 
(Bind b) u t2) H8) in ((let H11 \def (f_equal T T (\lambda (e: T).(match e in 
T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u1 | (TLRef _) 
\Rightarrow u1 | (THead _ t7 _) \Rightarrow t7])) (THead k u1 t5) (THead 
(Bind b) u t2) H8) in ((let H12 \def (f_equal T K (\lambda (e: T).(match e in 
T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k0 _ _) \Rightarrow k0])) (THead k u1 t5) (THead (Bind 
b) u t2) H8) in (eq_ind K (Bind b) (\lambda (k0: K).((eq T u1 u) \to ((eq T 
t5 t2) \to ((eq T (THead k0 u2 t6) t4) \to ((pr0 u1 u2) \to ((pr0 t5 t6) \to 
(ty3 g c2 t4 (THead (Bind b) u t3)))))))) (\lambda (H13: (eq T u1 u)).(eq_ind 
T u (\lambda (t7: T).((eq T t5 t2) \to ((eq T (THead (Bind b) u2 t6) t4) \to 
((pr0 t7 u2) \to ((pr0 t5 t6) \to (ty3 g c2 t4 (THead (Bind b) u t3))))))) 
(\lambda (H14: (eq T t5 t2)).(eq_ind T t2 (\lambda (t7: T).((eq T (THead 
(Bind b) u2 t6) t4) \to ((pr0 u u2) \to ((pr0 t7 t6) \to (ty3 g c2 t4 (THead 
(Bind b) u t3)))))) (\lambda (H15: (eq T (THead (Bind b) u2 t6) t4)).(eq_ind 
T (THead (Bind b) u2 t6) (\lambda (t7: T).((pr0 u u2) \to ((pr0 t2 t6) \to 
(ty3 g c2 t7 (THead (Bind b) u t3))))) (\lambda (H16: (pr0 u u2)).(\lambda 
(H17: (pr0 t2 t6)).(ex_ind T (\lambda (t7: T).(ty3 g (CHead c2 (Bind b) u) t3 
t7)) (ty3 g c2 (THead (Bind b) u2 t6) (THead (Bind b) u t3)) (\lambda (x: 
T).(\lambda (H18: (ty3 g (CHead c2 (Bind b) u) t3 x)).(ex_ind T (\lambda (t7: 
T).(ty3 g (CHead c2 (Bind b) u2) t3 t7)) (ty3 g c2 (THead (Bind b) u2 t6) 
(THead (Bind b) u t3)) (\lambda (x0: T).(\lambda (_: (ty3 g (CHead c2 (Bind 
b) u2) t3 x0)).(ty3_conv g c2 (THead (Bind b) u t3) (THead (Bind b) u x) 
(ty3_bind g c2 u t0 (H1 c2 H4 u (pr0_refl u)) b t3 x H18) (THead (Bind b) u2 
t6) (THead (Bind b) u2 t3) (ty3_bind g c2 u2 t0 (H1 c2 H4 u2 H16) b t6 t3 (H3 
(CHead c2 (Bind b) u2) (wcpr0_comp c c2 H4 u u2 H16 (Bind b)) t6 H17)) 
(pc3_pr2_x c2 (THead (Bind b) u2 t3) (THead (Bind b) u t3) (pr2_head_1 c2 u 
u2 (pr2_free c2 u u2 H16) (Bind b) t3))))) (ty3_correct g (CHead c2 (Bind b) 
u2) t6 t3 (H3 (CHead c2 (Bind b) u2) (wcpr0_comp c c2 H4 u u2 H16 (Bind b)) 
t6 H17))))) (ty3_correct g (CHead c2 (Bind b) u) t2 t3 (H3 (CHead c2 (Bind b) 
u) (wcpr0_comp c c2 H4 u u (pr0_refl u) (Bind b)) t2 (pr0_refl t2)))))) t4 
H15)) t5 (sym_eq T t5 t2 H14))) u1 (sym_eq T u1 u H13))) k (sym_eq K k (Bind 
b) H12))) H11)) H10)) H9 H6 H7))) | (pr0_beta u0 v1 v2 H6 t5 t6 H7) 
\Rightarrow (\lambda (H8: (eq T (THead (Flat Appl) v1 (THead (Bind Abst) u0 
t5)) (THead (Bind b) u t2))).(\lambda (H9: (eq T (THead (Bind Abbr) v2 t6) 
t4)).((let H10 \def (eq_ind T (THead (Flat Appl) v1 (THead (Bind Abst) u0 
t5)) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind b) u t2) 
H8) in (False_ind ((eq T (THead (Bind Abbr) v2 t6) t4) \to ((pr0 v1 v2) \to 
((pr0 t5 t6) \to (ty3 g c2 t4 (THead (Bind b) u t3))))) H10)) H9 H6 H7))) | 
(pr0_upsilon b0 H6 v1 v2 H7 u1 u2 H8 t5 t6 H9) \Rightarrow (\lambda (H10: (eq 
T (THead (Flat Appl) v1 (THead (Bind b0) u1 t5)) (THead (Bind b) u 
t2))).(\lambda (H11: (eq T (THead (Bind b0) u2 (THead (Flat Appl) (lift (S O) 
O v2) t6)) t4)).((let H12 \def (eq_ind T (THead (Flat Appl) v1 (THead (Bind 
b0) u1 t5)) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat _) \Rightarrow True])])) I (THead (Bind b) u t2) 
H10) in (False_ind ((eq T (THead (Bind b0) u2 (THead (Flat Appl) (lift (S O) 
O v2) t6)) t4) \to ((not (eq B b0 Abst)) \to ((pr0 v1 v2) \to ((pr0 u1 u2) 
\to ((pr0 t5 t6) \to (ty3 g c2 t4 (THead (Bind b) u t3))))))) H12)) H11 H6 H7 
H8 H9))) | (pr0_delta u1 u2 H6 t5 t6 H7 w H8) \Rightarrow (\lambda (H9: (eq T 
(THead (Bind Abbr) u1 t5) (THead (Bind b) u t2))).(\lambda (H10: (eq T (THead 
(Bind Abbr) u2 w) t4)).((let H11 \def (f_equal T T (\lambda (e: T).(match e 
in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t5 | (TLRef _) 
\Rightarrow t5 | (THead _ _ t7) \Rightarrow t7])) (THead (Bind Abbr) u1 t5) 
(THead (Bind b) u t2) H9) in ((let H12 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u1 | 
(TLRef _) \Rightarrow u1 | (THead _ t7 _) \Rightarrow t7])) (THead (Bind 
Abbr) u1 t5) (THead (Bind b) u t2) H9) in ((let H13 \def (f_equal T B 
(\lambda (e: T).(match e in T return (\lambda (_: T).B) with [(TSort _) 
\Rightarrow Abbr | (TLRef _) \Rightarrow Abbr | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | 
(Flat _) \Rightarrow Abbr])])) (THead (Bind Abbr) u1 t5) (THead (Bind b) u 
t2) H9) in (eq_ind B Abbr (\lambda (b0: B).((eq T u1 u) \to ((eq T t5 t2) \to 
((eq T (THead (Bind Abbr) u2 w) t4) \to ((pr0 u1 u2) \to ((pr0 t5 t6) \to 
((subst0 O u2 t6 w) \to (ty3 g c2 t4 (THead (Bind b0) u t3))))))))) (\lambda 
(H14: (eq T u1 u)).(eq_ind T u (\lambda (t7: T).((eq T t5 t2) \to ((eq T 
(THead (Bind Abbr) u2 w) t4) \to ((pr0 t7 u2) \to ((pr0 t5 t6) \to ((subst0 O 
u2 t6 w) \to (ty3 g c2 t4 (THead (Bind Abbr) u t3)))))))) (\lambda (H15: (eq 
T t5 t2)).(eq_ind T t2 (\lambda (t7: T).((eq T (THead (Bind Abbr) u2 w) t4) 
\to ((pr0 u u2) \to ((pr0 t7 t6) \to ((subst0 O u2 t6 w) \to (ty3 g c2 t4 
(THead (Bind Abbr) u t3))))))) (\lambda (H16: (eq T (THead (Bind Abbr) u2 w) 
t4)).(eq_ind T (THead (Bind Abbr) u2 w) (\lambda (t7: T).((pr0 u u2) \to 
((pr0 t2 t6) \to ((subst0 O u2 t6 w) \to (ty3 g c2 t7 (THead (Bind Abbr) u 
t3)))))) (\lambda (H17: (pr0 u u2)).(\lambda (H18: (pr0 t2 t6)).(\lambda 
(H19: (subst0 O u2 t6 w)).(let H20 \def (eq_ind_r B b (\lambda (b0: 
B).(\forall (c3: C).((wcpr0 (CHead c (Bind b0) u) c3) \to (\forall (t7: 
T).((pr0 t2 t7) \to (ty3 g c3 t7 t3)))))) H3 Abbr H13) in (let H21 \def 
(eq_ind_r B b (\lambda (b0: B).(ty3 g (CHead c (Bind b0) u) t2 t3)) H2 Abbr 
H13) in (ex_ind T (\lambda (t7: T).(ty3 g (CHead c2 (Bind Abbr) u) t3 t7)) 
(ty3 g c2 (THead (Bind Abbr) u2 w) (THead (Bind Abbr) u t3)) (\lambda (x: 
T).(\lambda (H22: (ty3 g (CHead c2 (Bind Abbr) u) t3 x)).(ex_ind T (\lambda 
(t7: T).(ty3 g (CHead c2 (Bind Abbr) u2) t3 t7)) (ty3 g c2 (THead (Bind Abbr) 
u2 w) (THead (Bind Abbr) u t3)) (\lambda (x0: T).(\lambda (_: (ty3 g (CHead 
c2 (Bind Abbr) u2) t3 x0)).(ty3_conv g c2 (THead (Bind Abbr) u t3) (THead 
(Bind Abbr) u x) (ty3_bind g c2 u t0 (H1 c2 H4 u (pr0_refl u)) Abbr t3 x H22) 
(THead (Bind Abbr) u2 w) (THead (Bind Abbr) u2 t3) (ty3_bind g c2 u2 t0 (H1 
c2 H4 u2 H17) Abbr w t3 (ty3_subst0 g (CHead c2 (Bind Abbr) u2) t6 t3 (H20 
(CHead c2 (Bind Abbr) u2) (wcpr0_comp c c2 H4 u u2 H17 (Bind Abbr)) t6 H18) 
c2 u2 O (getl_refl Abbr c2 u2) w H19)) (pc3_pr2_x c2 (THead (Bind Abbr) u2 
t3) (THead (Bind Abbr) u t3) (pr2_head_1 c2 u u2 (pr2_free c2 u u2 H17) (Bind 
Abbr) t3))))) (ty3_correct g (CHead c2 (Bind Abbr) u2) t6 t3 (H20 (CHead c2 
(Bind Abbr) u2) (wcpr0_comp c c2 H4 u u2 H17 (Bind Abbr)) t6 H18))))) 
(ty3_correct g (CHead c2 (Bind Abbr) u) t2 t3 (H20 (CHead c2 (Bind Abbr) u) 
(wcpr0_comp c c2 H4 u u (pr0_refl u) (Bind Abbr)) t2 (pr0_refl t2))))))))) t4 
H16)) t5 (sym_eq T t5 t2 H15))) u1 (sym_eq T u1 u H14))) b H13)) H12)) H11)) 
H10 H6 H7 H8))) | (pr0_zeta b0 H6 t5 t6 H7 u0) \Rightarrow (\lambda (H8: (eq 
T (THead (Bind b0) u0 (lift (S O) O t5)) (THead (Bind b) u t2))).(\lambda 
(H9: (eq T t6 t4)).((let H10 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow ((let rec lref_map (f: 
((nat \to nat))) (d: nat) (t7: T) on t7: T \def (match t7 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k u1 t8) 
\Rightarrow (THead k (lref_map f d u1) (lref_map f (s k d) t8))]) in 
lref_map) (\lambda (x: nat).(plus x (S O))) O t5) | (TLRef _) \Rightarrow 
((let rec lref_map (f: ((nat \to nat))) (d: nat) (t7: T) on t7: T \def (match 
t7 with [(TSort n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef 
(match (blt i d) with [true \Rightarrow i | false \Rightarrow (f i)])) | 
(THead k u1 t8) \Rightarrow (THead k (lref_map f d u1) (lref_map f (s k d) 
t8))]) in lref_map) (\lambda (x: nat).(plus x (S O))) O t5) | (THead _ _ t7) 
\Rightarrow t7])) (THead (Bind b0) u0 (lift (S O) O t5)) (THead (Bind b) u 
t2) H8) in ((let H11 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow u0 | (TLRef _) \Rightarrow u0 
| (THead _ t7 _) \Rightarrow t7])) (THead (Bind b0) u0 (lift (S O) O t5)) 
(THead (Bind b) u t2) H8) in ((let H12 \def (f_equal T B (\lambda (e: 
T).(match e in T return (\lambda (_: T).B) with [(TSort _) \Rightarrow b0 | 
(TLRef _) \Rightarrow b0 | (THead k _ _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow 
b0])])) (THead (Bind b0) u0 (lift (S O) O t5)) (THead (Bind b) u t2) H8) in 
(eq_ind B b (\lambda (b1: B).((eq T u0 u) \to ((eq T (lift (S O) O t5) t2) 
\to ((eq T t6 t4) \to ((not (eq B b1 Abst)) \to ((pr0 t5 t6) \to (ty3 g c2 t4 
(THead (Bind b) u t3)))))))) (\lambda (H13: (eq T u0 u)).(eq_ind T u (\lambda 
(_: T).((eq T (lift (S O) O t5) t2) \to ((eq T t6 t4) \to ((not (eq B b 
Abst)) \to ((pr0 t5 t6) \to (ty3 g c2 t4 (THead (Bind b) u t3))))))) (\lambda 
(H14: (eq T (lift (S O) O t5) t2)).(eq_ind T (lift (S O) O t5) (\lambda (_: 
T).((eq T t6 t4) \to ((not (eq B b Abst)) \to ((pr0 t5 t6) \to (ty3 g c2 t4 
(THead (Bind b) u t3)))))) (\lambda (H15: (eq T t6 t4)).(eq_ind T t4 (\lambda 
(t7: T).((not (eq B b Abst)) \to ((pr0 t5 t7) \to (ty3 g c2 t4 (THead (Bind 
b) u t3))))) (\lambda (H16: (not (eq B b Abst))).(\lambda (H17: (pr0 t5 
t4)).(let H18 \def (eq_ind_r T t2 (\lambda (t7: T).(\forall (c3: C).((wcpr0 
(CHead c (Bind b) u) c3) \to (\forall (t8: T).((pr0 t7 t8) \to (ty3 g c3 t8 
t3)))))) H3 (lift (S O) O t5) H14) in (let H19 \def (eq_ind_r T t2 (\lambda 
(t7: T).(ty3 g (CHead c (Bind b) u) t7 t3)) H2 (lift (S O) O t5) H14) in 
(ex_ind T (\lambda (t7: T).(ty3 g (CHead c2 (Bind b) u) t3 t7)) (ty3 g c2 t4 
(THead (Bind b) u t3)) (\lambda (x: T).(\lambda (H20: (ty3 g (CHead c2 (Bind 
b) u) t3 x)).(B_ind (\lambda (b1: B).((not (eq B b1 Abst)) \to ((ty3 g (CHead 
c2 (Bind b1) u) t3 x) \to ((ty3 g (CHead c2 (Bind b1) u) (lift (S O) O t4) 
t3) \to (ty3 g c2 t4 (THead (Bind b1) u t3)))))) (\lambda (H21: (not (eq B 
Abbr Abst))).(\lambda (H22: (ty3 g (CHead c2 (Bind Abbr) u) t3 x)).(\lambda 
(H23: (ty3 g (CHead c2 (Bind Abbr) u) (lift (S O) O t4) t3)).(let H24 \def 
(ty3_gen_cabbr g (CHead c2 (Bind Abbr) u) (lift (S O) O t4) t3 H23 c2 u O 
(getl_refl Abbr c2 u) (CHead c2 (Bind Abbr) u) (csubst1_refl O u (CHead c2 
(Bind Abbr) u)) c2 (drop_drop (Bind Abbr) O c2 c2 (drop_refl c2) u)) in 
(ex3_2_ind T T (\lambda (y1: T).(\lambda (_: T).(subst1 O u (lift (S O) O t4) 
(lift (S O) O y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 O u t3 (lift (S 
O) O y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g c2 y1 y2))) (ty3 g c2 t4 
(THead (Bind Abbr) u t3)) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H25: 
(subst1 O u (lift (S O) O t4) (lift (S O) O x0))).(\lambda (H26: (subst1 O u 
t3 (lift (S O) O x1))).(\lambda (H27: (ty3 g c2 x0 x1)).(let H28 \def (eq_ind 
T x0 (\lambda (t7: T).(ty3 g c2 t7 x1)) H27 t4 (lift_inj x0 t4 (S O) O 
(subst1_gen_lift_eq t4 u (lift (S O) O x0) (S O) O O (le_n O) (eq_ind_r nat 
(plus (S O) O) (\lambda (n: nat).(lt O n)) (le_n (plus (S O) O)) (plus O (S 
O)) (plus_sym O (S O))) H25))) in (ty3_conv g c2 (THead (Bind Abbr) u t3) 
(THead (Bind Abbr) u x) (ty3_bind g c2 u t0 (H1 c2 H4 u (pr0_refl u)) Abbr t3 
x H22) t4 x1 H28 (pc3_pr3_x c2 x1 (THead (Bind Abbr) u t3) (pr3_t (THead 
(Bind Abbr) u (lift (S O) O x1)) (THead (Bind Abbr) u t3) c2 (pr3_pr2 c2 
(THead (Bind Abbr) u t3) (THead (Bind Abbr) u (lift (S O) O x1)) (pr2_free c2 
(THead (Bind Abbr) u t3) (THead (Bind Abbr) u (lift (S O) O x1)) (pr0_delta1 
u u (pr0_refl u) t3 t3 (pr0_refl t3) (lift (S O) O x1) H26))) x1 (pr3_pr2 c2 
(THead (Bind Abbr) u (lift (S O) O x1)) x1 (pr2_free c2 (THead (Bind Abbr) u 
(lift (S O) O x1)) x1 (pr0_zeta Abbr H21 x1 x1 (pr0_refl x1) u)))))))))))) 
H24))))) (\lambda (H21: (not (eq B Abst Abst))).(\lambda (_: (ty3 g (CHead c2 
(Bind Abst) u) t3 x)).(\lambda (_: (ty3 g (CHead c2 (Bind Abst) u) (lift (S 
O) O t4) t3)).(let H24 \def (match (H21 (refl_equal B Abst)) in False return 
(\lambda (_: False).(ty3 g c2 t4 (THead (Bind Abst) u t3))) with []) in 
H24)))) (\lambda (H21: (not (eq B Void Abst))).(\lambda (H22: (ty3 g (CHead 
c2 (Bind Void) u) t3 x)).(\lambda (H23: (ty3 g (CHead c2 (Bind Void) u) (lift 
(S O) O t4) t3)).(let H24 \def (ty3_gen_cvoid g (CHead c2 (Bind Void) u) 
(lift (S O) O t4) t3 H23 c2 u O (getl_refl Void c2 u) c2 (drop_drop (Bind 
Void) O c2 c2 (drop_refl c2) u)) in (ex3_2_ind T T (\lambda (y1: T).(\lambda 
(_: T).(eq T (lift (S O) O t4) (lift (S O) O y1)))) (\lambda (_: T).(\lambda 
(y2: T).(eq T t3 (lift (S O) O y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 
g c2 y1 y2))) (ty3 g c2 t4 (THead (Bind Void) u t3)) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H25: (eq T (lift (S O) O t4) (lift (S O) O 
x0))).(\lambda (H26: (eq T t3 (lift (S O) O x1))).(\lambda (H27: (ty3 g c2 x0 
x1)).(let H28 \def (eq_ind T t3 (\lambda (t7: T).(ty3 g (CHead c2 (Bind Void) 
u) t7 x)) H22 (lift (S O) O x1) H26) in (eq_ind_r T (lift (S O) O x1) 
(\lambda (t7: T).(ty3 g c2 t4 (THead (Bind Void) u t7))) (let H29 \def 
(eq_ind_r T x0 (\lambda (t7: T).(ty3 g c2 t7 x1)) H27 t4 (lift_inj t4 x0 (S 
O) O H25)) in (ty3_conv g c2 (THead (Bind Void) u (lift (S O) O x1)) (THead 
(Bind Void) u x) (ty3_bind g c2 u t0 (H1 c2 H4 u (pr0_refl u)) Void (lift (S 
O) O x1) x H28) t4 x1 H29 (pc3_s c2 x1 (THead (Bind Void) u (lift (S O) O 
x1)) (pc3_pr2_r c2 (THead (Bind Void) u (lift (S O) O x1)) x1 (pr2_free c2 
(THead (Bind Void) u (lift (S O) O x1)) x1 (pr0_zeta Void H21 x1 x1 (pr0_refl 
x1) u)))))) t3 H26))))))) H24))))) b H16 H20 (H18 (CHead c2 (Bind b) u) 
(wcpr0_comp c c2 H4 u u (pr0_refl u) (Bind b)) (lift (S O) O t4) (pr0_lift t5 
t4 H17 (S O) O))))) (ty3_correct g (CHead c2 (Bind b) u) (lift (S O) O t4) t3 
(H18 (CHead c2 (Bind b) u) (wcpr0_comp c c2 H4 u u (pr0_refl u) (Bind b)) 
(lift (S O) O t4) (pr0_lift t5 t4 H17 (S O) O)))))))) t6 (sym_eq T t6 t4 
H15))) t2 H14)) u0 (sym_eq T u0 u H13))) b0 (sym_eq B b0 b H12))) H11)) H10)) 
H9 H6 H7))) | (pr0_tau t5 t6 H6 u0) \Rightarrow (\lambda (H7: (eq T (THead 
(Flat Cast) u0 t5) (THead (Bind b) u t2))).(\lambda (H8: (eq T t6 t4)).((let 
H9 \def (eq_ind T (THead (Flat Cast) u0 t5) (\lambda (e: T).(match e in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow 
True])])) I (THead (Bind b) u t2) H7) in (False_ind ((eq T t6 t4) \to ((pr0 
t5 t6) \to (ty3 g c2 t4 (THead (Bind b) u t3)))) H9)) H8 H6)))]) in (H6 
(refl_equal T (THead (Bind b) u t2)) (refl_equal T t4))))))))))))))))) 
(\lambda (c: C).(\lambda (w: T).(\lambda (u: T).(\lambda (_: (ty3 g c w 
u)).(\lambda (H1: ((\forall (c2: C).((wcpr0 c c2) \to (\forall (t2: T).((pr0 
w t2) \to (ty3 g c2 t2 u))))))).(\lambda (v: T).(\lambda (t0: T).(\lambda 
(H2: (ty3 g c v (THead (Bind Abst) u t0))).(\lambda (H3: ((\forall (c2: 
C).((wcpr0 c c2) \to (\forall (t2: T).((pr0 v t2) \to (ty3 g c2 t2 (THead 
(Bind Abst) u t0)))))))).(\lambda (c2: C).(\lambda (H4: (wcpr0 c 
c2)).(\lambda (t2: T).(\lambda (H5: (pr0 (THead (Flat Appl) w v) t2)).(let H6 
\def (match H5 in pr0 return (\lambda (t3: T).(\lambda (t4: T).(\lambda (_: 
(pr0 t3 t4)).((eq T t3 (THead (Flat Appl) w v)) \to ((eq T t4 t2) \to (ty3 g 
c2 t2 (THead (Flat Appl) w (THead (Bind Abst) u t0)))))))) with [(pr0_refl 
t3) \Rightarrow (\lambda (H6: (eq T t3 (THead (Flat Appl) w v))).(\lambda 
(H7: (eq T t3 t2)).(eq_ind T (THead (Flat Appl) w v) (\lambda (t4: T).((eq T 
t4 t2) \to (ty3 g c2 t2 (THead (Flat Appl) w (THead (Bind Abst) u t0))))) 
(\lambda (H8: (eq T (THead (Flat Appl) w v) t2)).(eq_ind T (THead (Flat Appl) 
w v) (\lambda (t4: T).(ty3 g c2 t4 (THead (Flat Appl) w (THead (Bind Abst) u 
t0)))) (ty3_appl g c2 w u (H1 c2 H4 w (pr0_refl w)) v t0 (H3 c2 H4 v 
(pr0_refl v))) t2 H8)) t3 (sym_eq T t3 (THead (Flat Appl) w v) H6) H7))) | 
(pr0_comp u1 u2 H6 t3 t4 H7 k) \Rightarrow (\lambda (H8: (eq T (THead k u1 
t3) (THead (Flat Appl) w v))).(\lambda (H9: (eq T (THead k u2 t4) t2)).((let 
H10 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t3 | (TLRef _) \Rightarrow t3 | (THead _ _ t5) 
\Rightarrow t5])) (THead k u1 t3) (THead (Flat Appl) w v) H8) in ((let H11 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow u1 | (TLRef _) \Rightarrow u1 | (THead _ t5 _) 
\Rightarrow t5])) (THead k u1 t3) (THead (Flat Appl) w v) H8) in ((let H12 
\def (f_equal T K (\lambda (e: T).(match e in T return (\lambda (_: T).K) 
with [(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | (THead k0 _ _) 
\Rightarrow k0])) (THead k u1 t3) (THead (Flat Appl) w v) H8) in (eq_ind K 
(Flat Appl) (\lambda (k0: K).((eq T u1 w) \to ((eq T t3 v) \to ((eq T (THead 
k0 u2 t4) t2) \to ((pr0 u1 u2) \to ((pr0 t3 t4) \to (ty3 g c2 t2 (THead (Flat 
Appl) w (THead (Bind Abst) u t0))))))))) (\lambda (H13: (eq T u1 w)).(eq_ind 
T w (\lambda (t5: T).((eq T t3 v) \to ((eq T (THead (Flat Appl) u2 t4) t2) 
\to ((pr0 t5 u2) \to ((pr0 t3 t4) \to (ty3 g c2 t2 (THead (Flat Appl) w 
(THead (Bind Abst) u t0)))))))) (\lambda (H14: (eq T t3 v)).(eq_ind T v 
(\lambda (t5: T).((eq T (THead (Flat Appl) u2 t4) t2) \to ((pr0 w u2) \to 
((pr0 t5 t4) \to (ty3 g c2 t2 (THead (Flat Appl) w (THead (Bind Abst) u 
t0))))))) (\lambda (H15: (eq T (THead (Flat Appl) u2 t4) t2)).(eq_ind T 
(THead (Flat Appl) u2 t4) (\lambda (t5: T).((pr0 w u2) \to ((pr0 v t4) \to 
(ty3 g c2 t5 (THead (Flat Appl) w (THead (Bind Abst) u t0)))))) (\lambda 
(H16: (pr0 w u2)).(\lambda (H17: (pr0 v t4)).(ex_ind T (\lambda (t5: T).(ty3 
g c2 (THead (Bind Abst) u t0) t5)) (ty3 g c2 (THead (Flat Appl) u2 t4) (THead 
(Flat Appl) w (THead (Bind Abst) u t0))) (\lambda (x: T).(\lambda (H18: (ty3 
g c2 (THead (Bind Abst) u t0) x)).(ex3_2_ind T T (\lambda (t5: T).(\lambda 
(_: T).(pc3 c2 (THead (Bind Abst) u t5) x))) (\lambda (_: T).(\lambda (t6: 
T).(ty3 g c2 u t6))) (\lambda (t5: T).(\lambda (_: T).(ty3 g (CHead c2 (Bind 
Abst) u) t0 t5))) (ty3 g c2 (THead (Flat Appl) u2 t4) (THead (Flat Appl) w 
(THead (Bind Abst) u t0))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (_: 
(pc3 c2 (THead (Bind Abst) u x0) x)).(\lambda (H20: (ty3 g c2 u x1)).(\lambda 
(H21: (ty3 g (CHead c2 (Bind Abst) u) t0 x0)).(ty3_conv g c2 (THead (Flat 
Appl) w (THead (Bind Abst) u t0)) (THead (Flat Appl) w (THead (Bind Abst) u 
x0)) (ty3_appl g c2 w u (H1 c2 H4 w (pr0_refl w)) (THead (Bind Abst) u t0) x0 
(ty3_bind g c2 u x1 H20 Abst t0 x0 H21)) (THead (Flat Appl) u2 t4) (THead 
(Flat Appl) u2 (THead (Bind Abst) u t0)) (ty3_appl g c2 u2 u (H1 c2 H4 u2 
H16) t4 t0 (H3 c2 H4 t4 H17)) (pc3_pr2_x c2 (THead (Flat Appl) u2 (THead 
(Bind Abst) u t0)) (THead (Flat Appl) w (THead (Bind Abst) u t0)) (pr2_head_1 
c2 w u2 (pr2_free c2 w u2 H16) (Flat Appl) (THead (Bind Abst) u t0))))))))) 
(ty3_gen_bind g Abst c2 u t0 x H18)))) (ty3_correct g c2 v (THead (Bind Abst) 
u t0) (H3 c2 H4 v (pr0_refl v)))))) t2 H15)) t3 (sym_eq T t3 v H14))) u1 
(sym_eq T u1 w H13))) k (sym_eq K k (Flat Appl) H12))) H11)) H10)) H9 H6 
H7))) | (pr0_beta u0 v1 v2 H6 t3 t4 H7) \Rightarrow (\lambda (H8: (eq T 
(THead (Flat Appl) v1 (THead (Bind Abst) u0 t3)) (THead (Flat Appl) w 
v))).(\lambda (H9: (eq T (THead (Bind Abbr) v2 t4) t2)).((let H10 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow (THead (Bind Abst) u0 t3) | (TLRef _) \Rightarrow 
(THead (Bind Abst) u0 t3) | (THead _ _ t5) \Rightarrow t5])) (THead (Flat 
Appl) v1 (THead (Bind Abst) u0 t3)) (THead (Flat Appl) w v) H8) in ((let H11 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow v1 | (TLRef _) \Rightarrow v1 | (THead _ t5 _) 
\Rightarrow t5])) (THead (Flat Appl) v1 (THead (Bind Abst) u0 t3)) (THead 
(Flat Appl) w v) H8) in (eq_ind T w (\lambda (t5: T).((eq T (THead (Bind 
Abst) u0 t3) v) \to ((eq T (THead (Bind Abbr) v2 t4) t2) \to ((pr0 t5 v2) \to 
((pr0 t3 t4) \to (ty3 g c2 t2 (THead (Flat Appl) w (THead (Bind Abst) u 
t0)))))))) (\lambda (H12: (eq T (THead (Bind Abst) u0 t3) v)).(eq_ind T 
(THead (Bind Abst) u0 t3) (\lambda (_: T).((eq T (THead (Bind Abbr) v2 t4) 
t2) \to ((pr0 w v2) \to ((pr0 t3 t4) \to (ty3 g c2 t2 (THead (Flat Appl) w 
(THead (Bind Abst) u t0))))))) (\lambda (H13: (eq T (THead (Bind Abbr) v2 t4) 
t2)).(eq_ind T (THead (Bind Abbr) v2 t4) (\lambda (t5: T).((pr0 w v2) \to 
((pr0 t3 t4) \to (ty3 g c2 t5 (THead (Flat Appl) w (THead (Bind Abst) u 
t0)))))) (\lambda (H14: (pr0 w v2)).(\lambda (H15: (pr0 t3 t4)).(let H16 \def 
(eq_ind_r T v (\lambda (t5: T).(\forall (c3: C).((wcpr0 c c3) \to (\forall 
(t6: T).((pr0 t5 t6) \to (ty3 g c3 t6 (THead (Bind Abst) u t0))))))) H3 
(THead (Bind Abst) u0 t3) H12) in (let H17 \def (eq_ind_r T v (\lambda (t5: 
T).(ty3 g c t5 (THead (Bind Abst) u t0))) H2 (THead (Bind Abst) u0 t3) H12) 
in (ex_ind T (\lambda (t5: T).(ty3 g c2 (THead (Bind Abst) u t0) t5)) (ty3 g 
c2 (THead (Bind Abbr) v2 t4) (THead (Flat Appl) w (THead (Bind Abst) u t0))) 
(\lambda (x: T).(\lambda (H18: (ty3 g c2 (THead (Bind Abst) u t0) 
x)).(ex3_2_ind T T (\lambda (t5: T).(\lambda (_: T).(pc3 c2 (THead (Bind 
Abst) u t5) x))) (\lambda (_: T).(\lambda (t6: T).(ty3 g c2 u t6))) (\lambda 
(t5: T).(\lambda (_: T).(ty3 g (CHead c2 (Bind Abst) u) t0 t5))) (ty3 g c2 
(THead (Bind Abbr) v2 t4) (THead (Flat Appl) w (THead (Bind Abst) u t0))) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (_: (pc3 c2 (THead (Bind Abst) u 
x0) x)).(\lambda (H20: (ty3 g c2 u x1)).(\lambda (H21: (ty3 g (CHead c2 (Bind 
Abst) u) t0 x0)).(ex3_2_ind T T (\lambda (t5: T).(\lambda (_: T).(pc3 c2 
(THead (Bind Abst) u0 t5) (THead (Bind Abst) u t0)))) (\lambda (_: 
T).(\lambda (t6: T).(ty3 g c2 u0 t6))) (\lambda (t5: T).(\lambda (_: T).(ty3 
g (CHead c2 (Bind Abst) u0) t4 t5))) (ty3 g c2 (THead (Bind Abbr) v2 t4) 
(THead (Flat Appl) w (THead (Bind Abst) u t0))) (\lambda (x2: T).(\lambda 
(x3: T).(\lambda (H22: (pc3 c2 (THead (Bind Abst) u0 x2) (THead (Bind Abst) u 
t0))).(\lambda (H23: (ty3 g c2 u0 x3)).(\lambda (H24: (ty3 g (CHead c2 (Bind 
Abst) u0) t4 x2)).(land_ind (pc3 c2 u0 u) (\forall (b: B).(\forall (u1: 
T).(pc3 (CHead c2 (Bind b) u1) x2 t0))) (ty3 g c2 (THead (Bind Abbr) v2 t4) 
(THead (Flat Appl) w (THead (Bind Abst) u t0))) (\lambda (H25: (pc3 c2 u0 
u)).(\lambda (H26: ((\forall (b: B).(\forall (u1: T).(pc3 (CHead c2 (Bind b) 
u1) x2 t0))))).(ty3_conv g c2 (THead (Flat Appl) w (THead (Bind Abst) u t0)) 
(THead (Flat Appl) w (THead (Bind Abst) u x0)) (ty3_appl g c2 w u (H1 c2 H4 w 
(pr0_refl w)) (THead (Bind Abst) u t0) x0 (ty3_bind g c2 u x1 H20 Abst t0 x0 
H21)) (THead (Bind Abbr) v2 t4) (THead (Bind Abbr) v2 x2) (ty3_bind g c2 v2 u 
(H1 c2 H4 v2 H14) Abbr t4 x2 (csubt_ty3_ld g c2 v2 u0 (ty3_conv g c2 u0 x3 
H23 v2 u (H1 c2 H4 v2 H14) (pc3_s c2 u u0 H25)) t4 x2 H24)) (pc3_t (THead 
(Bind Abbr) v2 t0) c2 (THead (Bind Abbr) v2 x2) (pc3_head_2 c2 v2 x2 t0 (Bind 
Abbr) (H26 Abbr v2)) (THead (Flat Appl) w (THead (Bind Abst) u t0)) 
(pc3_pr2_x c2 (THead (Bind Abbr) v2 t0) (THead (Flat Appl) w (THead (Bind 
Abst) u t0)) (pr2_free c2 (THead (Flat Appl) w (THead (Bind Abst) u t0)) 
(THead (Bind Abbr) v2 t0) (pr0_beta u w v2 H14 t0 t0 (pr0_refl t0)))))))) 
(pc3_gen_abst c2 u0 u x2 t0 H22))))))) (ty3_gen_bind g Abst c2 u0 t4 (THead 
(Bind Abst) u t0) (H16 c2 H4 (THead (Bind Abst) u0 t4) (pr0_comp u0 u0 
(pr0_refl u0) t3 t4 H15 (Bind Abst)))))))))) (ty3_gen_bind g Abst c2 u t0 x 
H18)))) (ty3_correct g c2 (THead (Bind Abst) u0 t3) (THead (Bind Abst) u t0) 
(H16 c2 H4 (THead (Bind Abst) u0 t3) (pr0_refl (THead (Bind Abst) u0 
t3))))))))) t2 H13)) v H12)) v1 (sym_eq T v1 w H11))) H10)) H9 H6 H7))) | 
(pr0_upsilon b H6 v1 v2 H7 u1 u2 H8 t3 t4 H9) \Rightarrow (\lambda (H10: (eq 
T (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) (THead (Flat Appl) w 
v))).(\lambda (H11: (eq T (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O 
v2) t4)) t2)).((let H12 \def (f_equal T T (\lambda (e: T).(match e in T 
return (\lambda (_: T).T) with [(TSort _) \Rightarrow (THead (Bind b) u1 t3) 
| (TLRef _) \Rightarrow (THead (Bind b) u1 t3) | (THead _ _ t5) \Rightarrow 
t5])) (THead (Flat Appl) v1 (THead (Bind b) u1 t3)) (THead (Flat Appl) w v) 
H10) in ((let H13 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow v1 | (TLRef _) \Rightarrow v1 
| (THead _ t5 _) \Rightarrow t5])) (THead (Flat Appl) v1 (THead (Bind b) u1 
t3)) (THead (Flat Appl) w v) H10) in (eq_ind T w (\lambda (t5: T).((eq T 
(THead (Bind b) u1 t3) v) \to ((eq T (THead (Bind b) u2 (THead (Flat Appl) 
(lift (S O) O v2) t4)) t2) \to ((not (eq B b Abst)) \to ((pr0 t5 v2) \to 
((pr0 u1 u2) \to ((pr0 t3 t4) \to (ty3 g c2 t2 (THead (Flat Appl) w (THead 
(Bind Abst) u t0)))))))))) (\lambda (H14: (eq T (THead (Bind b) u1 t3) 
v)).(eq_ind T (THead (Bind b) u1 t3) (\lambda (_: T).((eq T (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t2) \to ((not (eq B b Abst)) \to 
((pr0 w v2) \to ((pr0 u1 u2) \to ((pr0 t3 t4) \to (ty3 g c2 t2 (THead (Flat 
Appl) w (THead (Bind Abst) u t0))))))))) (\lambda (H15: (eq T (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4)) t2)).(eq_ind T (THead (Bind b) 
u2 (THead (Flat Appl) (lift (S O) O v2) t4)) (\lambda (t5: T).((not (eq B b 
Abst)) \to ((pr0 w v2) \to ((pr0 u1 u2) \to ((pr0 t3 t4) \to (ty3 g c2 t5 
(THead (Flat Appl) w (THead (Bind Abst) u t0)))))))) (\lambda (H16: (not (eq 
B b Abst))).(\lambda (H17: (pr0 w v2)).(\lambda (H18: (pr0 u1 u2)).(\lambda 
(H19: (pr0 t3 t4)).(let H20 \def (eq_ind_r T v (\lambda (t5: T).(\forall (c3: 
C).((wcpr0 c c3) \to (\forall (t6: T).((pr0 t5 t6) \to (ty3 g c3 t6 (THead 
(Bind Abst) u t0))))))) H3 (THead (Bind b) u1 t3) H14) in (let H21 \def 
(eq_ind_r T v (\lambda (t5: T).(ty3 g c t5 (THead (Bind Abst) u t0))) H2 
(THead (Bind b) u1 t3) H14) in (ex_ind T (\lambda (t5: T).(ty3 g c2 (THead 
(Bind Abst) u t0) t5)) (ty3 g c2 (THead (Bind b) u2 (THead (Flat Appl) (lift 
(S O) O v2) t4)) (THead (Flat Appl) w (THead (Bind Abst) u t0))) (\lambda (x: 
T).(\lambda (H22: (ty3 g c2 (THead (Bind Abst) u t0) x)).(let H23 \def H22 in 
(ex3_2_ind T T (\lambda (t5: T).(\lambda (_: T).(pc3 c2 (THead (Bind Abst) u 
t5) x))) (\lambda (_: T).(\lambda (t6: T).(ty3 g c2 u t6))) (\lambda (t5: 
T).(\lambda (_: T).(ty3 g (CHead c2 (Bind Abst) u) t0 t5))) (ty3 g c2 (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) (THead (Flat Appl) w 
(THead (Bind Abst) u t0))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (_: 
(pc3 c2 (THead (Bind Abst) u x0) x)).(\lambda (H25: (ty3 g c2 u x1)).(\lambda 
(H26: (ty3 g (CHead c2 (Bind Abst) u) t0 x0)).(ex3_2_ind T T (\lambda (t5: 
T).(\lambda (_: T).(pc3 c2 (THead (Bind b) u2 t5) (THead (Bind Abst) u t0)))) 
(\lambda (_: T).(\lambda (t6: T).(ty3 g c2 u2 t6))) (\lambda (t5: T).(\lambda 
(_: T).(ty3 g (CHead c2 (Bind b) u2) t4 t5))) (ty3 g c2 (THead (Bind b) u2 
(THead (Flat Appl) (lift (S O) O v2) t4)) (THead (Flat Appl) w (THead (Bind 
Abst) u t0))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H27: (pc3 c2 (THead 
(Bind b) u2 x2) (THead (Bind Abst) u t0))).(\lambda (H28: (ty3 g c2 u2 
x3)).(\lambda (H29: (ty3 g (CHead c2 (Bind b) u2) t4 x2)).(let H30 \def 
(eq_ind T (lift (S O) O (THead (Bind Abst) u t0)) (\lambda (t5: T).(pc3 
(CHead c2 (Bind b) u2) x2 t5)) (pc3_gen_not_abst b H16 c2 x2 t0 u2 u H27) 
(THead (Bind Abst) (lift (S O) O u) (lift (S O) (S O) t0)) (lift_bind Abst u 
t0 (S O) O)) in (let H31 \def (eq_ind T (lift (S O) O (THead (Bind Abst) u 
t0)) (\lambda (t5: T).(ty3 g (CHead c2 (Bind b) u2) t5 (lift (S O) O x))) 
(ty3_lift g c2 (THead (Bind Abst) u t0) x H22 (CHead c2 (Bind b) u2) O (S O) 
(drop_drop (Bind b) O c2 c2 (drop_refl c2) u2)) (THead (Bind Abst) (lift (S 
O) O u) (lift (S O) (S O) t0)) (lift_bind Abst u t0 (S O) O)) in (ex3_2_ind T 
T (\lambda (t5: T).(\lambda (_: T).(pc3 (CHead c2 (Bind b) u2) (THead (Bind 
Abst) (lift (S O) O u) t5) (lift (S O) O x)))) (\lambda (_: T).(\lambda (t6: 
T).(ty3 g (CHead c2 (Bind b) u2) (lift (S O) O u) t6))) (\lambda (t5: 
T).(\lambda (_: T).(ty3 g (CHead (CHead c2 (Bind b) u2) (Bind Abst) (lift (S 
O) O u)) (lift (S O) (S O) t0) t5))) (ty3 g c2 (THead (Bind b) u2 (THead 
(Flat Appl) (lift (S O) O v2) t4)) (THead (Flat Appl) w (THead (Bind Abst) u 
t0))) (\lambda (x4: T).(\lambda (x5: T).(\lambda (_: (pc3 (CHead c2 (Bind b) 
u2) (THead (Bind Abst) (lift (S O) O u) x4) (lift (S O) O x))).(\lambda (H33: 
(ty3 g (CHead c2 (Bind b) u2) (lift (S O) O u) x5)).(\lambda (H34: (ty3 g 
(CHead (CHead c2 (Bind b) u2) (Bind Abst) (lift (S O) O u)) (lift (S O) (S O) 
t0) x4)).(ty3_conv g c2 (THead (Flat Appl) w (THead (Bind Abst) u t0)) (THead 
(Flat Appl) w (THead (Bind Abst) u x0)) (ty3_appl g c2 w u (H1 c2 H4 w 
(pr0_refl w)) (THead (Bind Abst) u t0) x0 (ty3_bind g c2 u x1 H25 Abst t0 x0 
H26)) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t4)) (THead 
(Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) (THead (Bind Abst) (lift (S 
O) O u) (lift (S O) (S O) t0)))) (ty3_bind g c2 u2 x3 H28 b (THead (Flat 
Appl) (lift (S O) O v2) t4) (THead (Flat Appl) (lift (S O) O v2) (THead (Bind 
Abst) (lift (S O) O u) (lift (S O) (S O) t0))) (ty3_appl g (CHead c2 (Bind b) 
u2) (lift (S O) O v2) (lift (S O) O u) (ty3_lift g c2 v2 u (H1 c2 H4 v2 H17) 
(CHead c2 (Bind b) u2) O (S O) (drop_drop (Bind b) O c2 c2 (drop_refl c2) 
u2)) t4 (lift (S O) (S O) t0) (ty3_conv g (CHead c2 (Bind b) u2) (THead (Bind 
Abst) (lift (S O) O u) (lift (S O) (S O) t0)) (THead (Bind Abst) (lift (S O) 
O u) x4) (ty3_bind g (CHead c2 (Bind b) u2) (lift (S O) O u) x5 H33 Abst 
(lift (S O) (S O) t0) x4 H34) t4 x2 H29 H30))) (eq_ind T (lift (S O) O (THead 
(Bind Abst) u t0)) (\lambda (t5: T).(pc3 c2 (THead (Bind b) u2 (THead (Flat 
Appl) (lift (S O) O v2) t5)) (THead (Flat Appl) w (THead (Bind Abst) u t0)))) 
(pc3_pc1 (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) (lift (S O) 
O (THead (Bind Abst) u t0)))) (THead (Flat Appl) w (THead (Bind Abst) u t0)) 
(pc1_pr0_u2 (THead (Flat Appl) v2 (THead (Bind b) u2 (lift (S O) O (THead 
(Bind Abst) u t0)))) (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) 
(lift (S O) O (THead (Bind Abst) u t0)))) (pr0_upsilon b H16 v2 v2 (pr0_refl 
v2) u2 u2 (pr0_refl u2) (lift (S O) O (THead (Bind Abst) u t0)) (lift (S O) O 
(THead (Bind Abst) u t0)) (pr0_refl (lift (S O) O (THead (Bind Abst) u t0)))) 
(THead (Flat Appl) w (THead (Bind Abst) u t0)) (pc1_head v2 w (pc1_pr0_x v2 w 
H17) (THead (Bind b) u2 (lift (S O) O (THead (Bind Abst) u t0))) (THead (Bind 
Abst) u t0) (pc1_pr0_r (THead (Bind b) u2 (lift (S O) O (THead (Bind Abst) u 
t0))) (THead (Bind Abst) u t0) (pr0_zeta b H16 (THead (Bind Abst) u t0) 
(THead (Bind Abst) u t0) (pr0_refl (THead (Bind Abst) u t0)) u2)) (Flat 
Appl))) c2) (THead (Bind Abst) (lift (S O) O u) (lift (S O) (S O) t0)) 
(lift_bind Abst u t0 (S O) O)))))))) (ty3_gen_bind g Abst (CHead c2 (Bind b) 
u2) (lift (S O) O u) (lift (S O) (S O) t0) (lift (S O) O x) H31))))))))) 
(ty3_gen_bind g b c2 u2 t4 (THead (Bind Abst) u t0) (H20 c2 H4 (THead (Bind 
b) u2 t4) (pr0_comp u1 u2 H18 t3 t4 H19 (Bind b)))))))))) (ty3_gen_bind g 
Abst c2 u t0 x H23))))) (ty3_correct g c2 (THead (Bind b) u2 t4) (THead (Bind 
Abst) u t0) (H20 c2 H4 (THead (Bind b) u2 t4) (pr0_comp u1 u2 H18 t3 t4 H19 
(Bind b))))))))))) t2 H15)) v H14)) v1 (sym_eq T v1 w H13))) H12)) H11 H6 H7 
H8 H9))) | (pr0_delta u1 u2 H6 t3 t4 H7 w0 H8) \Rightarrow (\lambda (H9: (eq 
T (THead (Bind Abbr) u1 t3) (THead (Flat Appl) w v))).(\lambda (H10: (eq T 
(THead (Bind Abbr) u2 w0) t2)).((let H11 \def (eq_ind T (THead (Bind Abbr) u1 
t3) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat Appl) w v) 
H9) in (False_ind ((eq T (THead (Bind Abbr) u2 w0) t2) \to ((pr0 u1 u2) \to 
((pr0 t3 t4) \to ((subst0 O u2 t4 w0) \to (ty3 g c2 t2 (THead (Flat Appl) w 
(THead (Bind Abst) u t0))))))) H11)) H10 H6 H7 H8))) | (pr0_zeta b H6 t3 t4 
H7 u0) \Rightarrow (\lambda (H8: (eq T (THead (Bind b) u0 (lift (S O) O t3)) 
(THead (Flat Appl) w v))).(\lambda (H9: (eq T t4 t2)).((let H10 \def (eq_ind 
T (THead (Bind b) u0 (lift (S O) O t3)) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow True | (Flat _) \Rightarrow 
False])])) I (THead (Flat Appl) w v) H8) in (False_ind ((eq T t4 t2) \to 
((not (eq B b Abst)) \to ((pr0 t3 t4) \to (ty3 g c2 t2 (THead (Flat Appl) w 
(THead (Bind Abst) u t0)))))) H10)) H9 H6 H7))) | (pr0_tau t3 t4 H6 u0) 
\Rightarrow (\lambda (H7: (eq T (THead (Flat Cast) u0 t3) (THead (Flat Appl) 
w v))).(\lambda (H8: (eq T t4 t2)).((let H9 \def (eq_ind T (THead (Flat Cast) 
u0 t3) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with 
[(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow False | (Flat f) \Rightarrow (match f in F return (\lambda (_: 
F).Prop) with [Appl \Rightarrow False | Cast \Rightarrow True])])])) I (THead 
(Flat Appl) w v) H7) in (False_ind ((eq T t4 t2) \to ((pr0 t3 t4) \to (ty3 g 
c2 t2 (THead (Flat Appl) w (THead (Bind Abst) u t0))))) H9)) H8 H6)))]) in 
(H6 (refl_equal T (THead (Flat Appl) w v)) (refl_equal T t2)))))))))))))))) 
(\lambda (c: C).(\lambda (t2: T).(\lambda (t3: T).(\lambda (_: (ty3 g c t2 
t3)).(\lambda (H1: ((\forall (c2: C).((wcpr0 c c2) \to (\forall (t4: T).((pr0 
t2 t4) \to (ty3 g c2 t4 t3))))))).(\lambda (t0: T).(\lambda (_: (ty3 g c t3 
t0)).(\lambda (H3: ((\forall (c2: C).((wcpr0 c c2) \to (\forall (t4: T).((pr0 
t3 t4) \to (ty3 g c2 t4 t0))))))).(\lambda (c2: C).(\lambda (H4: (wcpr0 c 
c2)).(\lambda (t4: T).(\lambda (H5: (pr0 (THead (Flat Cast) t3 t2) t4)).(let 
H6 \def (match H5 in pr0 return (\lambda (t5: T).(\lambda (t6: T).(\lambda 
(_: (pr0 t5 t6)).((eq T t5 (THead (Flat Cast) t3 t2)) \to ((eq T t6 t4) \to 
(ty3 g c2 t4 (THead (Flat Cast) t0 t3))))))) with [(pr0_refl t5) \Rightarrow 
(\lambda (H6: (eq T t5 (THead (Flat Cast) t3 t2))).(\lambda (H7: (eq T t5 
t4)).(eq_ind T (THead (Flat Cast) t3 t2) (\lambda (t6: T).((eq T t6 t4) \to 
(ty3 g c2 t4 (THead (Flat Cast) t0 t3)))) (\lambda (H8: (eq T (THead (Flat 
Cast) t3 t2) t4)).(eq_ind T (THead (Flat Cast) t3 t2) (\lambda (t6: T).(ty3 g 
c2 t6 (THead (Flat Cast) t0 t3))) (ty3_cast g c2 t2 t3 (H1 c2 H4 t2 (pr0_refl 
t2)) t0 (H3 c2 H4 t3 (pr0_refl t3))) t4 H8)) t5 (sym_eq T t5 (THead (Flat 
Cast) t3 t2) H6) H7))) | (pr0_comp u1 u2 H6 t5 t6 H7 k) \Rightarrow (\lambda 
(H8: (eq T (THead k u1 t5) (THead (Flat Cast) t3 t2))).(\lambda (H9: (eq T 
(THead k u2 t6) t4)).((let H10 \def (f_equal T T (\lambda (e: T).(match e in 
T return (\lambda (_: T).T) with [(TSort _) \Rightarrow t5 | (TLRef _) 
\Rightarrow t5 | (THead _ _ t7) \Rightarrow t7])) (THead k u1 t5) (THead 
(Flat Cast) t3 t2) H8) in ((let H11 \def (f_equal T T (\lambda (e: T).(match 
e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u1 | (TLRef _) 
\Rightarrow u1 | (THead _ t7 _) \Rightarrow t7])) (THead k u1 t5) (THead 
(Flat Cast) t3 t2) H8) in ((let H12 \def (f_equal T K (\lambda (e: T).(match 
e in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k0 _ _) \Rightarrow k0])) (THead k u1 t5) (THead (Flat 
Cast) t3 t2) H8) in (eq_ind K (Flat Cast) (\lambda (k0: K).((eq T u1 t3) \to 
((eq T t5 t2) \to ((eq T (THead k0 u2 t6) t4) \to ((pr0 u1 u2) \to ((pr0 t5 
t6) \to (ty3 g c2 t4 (THead (Flat Cast) t0 t3)))))))) (\lambda (H13: (eq T u1 
t3)).(eq_ind T t3 (\lambda (t7: T).((eq T t5 t2) \to ((eq T (THead (Flat 
Cast) u2 t6) t4) \to ((pr0 t7 u2) \to ((pr0 t5 t6) \to (ty3 g c2 t4 (THead 
(Flat Cast) t0 t3))))))) (\lambda (H14: (eq T t5 t2)).(eq_ind T t2 (\lambda 
(t7: T).((eq T (THead (Flat Cast) u2 t6) t4) \to ((pr0 t3 u2) \to ((pr0 t7 
t6) \to (ty3 g c2 t4 (THead (Flat Cast) t0 t3)))))) (\lambda (H15: (eq T 
(THead (Flat Cast) u2 t6) t4)).(eq_ind T (THead (Flat Cast) u2 t6) (\lambda 
(t7: T).((pr0 t3 u2) \to ((pr0 t2 t6) \to (ty3 g c2 t7 (THead (Flat Cast) t0 
t3))))) (\lambda (H16: (pr0 t3 u2)).(\lambda (H17: (pr0 t2 t6)).(ex_ind T 
(\lambda (t7: T).(ty3 g c2 t0 t7)) (ty3 g c2 (THead (Flat Cast) u2 t6) (THead 
(Flat Cast) t0 t3)) (\lambda (x: T).(\lambda (H18: (ty3 g c2 t0 x)).(ty3_conv 
g c2 (THead (Flat Cast) t0 t3) (THead (Flat Cast) x t0) (ty3_cast g c2 t3 t0 
(H3 c2 H4 t3 (pr0_refl t3)) x H18) (THead (Flat Cast) u2 t6) (THead (Flat 
Cast) t0 u2) (ty3_cast g c2 t6 u2 (ty3_conv g c2 u2 t0 (H3 c2 H4 u2 H16) t6 
t3 (H1 c2 H4 t6 H17) (pc3_pr2_r c2 t3 u2 (pr2_free c2 t3 u2 H16))) t0 (H3 c2 
H4 u2 H16)) (pc3_s c2 (THead (Flat Cast) t0 u2) (THead (Flat Cast) t0 t3) 
(pc3_pr2_r c2 (THead (Flat Cast) t0 t3) (THead (Flat Cast) t0 u2) 
(pr2_thin_dx c2 t3 u2 (pr2_free c2 t3 u2 H16) t0 Cast)))))) (ty3_correct g c2 
t3 t0 (H3 c2 H4 t3 (pr0_refl t3)))))) t4 H15)) t5 (sym_eq T t5 t2 H14))) u1 
(sym_eq T u1 t3 H13))) k (sym_eq K k (Flat Cast) H12))) H11)) H10)) H9 H6 
H7))) | (pr0_beta u v1 v2 H6 t5 t6 H7) \Rightarrow (\lambda (H8: (eq T (THead 
(Flat Appl) v1 (THead (Bind Abst) u t5)) (THead (Flat Cast) t3 t2))).(\lambda 
(H9: (eq T (THead (Bind Abbr) v2 t6) t4)).((let H10 \def (eq_ind T (THead 
(Flat Appl) v1 (THead (Bind Abst) u t5)) (\lambda (e: T).(match e in T return 
(\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead k _ _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind _) \Rightarrow False | (Flat f) \Rightarrow (match f 
in F return (\lambda (_: F).Prop) with [Appl \Rightarrow True | Cast 
\Rightarrow False])])])) I (THead (Flat Cast) t3 t2) H8) in (False_ind ((eq T 
(THead (Bind Abbr) v2 t6) t4) \to ((pr0 v1 v2) \to ((pr0 t5 t6) \to (ty3 g c2 
t4 (THead (Flat Cast) t0 t3))))) H10)) H9 H6 H7))) | (pr0_upsilon b H6 v1 v2 
H7 u1 u2 H8 t5 t6 H9) \Rightarrow (\lambda (H10: (eq T (THead (Flat Appl) v1 
(THead (Bind b) u1 t5)) (THead (Flat Cast) t3 t2))).(\lambda (H11: (eq T 
(THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) t6)) t4)).((let H12 
\def (eq_ind T (THead (Flat Appl) v1 (THead (Bind b) u1 t5)) (\lambda (e: 
T).(match e in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k in K 
return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | (Flat f) 
\Rightarrow (match f in F return (\lambda (_: F).Prop) with [Appl \Rightarrow 
True | Cast \Rightarrow False])])])) I (THead (Flat Cast) t3 t2) H10) in 
(False_ind ((eq T (THead (Bind b) u2 (THead (Flat Appl) (lift (S O) O v2) 
t6)) t4) \to ((not (eq B b Abst)) \to ((pr0 v1 v2) \to ((pr0 u1 u2) \to ((pr0 
t5 t6) \to (ty3 g c2 t4 (THead (Flat Cast) t0 t3))))))) H12)) H11 H6 H7 H8 
H9))) | (pr0_delta u1 u2 H6 t5 t6 H7 w H8) \Rightarrow (\lambda (H9: (eq T 
(THead (Bind Abbr) u1 t5) (THead (Flat Cast) t3 t2))).(\lambda (H10: (eq T 
(THead (Bind Abbr) u2 w) t4)).((let H11 \def (eq_ind T (THead (Bind Abbr) u1 
t5) (\lambda (e: T).(match e in T return (\lambda (_: T).Prop) with [(TSort 
_) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind _) 
\Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat Cast) t3 
t2) H9) in (False_ind ((eq T (THead (Bind Abbr) u2 w) t4) \to ((pr0 u1 u2) 
\to ((pr0 t5 t6) \to ((subst0 O u2 t6 w) \to (ty3 g c2 t4 (THead (Flat Cast) 
t0 t3)))))) H11)) H10 H6 H7 H8))) | (pr0_zeta b H6 t5 t6 H7 u) \Rightarrow 
(\lambda (H8: (eq T (THead (Bind b) u (lift (S O) O t5)) (THead (Flat Cast) 
t3 t2))).(\lambda (H9: (eq T t6 t4)).((let H10 \def (eq_ind T (THead (Bind b) 
u (lift (S O) O t5)) (\lambda (e: T).(match e in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead k _ _) \Rightarrow (match k in K return (\lambda (_: K).Prop) with 
[(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])])) I (THead (Flat 
Cast) t3 t2) H8) in (False_ind ((eq T t6 t4) \to ((not (eq B b Abst)) \to 
((pr0 t5 t6) \to (ty3 g c2 t4 (THead (Flat Cast) t0 t3))))) H10)) H9 H6 H7))) 
| (pr0_tau t5 t6 H6 u) \Rightarrow (\lambda (H7: (eq T (THead (Flat Cast) u 
t5) (THead (Flat Cast) t3 t2))).(\lambda (H8: (eq T t6 t4)).((let H9 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow t5 | (TLRef _) \Rightarrow t5 | (THead _ _ t7) 
\Rightarrow t7])) (THead (Flat Cast) u t5) (THead (Flat Cast) t3 t2) H7) in 
((let H10 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: 
T).T) with [(TSort _) \Rightarrow u | (TLRef _) \Rightarrow u | (THead _ t7 
_) \Rightarrow t7])) (THead (Flat Cast) u t5) (THead (Flat Cast) t3 t2) H7) 
in (eq_ind T t3 (\lambda (_: T).((eq T t5 t2) \to ((eq T t6 t4) \to ((pr0 t5 
t6) \to (ty3 g c2 t4 (THead (Flat Cast) t0 t3)))))) (\lambda (H11: (eq T t5 
t2)).(eq_ind T t2 (\lambda (t7: T).((eq T t6 t4) \to ((pr0 t7 t6) \to (ty3 g 
c2 t4 (THead (Flat Cast) t0 t3))))) (\lambda (H12: (eq T t6 t4)).(eq_ind T t4 
(\lambda (t7: T).((pr0 t2 t7) \to (ty3 g c2 t4 (THead (Flat Cast) t0 t3)))) 
(\lambda (H13: (pr0 t2 t4)).(ex_ind T (\lambda (t7: T).(ty3 g c2 t0 t7)) (ty3 
g c2 t4 (THead (Flat Cast) t0 t3)) (\lambda (x: T).(\lambda (H14: (ty3 g c2 
t0 x)).(ty3_conv g c2 (THead (Flat Cast) t0 t3) (THead (Flat Cast) x t0) 
(ty3_cast g c2 t3 t0 (H3 c2 H4 t3 (pr0_refl t3)) x H14) t4 t3 (H1 c2 H4 t4 
H13) (pc3_pr2_x c2 t3 (THead (Flat Cast) t0 t3) (pr2_free c2 (THead (Flat 
Cast) t0 t3) t3 (pr0_tau t3 t3 (pr0_refl t3) t0)))))) (ty3_correct g c2 t3 t0 
(H3 c2 H4 t3 (pr0_refl t3))))) t6 (sym_eq T t6 t4 H12))) t5 (sym_eq T t5 t2 
H11))) u (sym_eq T u t3 H10))) H9)) H8 H6)))]) in (H6 (refl_equal T (THead 
(Flat Cast) t3 t2)) (refl_equal T t4))))))))))))))) c1 t1 t H))))).
(* COMMENTS
Initial nodes: 14710
END *)

theorem ty3_sred_pr0:
 \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (g: G).(\forall 
(c: C).(\forall (t: T).((ty3 g c t1 t) \to (ty3 g c t2 t)))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr0 t1 t2)).(\lambda (g: 
G).(\lambda (c: C).(\lambda (t: T).(\lambda (H0: (ty3 g c t1 
t)).(ty3_sred_wcpr0_pr0 g c t1 t H0 c (wcpr0_refl c) t2 H))))))).
(* COMMENTS
Initial nodes: 47
END *)

theorem ty3_sred_pr1:
 \forall (t1: T).(\forall (t2: T).((pr1 t1 t2) \to (\forall (g: G).(\forall 
(c: C).(\forall (t: T).((ty3 g c t1 t) \to (ty3 g c t2 t)))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr1 t1 t2)).(pr1_ind (\lambda 
(t: T).(\lambda (t0: T).(\forall (g: G).(\forall (c: C).(\forall (t3: 
T).((ty3 g c t t3) \to (ty3 g c t0 t3))))))) (\lambda (t: T).(\lambda (g: 
G).(\lambda (c: C).(\lambda (t0: T).(\lambda (H0: (ty3 g c t t0)).H0))))) 
(\lambda (t3: T).(\lambda (t4: T).(\lambda (H0: (pr0 t4 t3)).(\lambda (t5: 
T).(\lambda (_: (pr1 t3 t5)).(\lambda (H2: ((\forall (g: G).(\forall (c: 
C).(\forall (t: T).((ty3 g c t3 t) \to (ty3 g c t5 t))))))).(\lambda (g: 
G).(\lambda (c: C).(\lambda (t: T).(\lambda (H3: (ty3 g c t4 t)).(H2 g c t 
(ty3_sred_pr0 t4 t3 H0 g c t H3)))))))))))) t1 t2 H))).
(* COMMENTS
Initial nodes: 151
END *)

theorem ty3_sred_pr2:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall 
(g: G).(\forall (t: T).((ty3 g c t1 t) \to (ty3 g c t2 t)))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr2 c t1 
t2)).(pr2_ind (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).(\forall (g: 
G).(\forall (t3: T).((ty3 g c0 t t3) \to (ty3 g c0 t0 t3))))))) (\lambda (c0: 
C).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H0: (pr0 t3 t4)).(\lambda (g: 
G).(\lambda (t: T).(\lambda (H1: (ty3 g c0 t3 t)).(ty3_sred_wcpr0_pr0 g c0 t3 
t H1 c0 (wcpr0_refl c0) t4 H0)))))))) (\lambda (c0: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind 
Abbr) u))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H1: (pr0 t3 
t4)).(\lambda (t: T).(\lambda (H2: (subst0 i u t4 t)).(\lambda (g: 
G).(\lambda (t0: T).(\lambda (H3: (ty3 g c0 t3 t0)).(ty3_subst0 g c0 t4 t0 
(ty3_sred_wcpr0_pr0 g c0 t3 t0 H3 c0 (wcpr0_refl c0) t4 H1) d u i H0 t 
H2)))))))))))))) c t1 t2 H)))).
(* COMMENTS
Initial nodes: 205
END *)

theorem ty3_sred_pr3:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (\forall 
(g: G).(\forall (t: T).((ty3 g c t1 t) \to (ty3 g c t2 t)))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr3 c t1 
t2)).(pr3_ind c (\lambda (t: T).(\lambda (t0: T).(\forall (g: G).(\forall 
(t3: T).((ty3 g c t t3) \to (ty3 g c t0 t3)))))) (\lambda (t: T).(\lambda (g: 
G).(\lambda (t0: T).(\lambda (H0: (ty3 g c t t0)).H0)))) (\lambda (t3: 
T).(\lambda (t4: T).(\lambda (H0: (pr2 c t4 t3)).(\lambda (t5: T).(\lambda 
(_: (pr3 c t3 t5)).(\lambda (H2: ((\forall (g: G).(\forall (t: T).((ty3 g c 
t3 t) \to (ty3 g c t5 t)))))).(\lambda (g: G).(\lambda (t: T).(\lambda (H3: 
(ty3 g c t4 t)).(H2 g t (ty3_sred_pr2 c t4 t3 H0 g t H3))))))))))) t1 t2 
H)))).
(* COMMENTS
Initial nodes: 151
END *)

