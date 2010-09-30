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

include "Basic-1/pr2/props.ma".

include "Basic-1/clen/getl.ma".

theorem pr2_gen_ctail:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall 
(t2: T).((pr2 (CTail k u c) t1 t2) \to (or (pr2 c t1 t2) (ex3 T (\lambda (_: 
T).(eq K k (Bind Abbr))) (\lambda (t: T).(pr0 t1 t)) (\lambda (t: T).(subst0 
(clen c) u t t2)))))))))
\def
 \lambda (k: K).(\lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda 
(t2: T).(\lambda (H: (pr2 (CTail k u c) t1 t2)).(insert_eq C (CTail k u c) 
(\lambda (c0: C).(pr2 c0 t1 t2)) (\lambda (_: C).(or (pr2 c t1 t2) (ex3 T 
(\lambda (_: T).(eq K k (Bind Abbr))) (\lambda (t: T).(pr0 t1 t)) (\lambda 
(t: T).(subst0 (clen c) u t t2))))) (\lambda (y: C).(\lambda (H0: (pr2 y t1 
t2)).(pr2_ind (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).((eq C c0 
(CTail k u c)) \to (or (pr2 c t t0) (ex3 T (\lambda (_: T).(eq K k (Bind 
Abbr))) (\lambda (t3: T).(pr0 t t3)) (\lambda (t3: T).(subst0 (clen c) u t3 
t0)))))))) (\lambda (c0: C).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H1: 
(pr0 t3 t4)).(\lambda (_: (eq C c0 (CTail k u c))).(or_introl (pr2 c t3 t4) 
(ex3 T (\lambda (_: T).(eq K k (Bind Abbr))) (\lambda (t: T).(pr0 t3 t)) 
(\lambda (t: T).(subst0 (clen c) u t t4))) (pr2_free c t3 t4 H1))))))) 
(\lambda (c0: C).(\lambda (d: C).(\lambda (u0: T).(\lambda (i: nat).(\lambda 
(H1: (getl i c0 (CHead d (Bind Abbr) u0))).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (H2: (pr0 t3 t4)).(\lambda (t: T).(\lambda (H3: (subst0 i u0 t4 
t)).(\lambda (H4: (eq C c0 (CTail k u c))).(let H5 \def (eq_ind C c0 (\lambda 
(c1: C).(getl i c1 (CHead d (Bind Abbr) u0))) H1 (CTail k u c) H4) in (let 
H_x \def (getl_gen_tail k Abbr u u0 d c i H5) in (let H6 \def H_x in (or_ind 
(ex2 C (\lambda (e: C).(eq C d (CTail k u e))) (\lambda (e: C).(getl i c 
(CHead e (Bind Abbr) u0)))) (ex4 nat (\lambda (_: nat).(eq nat i (clen c))) 
(\lambda (_: nat).(eq K k (Bind Abbr))) (\lambda (_: nat).(eq T u u0)) 
(\lambda (n: nat).(eq C d (CSort n)))) (or (pr2 c t3 t) (ex3 T (\lambda (_: 
T).(eq K k (Bind Abbr))) (\lambda (t0: T).(pr0 t3 t0)) (\lambda (t0: 
T).(subst0 (clen c) u t0 t)))) (\lambda (H7: (ex2 C (\lambda (e: C).(eq C d 
(CTail k u e))) (\lambda (e: C).(getl i c (CHead e (Bind Abbr) 
u0))))).(ex2_ind C (\lambda (e: C).(eq C d (CTail k u e))) (\lambda (e: 
C).(getl i c (CHead e (Bind Abbr) u0))) (or (pr2 c t3 t) (ex3 T (\lambda (_: 
T).(eq K k (Bind Abbr))) (\lambda (t0: T).(pr0 t3 t0)) (\lambda (t0: 
T).(subst0 (clen c) u t0 t)))) (\lambda (x: C).(\lambda (_: (eq C d (CTail k 
u x))).(\lambda (H9: (getl i c (CHead x (Bind Abbr) u0))).(or_introl (pr2 c 
t3 t) (ex3 T (\lambda (_: T).(eq K k (Bind Abbr))) (\lambda (t0: T).(pr0 t3 
t0)) (\lambda (t0: T).(subst0 (clen c) u t0 t))) (pr2_delta c x u0 i H9 t3 t4 
H2 t H3))))) H7)) (\lambda (H7: (ex4 nat (\lambda (_: nat).(eq nat i (clen 
c))) (\lambda (_: nat).(eq K k (Bind Abbr))) (\lambda (_: nat).(eq T u u0)) 
(\lambda (n: nat).(eq C d (CSort n))))).(ex4_ind nat (\lambda (_: nat).(eq 
nat i (clen c))) (\lambda (_: nat).(eq K k (Bind Abbr))) (\lambda (_: 
nat).(eq T u u0)) (\lambda (n: nat).(eq C d (CSort n))) (or (pr2 c t3 t) (ex3 
T (\lambda (_: T).(eq K k (Bind Abbr))) (\lambda (t0: T).(pr0 t3 t0)) 
(\lambda (t0: T).(subst0 (clen c) u t0 t)))) (\lambda (x0: nat).(\lambda (H8: 
(eq nat i (clen c))).(\lambda (H9: (eq K k (Bind Abbr))).(\lambda (H10: (eq T 
u u0)).(\lambda (_: (eq C d (CSort x0))).(let H12 \def (eq_ind nat i (\lambda 
(n: nat).(subst0 n u0 t4 t)) H3 (clen c) H8) in (let H13 \def (eq_ind_r T u0 
(\lambda (t0: T).(subst0 (clen c) t0 t4 t)) H12 u H10) in (eq_ind_r K (Bind 
Abbr) (\lambda (k0: K).(or (pr2 c t3 t) (ex3 T (\lambda (_: T).(eq K k0 (Bind 
Abbr))) (\lambda (t0: T).(pr0 t3 t0)) (\lambda (t0: T).(subst0 (clen c) u t0 
t))))) (or_intror (pr2 c t3 t) (ex3 T (\lambda (_: T).(eq K (Bind Abbr) (Bind 
Abbr))) (\lambda (t0: T).(pr0 t3 t0)) (\lambda (t0: T).(subst0 (clen c) u t0 
t))) (ex3_intro T (\lambda (_: T).(eq K (Bind Abbr) (Bind Abbr))) (\lambda 
(t0: T).(pr0 t3 t0)) (\lambda (t0: T).(subst0 (clen c) u t0 t)) t4 
(refl_equal K (Bind Abbr)) H2 H13)) k H9)))))))) H7)) H6))))))))))))))) y t1 
t2 H0))) H)))))).
(* COMMENTS
Initial nodes: 1161
END *)

theorem pr2_gen_cbind:
 \forall (b: B).(\forall (c: C).(\forall (v: T).(\forall (t1: T).(\forall 
(t2: T).((pr2 (CHead c (Bind b) v) t1 t2) \to (pr2 c (THead (Bind b) v t1) 
(THead (Bind b) v t2)))))))
\def
 \lambda (b: B).(\lambda (c: C).(\lambda (v: T).(\lambda (t1: T).(\lambda 
(t2: T).(\lambda (H: (pr2 (CHead c (Bind b) v) t1 t2)).(insert_eq C (CHead c 
(Bind b) v) (\lambda (c0: C).(pr2 c0 t1 t2)) (\lambda (_: C).(pr2 c (THead 
(Bind b) v t1) (THead (Bind b) v t2))) (\lambda (y: C).(\lambda (H0: (pr2 y 
t1 t2)).(pr2_ind (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).((eq C c0 
(CHead c (Bind b) v)) \to (pr2 c (THead (Bind b) v t) (THead (Bind b) v 
t0)))))) (\lambda (c0: C).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H1: 
(pr0 t3 t4)).(\lambda (_: (eq C c0 (CHead c (Bind b) v))).(pr2_free c (THead 
(Bind b) v t3) (THead (Bind b) v t4) (pr0_comp v v (pr0_refl v) t3 t4 H1 
(Bind b)))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: 
nat).(\lambda (H1: (getl i c0 (CHead d (Bind Abbr) u))).(\lambda (t3: 
T).(\lambda (t4: T).(\lambda (H2: (pr0 t3 t4)).(\lambda (t: T).(\lambda (H3: 
(subst0 i u t4 t)).(\lambda (H4: (eq C c0 (CHead c (Bind b) v))).(let H5 \def 
(eq_ind C c0 (\lambda (c1: C).(getl i c1 (CHead d (Bind Abbr) u))) H1 (CHead 
c (Bind b) v) H4) in (let H_x \def (getl_gen_bind b c (CHead d (Bind Abbr) u) 
v i H5) in (let H6 \def H_x in (or_ind (land (eq nat i O) (eq C (CHead d 
(Bind Abbr) u) (CHead c (Bind b) v))) (ex2 nat (\lambda (j: nat).(eq nat i (S 
j))) (\lambda (j: nat).(getl j c (CHead d (Bind Abbr) u)))) (pr2 c (THead 
(Bind b) v t3) (THead (Bind b) v t)) (\lambda (H7: (land (eq nat i O) (eq C 
(CHead d (Bind Abbr) u) (CHead c (Bind b) v)))).(land_ind (eq nat i O) (eq C 
(CHead d (Bind Abbr) u) (CHead c (Bind b) v)) (pr2 c (THead (Bind b) v t3) 
(THead (Bind b) v t)) (\lambda (H8: (eq nat i O)).(\lambda (H9: (eq C (CHead 
d (Bind Abbr) u) (CHead c (Bind b) v))).(let H10 \def (f_equal C C (\lambda 
(e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d 
| (CHead c1 _ _) \Rightarrow c1])) (CHead d (Bind Abbr) u) (CHead c (Bind b) 
v) H9) in ((let H11 \def (f_equal C B (\lambda (e: C).(match e in C return 
(\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u) 
(CHead c (Bind b) v) H9) in ((let H12 \def (f_equal C T (\lambda (e: 
C).(match e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | 
(CHead _ _ t0) \Rightarrow t0])) (CHead d (Bind Abbr) u) (CHead c (Bind b) v) 
H9) in (\lambda (H13: (eq B Abbr b)).(\lambda (_: (eq C d c)).(let H15 \def 
(eq_ind nat i (\lambda (n: nat).(subst0 n u t4 t)) H3 O H8) in (let H16 \def 
(eq_ind T u (\lambda (t0: T).(subst0 O t0 t4 t)) H15 v H12) in (eq_ind B Abbr 
(\lambda (b0: B).(pr2 c (THead (Bind b0) v t3) (THead (Bind b0) v t))) 
(pr2_free c (THead (Bind Abbr) v t3) (THead (Bind Abbr) v t) (pr0_delta v v 
(pr0_refl v) t3 t4 H2 t H16)) b H13)))))) H11)) H10)))) H7)) (\lambda (H7: 
(ex2 nat (\lambda (j: nat).(eq nat i (S j))) (\lambda (j: nat).(getl j c 
(CHead d (Bind Abbr) u))))).(ex2_ind nat (\lambda (j: nat).(eq nat i (S j))) 
(\lambda (j: nat).(getl j c (CHead d (Bind Abbr) u))) (pr2 c (THead (Bind b) 
v t3) (THead (Bind b) v t)) (\lambda (x: nat).(\lambda (H8: (eq nat i (S 
x))).(\lambda (H9: (getl x c (CHead d (Bind Abbr) u))).(let H10 \def (f_equal 
nat nat (\lambda (e: nat).e) i (S x) H8) in (let H11 \def (eq_ind nat i 
(\lambda (n: nat).(subst0 n u t4 t)) H3 (S x) H10) in (pr2_head_2 c v t3 t 
(Bind b) (pr2_delta (CHead c (Bind b) v) d u (S x) (getl_clear_bind b (CHead 
c (Bind b) v) c v (clear_bind b c v) (CHead d (Bind Abbr) u) x H9) t3 t4 H2 t 
H11))))))) H7)) H6))))))))))))))) y t1 t2 H0))) H)))))).
(* COMMENTS
Initial nodes: 1085
END *)

theorem pr2_gen_cflat:
 \forall (f: F).(\forall (c: C).(\forall (v: T).(\forall (t1: T).(\forall 
(t2: T).((pr2 (CHead c (Flat f) v) t1 t2) \to (pr2 c t1 t2))))))
\def
 \lambda (f: F).(\lambda (c: C).(\lambda (v: T).(\lambda (t1: T).(\lambda 
(t2: T).(\lambda (H: (pr2 (CHead c (Flat f) v) t1 t2)).(insert_eq C (CHead c 
(Flat f) v) (\lambda (c0: C).(pr2 c0 t1 t2)) (\lambda (_: C).(pr2 c t1 t2)) 
(\lambda (y: C).(\lambda (H0: (pr2 y t1 t2)).(pr2_ind (\lambda (c0: 
C).(\lambda (t: T).(\lambda (t0: T).((eq C c0 (CHead c (Flat f) v)) \to (pr2 
c t t0))))) (\lambda (c0: C).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H1: 
(pr0 t3 t4)).(\lambda (_: (eq C c0 (CHead c (Flat f) v))).(pr2_free c t3 t4 
H1)))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: 
nat).(\lambda (H1: (getl i c0 (CHead d (Bind Abbr) u))).(\lambda (t3: 
T).(\lambda (t4: T).(\lambda (H2: (pr0 t3 t4)).(\lambda (t: T).(\lambda (H3: 
(subst0 i u t4 t)).(\lambda (H4: (eq C c0 (CHead c (Flat f) v))).(let H5 \def 
(eq_ind C c0 (\lambda (c1: C).(getl i c1 (CHead d (Bind Abbr) u))) H1 (CHead 
c (Flat f) v) H4) in (let H_y \def (getl_gen_flat f c (CHead d (Bind Abbr) u) 
v i H5) in (pr2_delta c d u i H_y t3 t4 H2 t H3)))))))))))))) y t1 t2 H0))) 
H)))))).
(* COMMENTS
Initial nodes: 293
END *)

