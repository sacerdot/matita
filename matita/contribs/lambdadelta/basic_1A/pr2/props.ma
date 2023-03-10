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

include "basic_1A/pr2/fwd.ma".

include "basic_1A/pr0/subst0.ma".

lemma pr2_thin_dx:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall 
(u: T).(\forall (f: F).(pr2 c (THead (Flat f) u t1) (THead (Flat f) u 
t2)))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr2 c t1 
t2)).(\lambda (u: T).(\lambda (f: F).(pr2_ind (\lambda (c0: C).(\lambda (t: 
T).(\lambda (t0: T).(pr2 c0 (THead (Flat f) u t) (THead (Flat f) u t0))))) 
(\lambda (c0: C).(\lambda (t0: T).(\lambda (t3: T).(\lambda (H0: (pr0 t0 
t3)).(pr2_free c0 (THead (Flat f) u t0) (THead (Flat f) u t3) (pr0_comp u u 
(pr0_refl u) t0 t3 H0 (Flat f))))))) (\lambda (c0: C).(\lambda (d: 
C).(\lambda (u0: T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind 
Abbr) u0))).(\lambda (t0: T).(\lambda (t3: T).(\lambda (H1: (pr0 t0 
t3)).(\lambda (t: T).(\lambda (H2: (subst0 i u0 t3 t)).(pr2_delta c0 d u0 i 
H0 (THead (Flat f) u t0) (THead (Flat f) u t3) (pr0_comp u u (pr0_refl u) t0 
t3 H1 (Flat f)) (THead (Flat f) u t) (subst0_snd (Flat f) u0 t t3 i H2 
u)))))))))))) c t1 t2 H)))))).

lemma pr2_head_1:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr2 c u1 u2) \to (\forall 
(k: K).(\forall (t: T).(pr2 c (THead k u1 t) (THead k u2 t)))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr2 c u1 
u2)).(\lambda (k: K).(\lambda (t: T).(pr2_ind (\lambda (c0: C).(\lambda (t0: 
T).(\lambda (t1: T).(pr2 c0 (THead k t0 t) (THead k t1 t))))) (\lambda (c0: 
C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pr0 t1 t2)).(pr2_free c0 
(THead k t1 t) (THead k t2 t) (pr0_comp t1 t2 H0 t t (pr0_refl t) k)))))) 
(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H0: (getl i c0 (CHead d (Bind Abbr) u))).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (H1: (pr0 t1 t2)).(\lambda (t0: T).(\lambda (H2: (subst0 i u t2 
t0)).(pr2_delta c0 d u i H0 (THead k t1 t) (THead k t2 t) (pr0_comp t1 t2 H1 
t t (pr0_refl t) k) (THead k t0 t) (subst0_fst u t0 t2 i H2 t k)))))))))))) c 
u1 u2 H)))))).

lemma pr2_head_2:
 \forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall (t2: T).(\forall 
(k: K).((pr2 (CHead c k u) t1 t2) \to (pr2 c (THead k u t1) (THead k u 
t2)))))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(k: K).(\lambda (H: (pr2 (CHead c k u) t1 t2)).(insert_eq C (CHead c k u) 
(\lambda (c0: C).(pr2 c0 t1 t2)) (\lambda (_: C).(pr2 c (THead k u t1) (THead 
k u t2))) (\lambda (y: C).(\lambda (H0: (pr2 y t1 t2)).(pr2_ind (\lambda (c0: 
C).(\lambda (t: T).(\lambda (t0: T).((eq C c0 (CHead c k u)) \to (pr2 c 
(THead k u t) (THead k u t0)))))) (\lambda (c0: C).(\lambda (t3: T).(\lambda 
(t4: T).(\lambda (H1: (pr0 t3 t4)).(\lambda (_: (eq C c0 (CHead c k 
u))).(pr2_free c (THead k u t3) (THead k u t4) (pr0_comp u u (pr0_refl u) t3 
t4 H1 k))))))) (K_ind (\lambda (k0: K).(\forall (c0: C).(\forall (d: 
C).(\forall (u0: T).(\forall (i: nat).((getl i c0 (CHead d (Bind Abbr) u0)) 
\to (\forall (t3: T).(\forall (t4: T).((pr0 t3 t4) \to (\forall (t: 
T).((subst0 i u0 t4 t) \to ((eq C c0 (CHead c k0 u)) \to (pr2 c (THead k0 u 
t3) (THead k0 u t)))))))))))))) (\lambda (b: B).(\lambda (c0: C).(\lambda (d: 
C).(\lambda (u0: T).(\lambda (i: nat).(nat_ind (\lambda (n: nat).((getl n c0 
(CHead d (Bind Abbr) u0)) \to (\forall (t3: T).(\forall (t4: T).((pr0 t3 t4) 
\to (\forall (t: T).((subst0 n u0 t4 t) \to ((eq C c0 (CHead c (Bind b) u)) 
\to (pr2 c (THead (Bind b) u t3) (THead (Bind b) u t)))))))))) (\lambda (H1: 
(getl O c0 (CHead d (Bind Abbr) u0))).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (H2: (pr0 t3 t4)).(\lambda (t: T).(\lambda (H3: (subst0 O u0 t4 
t)).(\lambda (H4: (eq C c0 (CHead c (Bind b) u))).(let H5 \def (eq_ind C c0 
(\lambda (c1: C).(getl O c1 (CHead d (Bind Abbr) u0))) H1 (CHead c (Bind b) 
u) H4) in (let H6 \def (f_equal C C (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow d | (CHead c1 _ _) \Rightarrow c1])) (CHead d (Bind Abbr) u0) 
(CHead c (Bind b) u) (clear_gen_bind b c (CHead d (Bind Abbr) u0) u 
(getl_gen_O (CHead c (Bind b) u) (CHead d (Bind Abbr) u0) H5))) in ((let H7 
\def (f_equal C B (\lambda (e: C).(match e with [(CSort _) \Rightarrow Abbr | 
(CHead _ k0 _) \Rightarrow (match k0 with [(Bind b0) \Rightarrow b0 | (Flat 
_) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u0) (CHead c (Bind b) u) 
(clear_gen_bind b c (CHead d (Bind Abbr) u0) u (getl_gen_O (CHead c (Bind b) 
u) (CHead d (Bind Abbr) u0) H5))) in ((let H8 \def (f_equal C T (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow u0 | (CHead _ _ t0) \Rightarrow t0])) 
(CHead d (Bind Abbr) u0) (CHead c (Bind b) u) (clear_gen_bind b c (CHead d 
(Bind Abbr) u0) u (getl_gen_O (CHead c (Bind b) u) (CHead d (Bind Abbr) u0) 
H5))) in (\lambda (H9: (eq B Abbr b)).(\lambda (_: (eq C d c)).(let H11 \def 
(eq_ind T u0 (\lambda (t0: T).(subst0 O t0 t4 t)) H3 u H8) in (eq_ind B Abbr 
(\lambda (b0: B).(pr2 c (THead (Bind b0) u t3) (THead (Bind b0) u t))) 
(pr2_free c (THead (Bind Abbr) u t3) (THead (Bind Abbr) u t) (pr0_delta u u 
(pr0_refl u) t3 t4 H2 t H11)) b H9))))) H7)) H6)))))))))) (\lambda (n: 
nat).(\lambda (H1: (((getl n c0 (CHead d (Bind Abbr) u0)) \to (\forall (t3: 
T).(\forall (t4: T).((pr0 t3 t4) \to (\forall (t: T).((subst0 n u0 t4 t) \to 
((eq C c0 (CHead c (Bind b) u)) \to (pr2 c (THead (Bind b) u t3) (THead (Bind 
b) u t))))))))))).(\lambda (H2: (getl (S n) c0 (CHead d (Bind Abbr) 
u0))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H3: (pr0 t3 t4)).(\lambda 
(t: T).(\lambda (H4: (subst0 (S n) u0 t4 t)).(\lambda (H5: (eq C c0 (CHead c 
(Bind b) u))).(let H6 \def (eq_ind C c0 (\lambda (c1: C).(getl (S n) c1 
(CHead d (Bind Abbr) u0))) H2 (CHead c (Bind b) u) H5) in (let H7 \def 
(eq_ind C c0 (\lambda (c1: C).((getl n c1 (CHead d (Bind Abbr) u0)) \to 
(\forall (t5: T).(\forall (t6: T).((pr0 t5 t6) \to (\forall (t0: T).((subst0 
n u0 t6 t0) \to ((eq C c1 (CHead c (Bind b) u)) \to (pr2 c (THead (Bind b) u 
t5) (THead (Bind b) u t0)))))))))) H1 (CHead c (Bind b) u) H5) in (pr2_delta 
c d u0 (r (Bind b) n) (getl_gen_S (Bind b) c (CHead d (Bind Abbr) u0) u n H6) 
(THead (Bind b) u t3) (THead (Bind b) u t4) (pr0_comp u u (pr0_refl u) t3 t4 
H3 (Bind b)) (THead (Bind b) u t) (subst0_snd (Bind b) u0 t t4 (r (Bind b) n) 
H4 u))))))))))))) i)))))) (\lambda (f: F).(\lambda (c0: C).(\lambda (d: 
C).(\lambda (u0: T).(\lambda (i: nat).(nat_ind (\lambda (n: nat).((getl n c0 
(CHead d (Bind Abbr) u0)) \to (\forall (t3: T).(\forall (t4: T).((pr0 t3 t4) 
\to (\forall (t: T).((subst0 n u0 t4 t) \to ((eq C c0 (CHead c (Flat f) u)) 
\to (pr2 c (THead (Flat f) u t3) (THead (Flat f) u t)))))))))) (\lambda (H1: 
(getl O c0 (CHead d (Bind Abbr) u0))).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (H2: (pr0 t3 t4)).(\lambda (t: T).(\lambda (H3: (subst0 O u0 t4 
t)).(\lambda (H4: (eq C c0 (CHead c (Flat f) u))).(let H5 \def (eq_ind C c0 
(\lambda (c1: C).(getl O c1 (CHead d (Bind Abbr) u0))) H1 (CHead c (Flat f) 
u) H4) in (pr2_delta c d u0 O (getl_intro O c (CHead d (Bind Abbr) u0) c 
(drop_refl c) (clear_gen_flat f c (CHead d (Bind Abbr) u0) u (getl_gen_O 
(CHead c (Flat f) u) (CHead d (Bind Abbr) u0) H5))) (THead (Flat f) u t3) 
(THead (Flat f) u t4) (pr0_comp u u (pr0_refl u) t3 t4 H2 (Flat f)) (THead 
(Flat f) u t) (subst0_snd (Flat f) u0 t t4 O H3 u)))))))))) (\lambda (n: 
nat).(\lambda (H1: (((getl n c0 (CHead d (Bind Abbr) u0)) \to (\forall (t3: 
T).(\forall (t4: T).((pr0 t3 t4) \to (\forall (t: T).((subst0 n u0 t4 t) \to 
((eq C c0 (CHead c (Flat f) u)) \to (pr2 c (THead (Flat f) u t3) (THead (Flat 
f) u t))))))))))).(\lambda (H2: (getl (S n) c0 (CHead d (Bind Abbr) 
u0))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H3: (pr0 t3 t4)).(\lambda 
(t: T).(\lambda (H4: (subst0 (S n) u0 t4 t)).(\lambda (H5: (eq C c0 (CHead c 
(Flat f) u))).(let H6 \def (eq_ind C c0 (\lambda (c1: C).(getl (S n) c1 
(CHead d (Bind Abbr) u0))) H2 (CHead c (Flat f) u) H5) in (let H7 \def 
(eq_ind C c0 (\lambda (c1: C).((getl n c1 (CHead d (Bind Abbr) u0)) \to 
(\forall (t5: T).(\forall (t6: T).((pr0 t5 t6) \to (\forall (t0: T).((subst0 
n u0 t6 t0) \to ((eq C c1 (CHead c (Flat f) u)) \to (pr2 c (THead (Flat f) u 
t5) (THead (Flat f) u t0)))))))))) H1 (CHead c (Flat f) u) H5) in (pr2_delta 
c d u0 (r (Flat f) n) (getl_gen_S (Flat f) c (CHead d (Bind Abbr) u0) u n H6) 
(THead (Flat f) u t3) (THead (Flat f) u t4) (pr0_comp u u (pr0_refl u) t3 t4 
H3 (Flat f)) (THead (Flat f) u t) (subst0_snd (Flat f) u0 t t4 (r (Flat f) n) 
H4 u))))))))))))) i)))))) k) y t1 t2 H0))) H)))))).

lemma clear_pr2_trans:
 \forall (c2: C).(\forall (t1: T).(\forall (t2: T).((pr2 c2 t1 t2) \to 
(\forall (c1: C).((clear c1 c2) \to (pr2 c1 t1 t2))))))
\def
 \lambda (c2: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr2 c2 t1 
t2)).(pr2_ind (\lambda (c: C).(\lambda (t: T).(\lambda (t0: T).(\forall (c1: 
C).((clear c1 c) \to (pr2 c1 t t0)))))) (\lambda (c: C).(\lambda (t3: 
T).(\lambda (t4: T).(\lambda (H0: (pr0 t3 t4)).(\lambda (c1: C).(\lambda (_: 
(clear c1 c)).(pr2_free c1 t3 t4 H0))))))) (\lambda (c: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c (CHead d (Bind 
Abbr) u))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H1: (pr0 t3 
t4)).(\lambda (t: T).(\lambda (H2: (subst0 i u t4 t)).(\lambda (c1: 
C).(\lambda (H3: (clear c1 c)).(pr2_delta c1 d u i (clear_getl_trans i c 
(CHead d (Bind Abbr) u) H0 c1 H3) t3 t4 H1 t H2))))))))))))) c2 t1 t2 H)))).

lemma pr2_cflat:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall 
(f: F).(\forall (v: T).(pr2 (CHead c (Flat f) v) t1 t2))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr2 c t1 
t2)).(\lambda (f: F).(\lambda (v: T).(pr2_ind (\lambda (c0: C).(\lambda (t: 
T).(\lambda (t0: T).(pr2 (CHead c0 (Flat f) v) t t0)))) (\lambda (c0: 
C).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H0: (pr0 t3 t4)).(pr2_free 
(CHead c0 (Flat f) v) t3 t4 H0))))) (\lambda (c0: C).(\lambda (d: C).(\lambda 
(u: T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind Abbr) 
u))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H1: (pr0 t3 t4)).(\lambda 
(t: T).(\lambda (H2: (subst0 i u t4 t)).(pr2_delta (CHead c0 (Flat f) v) d u 
i (getl_flat c0 (CHead d (Bind Abbr) u) i H0 f v) t3 t4 H1 t H2))))))))))) c 
t1 t2 H)))))).

lemma pr2_ctail:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall 
(k: K).(\forall (u: T).(pr2 (CTail k u c) t1 t2))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr2 c t1 
t2)).(\lambda (k: K).(\lambda (u: T).(pr2_ind (\lambda (c0: C).(\lambda (t: 
T).(\lambda (t0: T).(pr2 (CTail k u c0) t t0)))) (\lambda (c0: C).(\lambda 
(t3: T).(\lambda (t4: T).(\lambda (H0: (pr0 t3 t4)).(pr2_free (CTail k u c0) 
t3 t4 H0))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u0: T).(\lambda (i: 
nat).(\lambda (H0: (getl i c0 (CHead d (Bind Abbr) u0))).(\lambda (t3: 
T).(\lambda (t4: T).(\lambda (H1: (pr0 t3 t4)).(\lambda (t: T).(\lambda (H2: 
(subst0 i u0 t4 t)).(pr2_delta (CTail k u c0) (CTail k u d) u0 i (getl_ctail 
Abbr c0 d u0 i H0 k u) t3 t4 H1 t H2))))))))))) c t1 t2 H)))))).

lemma pr2_change:
 \forall (b: B).((not (eq B b Abbr)) \to (\forall (c: C).(\forall (v1: 
T).(\forall (t1: T).(\forall (t2: T).((pr2 (CHead c (Bind b) v1) t1 t2) \to 
(\forall (v2: T).(pr2 (CHead c (Bind b) v2) t1 t2))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abbr))).(\lambda (c: C).(\lambda 
(v1: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pr2 (CHead c (Bind 
b) v1) t1 t2)).(\lambda (v2: T).(insert_eq C (CHead c (Bind b) v1) (\lambda 
(c0: C).(pr2 c0 t1 t2)) (\lambda (_: C).(pr2 (CHead c (Bind b) v2) t1 t2)) 
(\lambda (y: C).(\lambda (H1: (pr2 y t1 t2)).(pr2_ind (\lambda (c0: 
C).(\lambda (t: T).(\lambda (t0: T).((eq C c0 (CHead c (Bind b) v1)) \to (pr2 
(CHead c (Bind b) v2) t t0))))) (\lambda (c0: C).(\lambda (t3: T).(\lambda 
(t4: T).(\lambda (H2: (pr0 t3 t4)).(\lambda (_: (eq C c0 (CHead c (Bind b) 
v1))).(pr2_free (CHead c (Bind b) v2) t3 t4 H2)))))) (\lambda (c0: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H2: (getl i c0 
(CHead d (Bind Abbr) u))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H3: 
(pr0 t3 t4)).(\lambda (t: T).(\lambda (H4: (subst0 i u t4 t)).(\lambda (H5: 
(eq C c0 (CHead c (Bind b) v1))).(let H6 \def (eq_ind C c0 (\lambda (c1: 
C).(getl i c1 (CHead d (Bind Abbr) u))) H2 (CHead c (Bind b) v1) H5) in 
(nat_ind (\lambda (n: nat).((getl n (CHead c (Bind b) v1) (CHead d (Bind 
Abbr) u)) \to ((subst0 n u t4 t) \to (pr2 (CHead c (Bind b) v2) t3 t)))) 
(\lambda (H7: (getl O (CHead c (Bind b) v1) (CHead d (Bind Abbr) 
u))).(\lambda (H8: (subst0 O u t4 t)).(let H9 \def (f_equal C C (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow d | (CHead c1 _ _) \Rightarrow c1])) 
(CHead d (Bind Abbr) u) (CHead c (Bind b) v1) (clear_gen_bind b c (CHead d 
(Bind Abbr) u) v1 (getl_gen_O (CHead c (Bind b) v1) (CHead d (Bind Abbr) u) 
H7))) in ((let H10 \def (f_equal C B (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow Abbr | (CHead _ k _) \Rightarrow (match k with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u) 
(CHead c (Bind b) v1) (clear_gen_bind b c (CHead d (Bind Abbr) u) v1 
(getl_gen_O (CHead c (Bind b) v1) (CHead d (Bind Abbr) u) H7))) in ((let H11 
\def (f_equal C T (\lambda (e: C).(match e with [(CSort _) \Rightarrow u | 
(CHead _ _ t0) \Rightarrow t0])) (CHead d (Bind Abbr) u) (CHead c (Bind b) 
v1) (clear_gen_bind b c (CHead d (Bind Abbr) u) v1 (getl_gen_O (CHead c (Bind 
b) v1) (CHead d (Bind Abbr) u) H7))) in (\lambda (H12: (eq B Abbr 
b)).(\lambda (_: (eq C d c)).(let H14 \def (eq_ind T u (\lambda (t0: 
T).(subst0 O t0 t4 t)) H8 v1 H11) in (let H15 \def (eq_ind_r B b (\lambda 
(b0: B).(not (eq B b0 Abbr))) H Abbr H12) in (eq_ind B Abbr (\lambda (b0: 
B).(pr2 (CHead c (Bind b0) v2) t3 t)) (let H16 \def (match (H15 (refl_equal B 
Abbr)) in False with []) in H16) b H12)))))) H10)) H9)))) (\lambda (i0: 
nat).(\lambda (_: (((getl i0 (CHead c (Bind b) v1) (CHead d (Bind Abbr) u)) 
\to ((subst0 i0 u t4 t) \to (pr2 (CHead c (Bind b) v2) t3 t))))).(\lambda 
(H7: (getl (S i0) (CHead c (Bind b) v1) (CHead d (Bind Abbr) u))).(\lambda 
(H8: (subst0 (S i0) u t4 t)).(pr2_delta (CHead c (Bind b) v2) d u (S i0) 
(getl_head (Bind b) i0 c (CHead d (Bind Abbr) u) (getl_gen_S (Bind b) c 
(CHead d (Bind Abbr) u) v1 i0 H7) v2) t3 t4 H3 t H8))))) i H6 H4))))))))))))) 
y t1 t2 H1))) H0)))))))).

lemma pr2_lift:
 \forall (c: C).(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h 
d c e) \to (\forall (t1: T).(\forall (t2: T).((pr2 e t1 t2) \to (pr2 c (lift 
h d t1) (lift h d t2)))))))))
\def
 \lambda (c: C).(\lambda (e: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda 
(H: (drop h d c e)).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pr2 e t1 
t2)).(insert_eq C e (\lambda (c0: C).(pr2 c0 t1 t2)) (\lambda (_: C).(pr2 c 
(lift h d t1) (lift h d t2))) (\lambda (y: C).(\lambda (H1: (pr2 y t1 
t2)).(pr2_ind (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).((eq C c0 e) 
\to (pr2 c (lift h d t) (lift h d t0)))))) (\lambda (c0: C).(\lambda (t3: 
T).(\lambda (t4: T).(\lambda (H2: (pr0 t3 t4)).(\lambda (_: (eq C c0 
e)).(pr2_free c (lift h d t3) (lift h d t4) (pr0_lift t3 t4 H2 h d))))))) 
(\lambda (c0: C).(\lambda (d0: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H2: (getl i c0 (CHead d0 (Bind Abbr) u))).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (H3: (pr0 t3 t4)).(\lambda (t: T).(\lambda (H4: (subst0 i u t4 
t)).(\lambda (H5: (eq C c0 e)).(let H6 \def (eq_ind C c0 (\lambda (c1: 
C).(getl i c1 (CHead d0 (Bind Abbr) u))) H2 e H5) in (lt_le_e i d (pr2 c 
(lift h d t3) (lift h d t)) (\lambda (H7: (lt i d)).(let H8 \def 
(drop_getl_trans_le i d (le_S_n i d (le_S_n (S i) (S d) (le_S (S (S i)) (S d) 
(le_n_S (S i) d H7)))) c e h H (CHead d0 (Bind Abbr) u) H6) in (ex3_2_ind C C 
(\lambda (e0: C).(\lambda (_: C).(drop i O c e0))) (\lambda (e0: C).(\lambda 
(e1: C).(drop h (minus d i) e0 e1))) (\lambda (_: C).(\lambda (e1: C).(clear 
e1 (CHead d0 (Bind Abbr) u)))) (pr2 c (lift h d t3) (lift h d t)) (\lambda 
(x0: C).(\lambda (x1: C).(\lambda (H9: (drop i O c x0)).(\lambda (H10: (drop 
h (minus d i) x0 x1)).(\lambda (H11: (clear x1 (CHead d0 (Bind Abbr) 
u))).(let H12 \def (eq_ind nat (minus d i) (\lambda (n: nat).(drop h n x0 
x1)) H10 (S (minus d (S i))) (minus_x_Sy d i H7)) in (let H13 \def 
(drop_clear_S x1 x0 h (minus d (S i)) H12 Abbr d0 u H11) in (ex2_ind C 
(\lambda (c1: C).(clear x0 (CHead c1 (Bind Abbr) (lift h (minus d (S i)) 
u)))) (\lambda (c1: C).(drop h (minus d (S i)) c1 d0)) (pr2 c (lift h d t3) 
(lift h d t)) (\lambda (x: C).(\lambda (H14: (clear x0 (CHead x (Bind Abbr) 
(lift h (minus d (S i)) u)))).(\lambda (_: (drop h (minus d (S i)) x 
d0)).(pr2_delta c x (lift h (minus d (S i)) u) i (getl_intro i c (CHead x 
(Bind Abbr) (lift h (minus d (S i)) u)) x0 H9 H14) (lift h d t3) (lift h d 
t4) (pr0_lift t3 t4 H3 h d) (lift h d t) (subst0_lift_lt t4 t u i H4 d H7 
h))))) H13)))))))) H8))) (\lambda (H7: (le d i)).(pr2_delta c d0 u (plus i h) 
(drop_getl_trans_ge i c e d h H (CHead d0 (Bind Abbr) u) H6 H7) (lift h d t3) 
(lift h d t4) (pr0_lift t3 t4 H3 h d) (lift h d t) (subst0_lift_ge t4 t u i h 
H4 d H7)))))))))))))))) y t1 t2 H1))) H0)))))))).

lemma pr2_gen_abbr:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr2 c 
(THead (Bind Abbr) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(or3 (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t2))) (ex2 T (\lambda (u: 
T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c (Bind Abbr) u) t1 t2))) (ex3_2 T 
T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) u1) t1 y))) 
(\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c (Bind Abbr) u1) z t2)))))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O x)))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr2 c (THead (Bind Abbr) u1 t1) x)).(insert_eq T (THead (Bind Abbr) u1 
t1) (\lambda (t: T).(pr2 c t x)) (\lambda (_: T).(or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Abbr) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(or3 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t2))) (ex2 T 
(\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c (Bind Abbr) u) t1 
t2))) (ex3_2 T T (\lambda (y: T).(\lambda (_: T).(pr2 (CHead c (Bind Abbr) 
u1) t1 y))) (\lambda (y: T).(\lambda (z: T).(pr0 y z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c (Bind Abbr) u1) z t2)))))))) (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O x)))))) 
(\lambda (y: T).(\lambda (H0: (pr2 c y x)).(pr2_ind (\lambda (c0: C).(\lambda 
(t: T).(\lambda (t0: T).((eq T t (THead (Bind Abbr) u1 t1)) \to (or (ex3_2 T 
T (\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Bind Abbr) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t2: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
t2))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind 
Abbr) u) t1 t2))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 
(Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) 
(\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t2)))))))) 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O 
t0))))))))) (\lambda (c0: C).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H1: 
(pr0 t0 t2)).(\lambda (H2: (eq T t0 (THead (Bind Abbr) u1 t1))).(let H3 \def 
(eq_ind T t0 (\lambda (t: T).(pr0 t t2)) H1 (THead (Bind Abbr) u1 t1) H2) in 
(or_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t3))))))) (pr0 t1 (lift (S O) O t2)) (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind 
b) u) t1 t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead 
c0 (Bind Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
(lift (S O) O t2))))) (\lambda (H4: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T 
(\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 
t3)))))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda 
(u2: T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t3)))))) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 t3))) (ex2 T 
(\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 
t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) 
u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O t2))))) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H5: (eq T t2 (THead (Bind Abbr) 
x0 x1))).(\lambda (H6: (pr0 u1 x0)).(\lambda (H_x: (or (pr0 t1 x1) (ex2 T 
(\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O x0 y0 
x1))))).(or_ind (pr0 t1 x1) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda 
(y0: T).(subst0 O x0 y0 x1))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 t3))) (ex2 T (\lambda (u: 
T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 t3))) (ex3_2 
T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) 
(\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O t2))))) (\lambda (H7: (pr0 t1 
x1)).(eq_ind_r T (THead (Bind Abbr) x0 x1) (\lambda (t: T).(or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind 
Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 
(Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) 
(\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O 
t)))))) (or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead 
(Bind Abbr) x0 x1) (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 t3))) (ex2 T (\lambda (u: 
T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 t3))) (ex3_2 
T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) 
(\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O (THead (Bind Abbr) x0 x1))))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) 
x0 x1) (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c0 (Bind b) u) t1 t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) 
(\lambda (u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 t3))) (ex3_2 T T (\lambda 
(y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3))))))) x0 x1 (refl_equal T (THead (Bind Abbr) x0 x1)) 
(pr2_free c0 u1 x0 H6) (or3_intro0 (\forall (b: B).(\forall (u: T).(pr2 
(CHead c0 (Bind b) u) t1 x1))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda 
(u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 x1))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z x1)))) (\lambda (b: B).(\lambda (u: T).(pr2_free (CHead 
c0 (Bind b) u) t1 x1 H7)))))) t2 H5)) (\lambda (H_x0: (ex2 T (\lambda (y0: 
T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O x0 y0 x1)))).(ex2_ind T (\lambda 
(y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O x0 y0 x1)) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind 
Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 
(Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) 
(\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O 
t2))))) (\lambda (x2: T).(\lambda (H7: (pr0 t1 x2)).(\lambda (H8: (subst0 O 
x0 x2 x1)).(eq_ind_r T (THead (Bind Abbr) x0 x1) (\lambda (t: T).(or (ex3_2 T 
T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind 
Abbr) u) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 
(Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) 
(\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O 
t)))))) (ex2_ind T (\lambda (t: T).(subst0 O u1 x2 t)) (\lambda (t: T).(pr0 t 
x1)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind 
Abbr) x0 x1) (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 t3))) (ex2 T (\lambda (u: 
T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 t3))) (ex3_2 
T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) 
(\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O (THead (Bind Abbr) x0 x1)))))) 
(\lambda (x3: T).(\lambda (_: (subst0 O u1 x2 x3)).(\lambda (_: (pr0 x3 
x1)).(or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead 
(Bind Abbr) x0 x1) (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 t3))) (ex2 T (\lambda (u: 
T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 t3))) (ex3_2 
T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) 
(\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O (THead (Bind Abbr) x0 x1))))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T (THead (Bind Abbr) 
x0 x1) (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 
u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c0 (Bind b) u) t1 t3))) (ex2 T (\lambda (u: T).(pr0 u1 u)) 
(\lambda (u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 t3))) (ex3_2 T T (\lambda 
(y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3))))))) x0 x1 (refl_equal T (THead (Bind Abbr) x0 x1)) 
(pr2_free c0 u1 x0 H6) (or3_intro1 (\forall (b: B).(\forall (u: T).(pr2 
(CHead c0 (Bind b) u) t1 x1))) (ex2 T (\lambda (u: T).(pr0 u1 u)) (\lambda 
(u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 x1))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z x1)))) (ex_intro2 T (\lambda (u: T).(pr0 u1 u)) (\lambda 
(u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 x1)) x0 H6 (pr2_delta (CHead c0 (Bind 
Abbr) x0) c0 x0 O (getl_refl Abbr c0 x0) t1 x2 H7 x1 H8)))))))) 
(pr0_subst0_back x0 x2 x1 O H8 u1 H6)) t2 H5)))) H_x0)) H_x)))))) H4)) 
(\lambda (H4: (pr0 t1 (lift (S O) O t2))).(or_intror (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 t3))) (ex2 T 
(\lambda (u: T).(pr0 u1 u)) (\lambda (u: T).(pr2 (CHead c0 (Bind Abbr) u) t1 
t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) 
u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 (lift (S O) O t2)))) 
(\lambda (b: B).(\lambda (u: T).(pr2_free (CHead c0 (Bind b) u) t1 (lift (S 
O) O t2) H4))))) (pr0_gen_abbr u1 t1 t2 H3)))))))) (\lambda (c0: C).(\lambda 
(d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H1: (getl i c0 (CHead d 
(Bind Abbr) u))).(\lambda (t0: T).(\lambda (t2: T).(\lambda (H2: (pr0 t0 
t2)).(\lambda (t: T).(\lambda (H3: (subst0 i u t2 t)).(\lambda (H4: (eq T t0 
(THead (Bind Abbr) u1 t1))).(let H5 \def (eq_ind T t0 (\lambda (t3: T).(pr0 
t3 t2)) H2 (THead (Bind Abbr) u1 t1) H4) in (or_ind (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t3: T).(or (pr0 
t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 
t3))))))) (pr0 t1 (lift (S O) O t2)) (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: 
T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) 
(ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 
y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda 
(z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t))))) (\lambda (H6: 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: 
T).(\lambda (t3: T).(or (pr0 t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O u2 y0 t3)))))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t2 (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (u2: T).(\lambda (t3: T).(or (pr0 
t1 t3) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O u2 y0 
t3)))))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t))))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H7: (eq T t2 (THead (Bind Abbr) x0 x1))).(\lambda (H8: (pr0 u1 
x0)).(\lambda (H_x: (or (pr0 t1 x1) (ex2 T (\lambda (y0: T).(pr0 t1 y0)) 
(\lambda (y0: T).(subst0 O x0 y0 x1))))).(or_ind (pr0 t1 x1) (ex2 T (\lambda 
(y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 O x0 y0 x1))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 
(Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t))))) (\lambda (H9: (pr0 t1 x1)).(let H10 \def (eq_ind T t2 
(\lambda (t3: T).(subst0 i u t3 t)) H3 (THead (Bind Abbr) x0 x1) H7) in 
(or3_ind (ex2 T (\lambda (u2: T).(eq T t (THead (Bind Abbr) u2 x1))) (\lambda 
(u2: T).(subst0 i u x0 u2))) (ex2 T (\lambda (t3: T).(eq T t (THead (Bind 
Abbr) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3))) (ex3_2 T 
T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3)))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 
(Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t))))) (\lambda (H11: (ex2 T (\lambda (u2: T).(eq T t (THead 
(Bind Abbr) u2 x1))) (\lambda (u2: T).(subst0 i u x0 u2)))).(ex2_ind T 
(\lambda (u2: T).(eq T t (THead (Bind Abbr) u2 x1))) (\lambda (u2: T).(subst0 
i u x0 u2)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t))))) (\lambda (x2: T).(\lambda (H12: (eq T 
t (THead (Bind Abbr) x2 x1))).(\lambda (H13: (subst0 i u x0 x2)).(or_introl 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 
(Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: 
T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t)))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3))))))) x2 x1 H12 
(pr2_delta c0 d u i H1 u1 x0 H8 x2 H13) (or3_intro0 (\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) t1 x1))) (ex2 T (\lambda (u0: T).(pr0 u1 
u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 x1))) (ex3_2 T T 
(\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) 
(\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c0 (Bind Abbr) u1) z x1)))) (\lambda (b: B).(\lambda (u0: 
T).(pr2_free (CHead c0 (Bind b) u0) t1 x1 H9))))))))) H11)) (\lambda (H11: 
(ex2 T (\lambda (t3: T).(eq T t (THead (Bind Abbr) x0 t3))) (\lambda (t3: 
T).(subst0 (s (Bind Abbr) i) u x1 t3)))).(ex2_ind T (\lambda (t3: T).(eq T t 
(THead (Bind Abbr) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 
t3)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind 
Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 
(Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: 
T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t))))) (\lambda (x2: T).(\lambda (H12: (eq T 
t (THead (Bind Abbr) x0 x2))).(\lambda (H13: (subst0 (s (Bind Abbr) i) u x1 
x2)).(or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t)))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3))))))) x0 x2 H12 
(pr2_free c0 u1 x0 H8) (or3_intro0 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 x2))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 x2))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z x2)))) (\lambda (b: B).(\lambda (u0: T).(pr2_delta 
(CHead c0 (Bind b) u0) d u (S i) (getl_head (Bind b) i c0 (CHead d (Bind 
Abbr) u) H1 u0) t1 x1 H9 x2 H13))))))))) H11)) (\lambda (H11: (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 
(Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t))))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H12: (eq T t 
(THead (Bind Abbr) x2 x3))).(\lambda (H13: (subst0 i u x0 x2)).(\lambda (H14: 
(subst0 (s (Bind Abbr) i) u x1 x3)).(or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t)))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 
(Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: 
T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3))))))) x2 x3 H12 (pr2_delta c0 d u i H1 u1 x0 H8 x2 
H13) (or3_intro0 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) 
t1 x3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 
(Bind Abbr) u0) t1 x3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z x3)))) 
(\lambda (b: B).(\lambda (u0: T).(pr2_delta (CHead c0 (Bind b) u0) d u (S i) 
(getl_head (Bind b) i c0 (CHead d (Bind Abbr) u) H1 u0) t1 x1 H9 x3 
H14))))))))))) H11)) (subst0_gen_head (Bind Abbr) u x0 x1 t i H10)))) 
(\lambda (H_x0: (ex2 T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: T).(subst0 
O x0 y0 x1)))).(ex2_ind T (\lambda (y0: T).(pr0 t1 y0)) (\lambda (y0: 
T).(subst0 O x0 y0 x1)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: 
T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) 
(\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda 
(y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t))))) (\lambda (x2: T).(\lambda (H9: (pr0 
t1 x2)).(\lambda (H10: (subst0 O x0 x2 x1)).(let H11 \def (eq_ind T t2 
(\lambda (t3: T).(subst0 i u t3 t)) H3 (THead (Bind Abbr) x0 x1) H7) in 
(or3_ind (ex2 T (\lambda (u2: T).(eq T t (THead (Bind Abbr) u2 x1))) (\lambda 
(u2: T).(subst0 i u x0 u2))) (ex2 T (\lambda (t3: T).(eq T t (THead (Bind 
Abbr) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3))) (ex3_2 T 
T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3)))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 
(Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t))))) (\lambda (H12: (ex2 T (\lambda (u2: T).(eq T t (THead 
(Bind Abbr) u2 x1))) (\lambda (u2: T).(subst0 i u x0 u2)))).(ex2_ind T 
(\lambda (u2: T).(eq T t (THead (Bind Abbr) u2 x1))) (\lambda (u2: T).(subst0 
i u x0 u2)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t))))) (\lambda (x3: T).(\lambda (H13: (eq T 
t (THead (Bind Abbr) x3 x1))).(\lambda (H14: (subst0 i u x0 x3)).(ex2_ind T 
(\lambda (t3: T).(subst0 O u1 x2 t3)) (\lambda (t3: T).(pr0 t3 x1)) (or 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 
(Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: 
T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t))))) (\lambda (x4: T).(\lambda (_: (subst0 
O u1 x2 x4)).(\lambda (_: (pr0 x4 x1)).(or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t)))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 
(Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: 
T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3))))))) x3 x1 H13 (pr2_delta c0 d u i H1 u1 x0 H8 x3 
H14) (or3_intro1 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) 
t1 x1))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 
(Bind Abbr) u0) t1 x1))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z x1)))) 
(ex_intro2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 
(Bind Abbr) u0) t1 x1)) x0 H8 (pr2_delta (CHead c0 (Bind Abbr) x0) c0 x0 O 
(getl_refl Abbr c0 x0) t1 x2 H9 x1 H10)))))))) (pr0_subst0_back x0 x2 x1 O 
H10 u1 H8))))) H12)) (\lambda (H12: (ex2 T (\lambda (t3: T).(eq T t (THead 
(Bind Abbr) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 
t3)))).(ex2_ind T (\lambda (t3: T).(eq T t (THead (Bind Abbr) x0 t3))) 
(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3)) (or (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t))))) 
(\lambda (x3: T).(\lambda (H13: (eq T t (THead (Bind Abbr) x0 x3))).(\lambda 
(H14: (subst0 (s (Bind Abbr) i) u x1 x3)).(ex2_ind T (\lambda (t3: T).(subst0 
O u1 x2 t3)) (\lambda (t3: T).(pr0 t3 x1)) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t))))) 
(\lambda (x4: T).(\lambda (H15: (subst0 O u1 x2 x4)).(\lambda (H16: (pr0 x4 
x1)).(or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t)))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3))))))) x0 x3 H13 
(pr2_free c0 u1 x0 H8) (or3_intro2 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 x3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 x3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z x3)))) (ex3_2_intro T T (\lambda (y0: T).(\lambda (_: 
T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: 
T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) 
u1) z x3))) x4 x1 (pr2_delta (CHead c0 (Bind Abbr) u1) c0 u1 O (getl_refl 
Abbr c0 u1) t1 x2 H9 x4 H15) H16 (pr2_delta (CHead c0 (Bind Abbr) u1) d u (S 
i) (getl_head (Bind Abbr) i c0 (CHead d (Bind Abbr) u) H1 u1) x1 x1 (pr0_refl 
x1) x3 H14)))))))) (pr0_subst0_back x0 x2 x1 O H10 u1 H8))))) H12)) (\lambda 
(H12: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Abbr) i) u x1 t3))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 
(Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 
(CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 
z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z 
t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t))))) (\lambda (x3: T).(\lambda (x4: T).(\lambda (H13: (eq T t 
(THead (Bind Abbr) x3 x4))).(\lambda (H14: (subst0 i u x0 x3)).(\lambda (H15: 
(subst0 (s (Bind Abbr) i) u x1 x4)).(ex2_ind T (\lambda (t3: T).(subst0 O u1 
x2 t3)) (\lambda (t3: T).(pr0 t3 x1)) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t))))) 
(\lambda (x5: T).(\lambda (H16: (subst0 O u1 x2 x5)).(\lambda (H17: (pr0 x5 
x1)).(or_introl (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead 
(Bind Abbr) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) 
(\lambda (_: T).(\lambda (t3: T).(or3 (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t3))) (ex2 T (\lambda (u0: T).(pr0 u1 u0)) (\lambda 
(u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 t3))) (ex3_2 T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead 
c0 (Bind b) u0) t1 (lift (S O) O t)))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3))))))) x3 x4 H13 
(pr2_delta c0 d u i H1 u1 x0 H8 x3 H14) (or3_intro2 (\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c0 (Bind b) u0) t1 x4))) (ex2 T (\lambda (u0: T).(pr0 u1 
u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) t1 x4))) (ex3_2 T T 
(\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) 
(\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: 
T).(pr2 (CHead c0 (Bind Abbr) u1) z x4)))) (ex3_2_intro T T (\lambda (y0: 
T).(\lambda (_: T).(pr2 (CHead c0 (Bind Abbr) u1) t1 y0))) (\lambda (y0: 
T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: T).(\lambda (z: T).(pr2 (CHead 
c0 (Bind Abbr) u1) z x4))) x5 x1 (pr2_delta (CHead c0 (Bind Abbr) u1) c0 u1 O 
(getl_refl Abbr c0 u1) t1 x2 H9 x5 H16) H17 (pr2_delta (CHead c0 (Bind Abbr) 
u1) d u (S i) (getl_head (Bind Abbr) i c0 (CHead d (Bind Abbr) u) H1 u1) x1 
x1 (pr0_refl x1) x4 H15)))))))) (pr0_subst0_back x0 x2 x1 O H10 u1 H8))))))) 
H12)) (subst0_gen_head (Bind Abbr) u x0 x1 t i H11)))))) H_x0)) H_x)))))) 
H6)) (\lambda (H6: (pr0 t1 (lift (S O) O t2))).(or_intror (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t (THead (Bind Abbr) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(or3 
(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3))) (ex2 T 
(\lambda (u0: T).(pr0 u1 u0)) (\lambda (u0: T).(pr2 (CHead c0 (Bind Abbr) u0) 
t1 t3))) (ex3_2 T T (\lambda (y0: T).(\lambda (_: T).(pr2 (CHead c0 (Bind 
Abbr) u1) t1 y0))) (\lambda (y0: T).(\lambda (z: T).(pr0 y0 z))) (\lambda (_: 
T).(\lambda (z: T).(pr2 (CHead c0 (Bind Abbr) u1) z t3)))))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t)))) 
(\lambda (b: B).(\lambda (u0: T).(pr2_delta (CHead c0 (Bind b) u0) d u (S i) 
(getl_head (Bind b) i c0 (CHead d (Bind Abbr) u) H1 u0) t1 (lift (S O) O t2) 
H6 (lift (S O) O t) (subst0_lift_ge_S t2 t u i H3 O (le_O_n i))))))) 
(pr0_gen_abbr u1 t1 t2 H5)))))))))))))) c y x H0))) H))))).

lemma pr2_gen_void:
 \forall (c: C).(\forall (u1: T).(\forall (t1: T).(\forall (x: T).((pr2 c 
(THead (Bind Void) u1 t1) x) \to (or (ex3_2 T T (\lambda (u2: T).(\lambda 
(t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall (b: B).(\forall 
(u: T).(pr2 (CHead c (Bind b) u) t1 t2)))))) (\forall (b: B).(\forall (u: 
T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O x)))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (t1: T).(\lambda (x: T).(\lambda 
(H: (pr2 c (THead (Bind Void) u1 t1) x)).(insert_eq T (THead (Bind Void) u1 
t1) (\lambda (t: T).(pr2 c t x)) (\lambda (_: T).(or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t2: T).(eq T x (THead (Bind Void) u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u1 u2))) (\lambda (_: T).(\lambda (t2: T).(\forall 
(b: B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 t2)))))) (\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) t1 (lift (S O) O x)))))) 
(\lambda (y: T).(\lambda (H0: (pr2 c y x)).(pr2_ind (\lambda (c0: C).(\lambda 
(t: T).(\lambda (t0: T).((eq T t (THead (Bind Void) u1 t1)) \to (or (ex3_2 T 
T (\lambda (u2: T).(\lambda (t2: T).(eq T t0 (THead (Bind Void) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t2: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
t2)))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 (lift 
(S O) O t0))))))))) (\lambda (c0: C).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (H1: (pr0 t0 t2)).(\lambda (H2: (eq T t0 (THead (Bind Void) u1 
t1))).(let H3 \def (eq_ind T t0 (\lambda (t: T).(pr0 t t2)) H1 (THead (Bind 
Void) u1 t1) H2) in (or_ind (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq 
T t2 (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O 
t2)) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind 
Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda 
(_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind 
b) u) t1 t3)))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) 
t1 (lift (S O) O t2))))) (\lambda (H4: (ex3_2 T T (\lambda (u2: T).(\lambda 
(t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))))).(ex3_2_ind 
T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 
(THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 
(CHead c0 (Bind b) u) t1 t3)))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead 
c0 (Bind b) u) t1 (lift (S O) O t2))))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H5: (eq T t2 (THead (Bind Void) x0 x1))).(\lambda (H6: (pr0 u1 
x0)).(\lambda (H7: (pr0 t1 x1)).(eq_ind_r T (THead (Bind Void) x0 x1) 
(\lambda (t: T).(or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t 
(THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 
(CHead c0 (Bind b) u) t1 t3)))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead 
c0 (Bind b) u) t1 (lift (S O) O t)))))) (or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Void) x0 x1) (THead (Bind Void) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) 
u) t1 t3)))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
(lift (S O) O (THead (Bind Void) x0 x1))))) (ex3_2_intro T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T (THead (Bind Void) x0 x1) (THead (Bind Void) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) 
u) t1 t3))))) x0 x1 (refl_equal T (THead (Bind Void) x0 x1)) (pr2_free c0 u1 
x0 H6) (\lambda (b: B).(\lambda (u: T).(pr2_free (CHead c0 (Bind b) u) t1 x1 
H7))))) t2 H5)))))) H4)) (\lambda (H4: (pr0 t1 (lift (S O) O t2))).(or_intror 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) 
u) t1 t3)))))) (\forall (b: B).(\forall (u: T).(pr2 (CHead c0 (Bind b) u) t1 
(lift (S O) O t2)))) (\lambda (b: B).(\lambda (u: T).(pr2_free (CHead c0 
(Bind b) u) t1 (lift (S O) O t2) H4))))) (pr0_gen_void u1 t1 t2 H3)))))))) 
(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H1: (getl i c0 (CHead d (Bind Abbr) u))).(\lambda (t0: T).(\lambda (t2: 
T).(\lambda (H2: (pr0 t0 t2)).(\lambda (t: T).(\lambda (H3: (subst0 i u t2 
t)).(\lambda (H4: (eq T t0 (THead (Bind Void) u1 t1))).(let H5 \def (eq_ind T 
t0 (\lambda (t3: T).(pr0 t3 t2)) H2 (THead (Bind Void) u1 t1) H4) in (or_ind 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(pr0 t1 t3)))) (pr0 t1 (lift (S O) O t2)) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3)))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t))))) (\lambda (H6: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(pr0 t1 t3))))).(ex3_2_ind 
T T (\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr0 u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(pr0 t1 t3))) (or (ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t 
(THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t3)))))) (\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 (lift (S O) O t))))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H7: (eq T t2 (THead (Bind Void) x0 x1))).(\lambda (H8: (pr0 u1 
x0)).(\lambda (H9: (pr0 t1 x1)).(let H10 \def (eq_ind T t2 (\lambda (t3: 
T).(subst0 i u t3 t)) H3 (THead (Bind Void) x0 x1) H7) in (or3_ind (ex2 T 
(\lambda (u2: T).(eq T t (THead (Bind Void) u2 x1))) (\lambda (u2: T).(subst0 
i u x0 u2))) (ex2 T (\lambda (t3: T).(eq T t (THead (Bind Void) x0 t3))) 
(\lambda (t3: T).(subst0 (s (Bind Void) i) u x1 t3))) (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s (Bind Void) i) u x1 t3)))) (or (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3)))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t))))) 
(\lambda (H11: (ex2 T (\lambda (u2: T).(eq T t (THead (Bind Void) u2 x1))) 
(\lambda (u2: T).(subst0 i u x0 u2)))).(ex2_ind T (\lambda (u2: T).(eq T t 
(THead (Bind Void) u2 x1))) (\lambda (u2: T).(subst0 i u x0 u2)) (or (ex3_2 T 
T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3)))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t))))) (\lambda (x2: T).(\lambda (H12: (eq T t (THead (Bind 
Void) x2 x1))).(\lambda (H13: (subst0 i u x0 x2)).(or_introl (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3)))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t)))) (ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T 
t (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 
u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 
(CHead c0 (Bind b) u0) t1 t3))))) x2 x1 H12 (pr2_delta c0 d u i H1 u1 x0 H8 
x2 H13) (\lambda (b: B).(\lambda (u0: T).(pr2_free (CHead c0 (Bind b) u0) t1 
x1 H9)))))))) H11)) (\lambda (H11: (ex2 T (\lambda (t3: T).(eq T t (THead 
(Bind Void) x0 t3))) (\lambda (t3: T).(subst0 (s (Bind Void) i) u x1 
t3)))).(ex2_ind T (\lambda (t3: T).(eq T t (THead (Bind Void) x0 t3))) 
(\lambda (t3: T).(subst0 (s (Bind Void) i) u x1 t3)) (or (ex3_2 T T (\lambda 
(u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3)))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t))))) 
(\lambda (x2: T).(\lambda (H12: (eq T t (THead (Bind Void) x0 x2))).(\lambda 
(H13: (subst0 (s (Bind Void) i) u x1 x2)).(or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3)))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t)))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) t1 t3))))) x0 x2 H12 (pr2_free c0 u1 x0 H8) (\lambda (b: B).(\lambda (u0: 
T).(pr2_delta (CHead c0 (Bind b) u0) d u (S i) (getl_head (Bind b) i c0 
(CHead d (Bind Abbr) u) H1 u0) t1 x1 H9 x2 H13)))))))) H11)) (\lambda (H11: 
(ex3_2 T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 
t3)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Void) i) u x1 t3))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u x0 u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst0 (s (Bind Void) i) u x1 t3))) (or (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) 
(\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda 
(t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
t3)))))) (\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 
(lift (S O) O t))))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H12: (eq T t 
(THead (Bind Void) x2 x3))).(\lambda (H13: (subst0 i u x0 x2)).(\lambda (H14: 
(subst0 (s (Bind Void) i) u x1 x3)).(or_introl (ex3_2 T T (\lambda (u2: 
T).(\lambda (t3: T).(eq T t (THead (Bind Void) u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall 
(b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 t3)))))) (\forall (b: 
B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t)))) 
(ex3_2_intro T T (\lambda (u2: T).(\lambda (t3: T).(eq T t (THead (Bind Void) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 c0 u1 u2))) (\lambda (_: 
T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(pr2 (CHead c0 (Bind b) 
u0) t1 t3))))) x2 x3 H12 (pr2_delta c0 d u i H1 u1 x0 H8 x2 H13) (\lambda (b: 
B).(\lambda (u0: T).(pr2_delta (CHead c0 (Bind b) u0) d u (S i) (getl_head 
(Bind b) i c0 (CHead d (Bind Abbr) u) H1 u0) t1 x1 H9 x3 H14)))))))))) H11)) 
(subst0_gen_head (Bind Void) u x0 x1 t i H10)))))))) H6)) (\lambda (H6: (pr0 
t1 (lift (S O) O t2))).(or_intror (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t (THead (Bind Void) u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(pr2 
c0 u1 u2))) (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: 
T).(pr2 (CHead c0 (Bind b) u0) t1 t3)))))) (\forall (b: B).(\forall (u0: 
T).(pr2 (CHead c0 (Bind b) u0) t1 (lift (S O) O t)))) (\lambda (b: 
B).(\lambda (u0: T).(pr2_delta (CHead c0 (Bind b) u0) d u (S i) (getl_head 
(Bind b) i c0 (CHead d (Bind Abbr) u) H1 u0) t1 (lift (S O) O t2) H6 (lift (S 
O) O t) (subst0_lift_ge_S t2 t u i H3 O (le_O_n i))))))) (pr0_gen_void u1 t1 
t2 H5)))))))))))))) c y x H0))) H))))).

