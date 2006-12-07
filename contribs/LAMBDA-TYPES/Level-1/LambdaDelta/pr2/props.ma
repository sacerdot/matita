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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr2/props".

include "pr2/defs.ma".

include "pr0/props.ma".

include "getl/drop.ma".

include "getl/clear.ma".

theorem pr2_thin_dx:
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

theorem pr2_head_1:
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

theorem pr2_head_2:
 \forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall (t2: T).(\forall 
(k: K).((pr2 (CHead c k u) t1 t2) \to (pr2 c (THead k u t1) (THead k u 
t2)))))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(k: K).(K_ind (\lambda (k0: K).((pr2 (CHead c k0 u) t1 t2) \to (pr2 c (THead 
k0 u t1) (THead k0 u t2)))) (\lambda (b: B).(\lambda (H: (pr2 (CHead c (Bind 
b) u) t1 t2)).(let H0 \def (match H in pr2 return (\lambda (c0: C).(\lambda 
(t: T).(\lambda (t0: T).(\lambda (_: (pr2 c0 t t0)).((eq C c0 (CHead c (Bind 
b) u)) \to ((eq T t t1) \to ((eq T t0 t2) \to (pr2 c (THead (Bind b) u t1) 
(THead (Bind b) u t2))))))))) with [(pr2_free c0 t0 t3 H0) \Rightarrow 
(\lambda (H1: (eq C c0 (CHead c (Bind b) u))).(\lambda (H2: (eq T t0 
t1)).(\lambda (H3: (eq T t3 t2)).(eq_ind C (CHead c (Bind b) u) (\lambda (_: 
C).((eq T t0 t1) \to ((eq T t3 t2) \to ((pr0 t0 t3) \to (pr2 c (THead (Bind 
b) u t1) (THead (Bind b) u t2)))))) (\lambda (H4: (eq T t0 t1)).(eq_ind T t1 
(\lambda (t: T).((eq T t3 t2) \to ((pr0 t t3) \to (pr2 c (THead (Bind b) u 
t1) (THead (Bind b) u t2))))) (\lambda (H5: (eq T t3 t2)).(eq_ind T t2 
(\lambda (t: T).((pr0 t1 t) \to (pr2 c (THead (Bind b) u t1) (THead (Bind b) 
u t2)))) (\lambda (H6: (pr0 t1 t2)).(pr2_free c (THead (Bind b) u t1) (THead 
(Bind b) u t2) (pr0_comp u u (pr0_refl u) t1 t2 H6 (Bind b)))) t3 (sym_eq T 
t3 t2 H5))) t0 (sym_eq T t0 t1 H4))) c0 (sym_eq C c0 (CHead c (Bind b) u) H1) 
H2 H3 H0)))) | (pr2_delta c0 d u0 i H0 t0 t3 H1 t H2) \Rightarrow (\lambda 
(H3: (eq C c0 (CHead c (Bind b) u))).(\lambda (H4: (eq T t0 t1)).(\lambda 
(H5: (eq T t t2)).(eq_ind C (CHead c (Bind b) u) (\lambda (c1: C).((eq T t0 
t1) \to ((eq T t t2) \to ((getl i c1 (CHead d (Bind Abbr) u0)) \to ((pr0 t0 
t3) \to ((subst0 i u0 t3 t) \to (pr2 c (THead (Bind b) u t1) (THead (Bind b) 
u t2)))))))) (\lambda (H6: (eq T t0 t1)).(eq_ind T t1 (\lambda (t4: T).((eq T 
t t2) \to ((getl i (CHead c (Bind b) u) (CHead d (Bind Abbr) u0)) \to ((pr0 
t4 t3) \to ((subst0 i u0 t3 t) \to (pr2 c (THead (Bind b) u t1) (THead (Bind 
b) u t2))))))) (\lambda (H7: (eq T t t2)).(eq_ind T t2 (\lambda (t4: 
T).((getl i (CHead c (Bind b) u) (CHead d (Bind Abbr) u0)) \to ((pr0 t1 t3) 
\to ((subst0 i u0 t3 t4) \to (pr2 c (THead (Bind b) u t1) (THead (Bind b) u 
t2)))))) (\lambda (H8: (getl i (CHead c (Bind b) u) (CHead d (Bind Abbr) 
u0))).(\lambda (H9: (pr0 t1 t3)).(\lambda (H10: (subst0 i u0 t3 t2)).(nat_ind 
(\lambda (n: nat).((getl n (CHead c (Bind b) u) (CHead d (Bind Abbr) u0)) \to 
((subst0 n u0 t3 t2) \to (pr2 c (THead (Bind b) u t1) (THead (Bind b) u 
t2))))) (\lambda (H11: (getl O (CHead c (Bind b) u) (CHead d (Bind Abbr) 
u0))).(\lambda (H12: (subst0 O u0 t3 t2)).(let H13 \def (f_equal C C (\lambda 
(e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d 
| (CHead c1 _ _) \Rightarrow c1])) (CHead d (Bind Abbr) u0) (CHead c (Bind b) 
u) (clear_gen_bind b c (CHead d (Bind Abbr) u0) u (getl_gen_O (CHead c (Bind 
b) u) (CHead d (Bind Abbr) u0) H11))) in ((let H14 \def (f_equal C B (\lambda 
(e: C).(match e in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow 
Abbr | (CHead _ k0 _) \Rightarrow (match k0 in K return (\lambda (_: K).B) 
with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) (CHead d 
(Bind Abbr) u0) (CHead c (Bind b) u) (clear_gen_bind b c (CHead d (Bind Abbr) 
u0) u (getl_gen_O (CHead c (Bind b) u) (CHead d (Bind Abbr) u0) H11))) in 
((let H15 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: 
C).T) with [(CSort _) \Rightarrow u0 | (CHead _ _ t4) \Rightarrow t4])) 
(CHead d (Bind Abbr) u0) (CHead c (Bind b) u) (clear_gen_bind b c (CHead d 
(Bind Abbr) u0) u (getl_gen_O (CHead c (Bind b) u) (CHead d (Bind Abbr) u0) 
H11))) in (\lambda (H16: (eq B Abbr b)).(\lambda (_: (eq C d c)).(let H18 
\def (eq_ind T u0 (\lambda (t4: T).(subst0 O t4 t3 t2)) H12 u H15) in (eq_ind 
B Abbr (\lambda (b0: B).(pr2 c (THead (Bind b0) u t1) (THead (Bind b0) u 
t2))) (pr2_free c (THead (Bind Abbr) u t1) (THead (Bind Abbr) u t2) 
(pr0_delta u u (pr0_refl u) t1 t3 H9 t2 H18)) b H16))))) H14)) H13)))) 
(\lambda (i0: nat).(\lambda (_: (((getl i0 (CHead c (Bind b) u) (CHead d 
(Bind Abbr) u0)) \to ((subst0 i0 u0 t3 t2) \to (pr2 c (THead (Bind b) u t1) 
(THead (Bind b) u t2)))))).(\lambda (H11: (getl (S i0) (CHead c (Bind b) u) 
(CHead d (Bind Abbr) u0))).(\lambda (H12: (subst0 (S i0) u0 t3 
t2)).(pr2_delta c d u0 (r (Bind b) i0) (getl_gen_S (Bind b) c (CHead d (Bind 
Abbr) u0) u i0 H11) (THead (Bind b) u t1) (THead (Bind b) u t3) (pr0_comp u u 
(pr0_refl u) t1 t3 H9 (Bind b)) (THead (Bind b) u t2) (subst0_snd (Bind b) u0 
t2 t3 (r (Bind b) i0) H12 u)))))) i H8 H10)))) t (sym_eq T t t2 H7))) t0 
(sym_eq T t0 t1 H6))) c0 (sym_eq C c0 (CHead c (Bind b) u) H3) H4 H5 H0 H1 
H2))))]) in (H0 (refl_equal C (CHead c (Bind b) u)) (refl_equal T t1) 
(refl_equal T t2))))) (\lambda (f: F).(\lambda (H: (pr2 (CHead c (Flat f) u) 
t1 t2)).(let H0 \def (match H in pr2 return (\lambda (c0: C).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (_: (pr2 c0 t t0)).((eq C c0 (CHead c (Flat f) 
u)) \to ((eq T t t1) \to ((eq T t0 t2) \to (pr2 c (THead (Flat f) u t1) 
(THead (Flat f) u t2))))))))) with [(pr2_free c0 t0 t3 H0) \Rightarrow 
(\lambda (H1: (eq C c0 (CHead c (Flat f) u))).(\lambda (H2: (eq T t0 
t1)).(\lambda (H3: (eq T t3 t2)).(eq_ind C (CHead c (Flat f) u) (\lambda (_: 
C).((eq T t0 t1) \to ((eq T t3 t2) \to ((pr0 t0 t3) \to (pr2 c (THead (Flat 
f) u t1) (THead (Flat f) u t2)))))) (\lambda (H4: (eq T t0 t1)).(eq_ind T t1 
(\lambda (t: T).((eq T t3 t2) \to ((pr0 t t3) \to (pr2 c (THead (Flat f) u 
t1) (THead (Flat f) u t2))))) (\lambda (H5: (eq T t3 t2)).(eq_ind T t2 
(\lambda (t: T).((pr0 t1 t) \to (pr2 c (THead (Flat f) u t1) (THead (Flat f) 
u t2)))) (\lambda (H6: (pr0 t1 t2)).(pr2_free c (THead (Flat f) u t1) (THead 
(Flat f) u t2) (pr0_comp u u (pr0_refl u) t1 t2 H6 (Flat f)))) t3 (sym_eq T 
t3 t2 H5))) t0 (sym_eq T t0 t1 H4))) c0 (sym_eq C c0 (CHead c (Flat f) u) H1) 
H2 H3 H0)))) | (pr2_delta c0 d u0 i H0 t0 t3 H1 t H2) \Rightarrow (\lambda 
(H3: (eq C c0 (CHead c (Flat f) u))).(\lambda (H4: (eq T t0 t1)).(\lambda 
(H5: (eq T t t2)).(eq_ind C (CHead c (Flat f) u) (\lambda (c1: C).((eq T t0 
t1) \to ((eq T t t2) \to ((getl i c1 (CHead d (Bind Abbr) u0)) \to ((pr0 t0 
t3) \to ((subst0 i u0 t3 t) \to (pr2 c (THead (Flat f) u t1) (THead (Flat f) 
u t2)))))))) (\lambda (H6: (eq T t0 t1)).(eq_ind T t1 (\lambda (t4: T).((eq T 
t t2) \to ((getl i (CHead c (Flat f) u) (CHead d (Bind Abbr) u0)) \to ((pr0 
t4 t3) \to ((subst0 i u0 t3 t) \to (pr2 c (THead (Flat f) u t1) (THead (Flat 
f) u t2))))))) (\lambda (H7: (eq T t t2)).(eq_ind T t2 (\lambda (t4: 
T).((getl i (CHead c (Flat f) u) (CHead d (Bind Abbr) u0)) \to ((pr0 t1 t3) 
\to ((subst0 i u0 t3 t4) \to (pr2 c (THead (Flat f) u t1) (THead (Flat f) u 
t2)))))) (\lambda (H8: (getl i (CHead c (Flat f) u) (CHead d (Bind Abbr) 
u0))).(\lambda (H9: (pr0 t1 t3)).(\lambda (H10: (subst0 i u0 t3 t2)).(nat_ind 
(\lambda (n: nat).((getl n (CHead c (Flat f) u) (CHead d (Bind Abbr) u0)) \to 
((subst0 n u0 t3 t2) \to (pr2 c (THead (Flat f) u t1) (THead (Flat f) u 
t2))))) (\lambda (H11: (getl O (CHead c (Flat f) u) (CHead d (Bind Abbr) 
u0))).(\lambda (H12: (subst0 O u0 t3 t2)).(pr2_delta c d u0 O (getl_intro O c 
(CHead d (Bind Abbr) u0) c (drop_refl c) (clear_gen_flat f c (CHead d (Bind 
Abbr) u0) u (getl_gen_O (CHead c (Flat f) u) (CHead d (Bind Abbr) u0) H11))) 
(THead (Flat f) u t1) (THead (Flat f) u t3) (pr0_comp u u (pr0_refl u) t1 t3 
H9 (Flat f)) (THead (Flat f) u t2) (subst0_snd (Flat f) u0 t2 t3 O H12 u)))) 
(\lambda (i0: nat).(\lambda (_: (((getl i0 (CHead c (Flat f) u) (CHead d 
(Bind Abbr) u0)) \to ((subst0 i0 u0 t3 t2) \to (pr2 c (THead (Flat f) u t1) 
(THead (Flat f) u t2)))))).(\lambda (H11: (getl (S i0) (CHead c (Flat f) u) 
(CHead d (Bind Abbr) u0))).(\lambda (H12: (subst0 (S i0) u0 t3 
t2)).(pr2_delta c d u0 (r (Flat f) i0) (getl_gen_S (Flat f) c (CHead d (Bind 
Abbr) u0) u i0 H11) (THead (Flat f) u t1) (THead (Flat f) u t3) (pr0_comp u u 
(pr0_refl u) t1 t3 H9 (Flat f)) (THead (Flat f) u t2) (subst0_snd (Flat f) u0 
t2 t3 (r (Flat f) i0) H12 u)))))) i H8 H10)))) t (sym_eq T t t2 H7))) t0 
(sym_eq T t0 t1 H6))) c0 (sym_eq C c0 (CHead c (Flat f) u) H3) H4 H5 H0 H1 
H2))))]) in (H0 (refl_equal C (CHead c (Flat f) u)) (refl_equal T t1) 
(refl_equal T t2))))) k))))).

theorem clear_pr2_trans:
 \forall (c2: C).(\forall (t1: T).(\forall (t2: T).((pr2 c2 t1 t2) \to 
(\forall (c1: C).((clear c1 c2) \to (pr2 c1 t1 t2))))))
\def
 \lambda (c2: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr2 c2 t1 
t2)).(\lambda (c1: C).(\lambda (H0: (clear c1 c2)).(let H1 \def (match H in 
pr2 return (\lambda (c: C).(\lambda (t: T).(\lambda (t0: T).(\lambda (_: (pr2 
c t t0)).((eq C c c2) \to ((eq T t t1) \to ((eq T t0 t2) \to (pr2 c1 t1 
t2)))))))) with [(pr2_free c t0 t3 H1) \Rightarrow (\lambda (H2: (eq C c 
c2)).(\lambda (H3: (eq T t0 t1)).(\lambda (H4: (eq T t3 t2)).(eq_ind C c2 
(\lambda (_: C).((eq T t0 t1) \to ((eq T t3 t2) \to ((pr0 t0 t3) \to (pr2 c1 
t1 t2))))) (\lambda (H5: (eq T t0 t1)).(eq_ind T t1 (\lambda (t: T).((eq T t3 
t2) \to ((pr0 t t3) \to (pr2 c1 t1 t2)))) (\lambda (H6: (eq T t3 t2)).(eq_ind 
T t2 (\lambda (t: T).((pr0 t1 t) \to (pr2 c1 t1 t2))) (\lambda (H7: (pr0 t1 
t2)).(pr2_free c1 t1 t2 H7)) t3 (sym_eq T t3 t2 H6))) t0 (sym_eq T t0 t1 
H5))) c (sym_eq C c c2 H2) H3 H4 H1)))) | (pr2_delta c d u i H1 t0 t3 H2 t 
H3) \Rightarrow (\lambda (H4: (eq C c c2)).(\lambda (H5: (eq T t0 
t1)).(\lambda (H6: (eq T t t2)).(eq_ind C c2 (\lambda (c0: C).((eq T t0 t1) 
\to ((eq T t t2) \to ((getl i c0 (CHead d (Bind Abbr) u)) \to ((pr0 t0 t3) 
\to ((subst0 i u t3 t) \to (pr2 c1 t1 t2))))))) (\lambda (H7: (eq T t0 
t1)).(eq_ind T t1 (\lambda (t4: T).((eq T t t2) \to ((getl i c2 (CHead d 
(Bind Abbr) u)) \to ((pr0 t4 t3) \to ((subst0 i u t3 t) \to (pr2 c1 t1 
t2)))))) (\lambda (H8: (eq T t t2)).(eq_ind T t2 (\lambda (t4: T).((getl i c2 
(CHead d (Bind Abbr) u)) \to ((pr0 t1 t3) \to ((subst0 i u t3 t4) \to (pr2 c1 
t1 t2))))) (\lambda (H9: (getl i c2 (CHead d (Bind Abbr) u))).(\lambda (H10: 
(pr0 t1 t3)).(\lambda (H11: (subst0 i u t3 t2)).(pr2_delta c1 d u i 
(clear_getl_trans i c2 (CHead d (Bind Abbr) u) H9 c1 H0) t1 t3 H10 t2 H11)))) 
t (sym_eq T t t2 H8))) t0 (sym_eq T t0 t1 H7))) c (sym_eq C c c2 H4) H5 H6 H1 
H2 H3))))]) in (H1 (refl_equal C c2) (refl_equal T t1) (refl_equal T 
t2)))))))).

theorem pr2_cflat:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall 
(f: F).(\forall (v: T).(pr2 (CHead c (Flat f) v) t1 t2))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr2 c t1 
t2)).(pr2_ind (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).(\forall (f: 
F).(\forall (v: T).(pr2 (CHead c0 (Flat f) v) t t0)))))) (\lambda (c0: 
C).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H0: (pr0 t3 t4)).(\lambda (f: 
F).(\lambda (v: T).(pr2_free (CHead c0 (Flat f) v) t3 t4 H0))))))) (\lambda 
(c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl 
i c0 (CHead d (Bind Abbr) u))).(\lambda (t3: T).(\lambda (t4: T).(\lambda 
(H1: (pr0 t3 t4)).(\lambda (t: T).(\lambda (H2: (subst0 i u t4 t)).(\lambda 
(f: F).(\lambda (v: T).(pr2_delta (CHead c0 (Flat f) v) d u i (getl_flat c0 
(CHead d (Bind Abbr) u) i H0 f v) t3 t4 H1 t H2))))))))))))) c t1 t2 H)))).

theorem pr2_ctail:
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

theorem pr2_change:
 \forall (b: B).((not (eq B b Abbr)) \to (\forall (c: C).(\forall (v1: 
T).(\forall (t1: T).(\forall (t2: T).((pr2 (CHead c (Bind b) v1) t1 t2) \to 
(\forall (v2: T).(pr2 (CHead c (Bind b) v2) t1 t2))))))))
\def
 \lambda (b: B).(\lambda (H: (not (eq B b Abbr))).(\lambda (c: C).(\lambda 
(v1: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pr2 (CHead c (Bind 
b) v1) t1 t2)).(\lambda (v2: T).(insert_eq C (CHead c (Bind b) v1) (\lambda 
(c0: C).(pr2 c0 t1 t2)) (pr2 (CHead c (Bind b) v2) t1 t2) (\lambda (y: 
C).(\lambda (H1: (pr2 y t1 t2)).(pr2_ind (\lambda (c0: C).(\lambda (t: 
T).(\lambda (t0: T).((eq C c0 (CHead c (Bind b) v1)) \to (pr2 (CHead c (Bind 
b) v2) t t0))))) (\lambda (c0: C).(\lambda (t3: T).(\lambda (t4: T).(\lambda 
(H2: (pr0 t3 t4)).(\lambda (_: (eq C c0 (CHead c (Bind b) v1))).(pr2_free 
(CHead c (Bind b) v2) t3 t4 H2)))))) (\lambda (c0: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H2: (getl i c0 (CHead d (Bind 
Abbr) u))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H3: (pr0 t3 
t4)).(\lambda (t: T).(\lambda (H4: (subst0 i u t4 t)).(\lambda (H5: (eq C c0 
(CHead c (Bind b) v1))).(let H6 \def (eq_ind C c0 (\lambda (c1: C).(getl i c1 
(CHead d (Bind Abbr) u))) H2 (CHead c (Bind b) v1) H5) in (nat_ind (\lambda 
(n: nat).((getl n (CHead c (Bind b) v1) (CHead d (Bind Abbr) u)) \to ((subst0 
n u t4 t) \to (pr2 (CHead c (Bind b) v2) t3 t)))) (\lambda (H7: (getl O 
(CHead c (Bind b) v1) (CHead d (Bind Abbr) u))).(\lambda (H8: (subst0 O u t4 
t)).(let H9 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow d | (CHead c1 _ _) \Rightarrow c1])) 
(CHead d (Bind Abbr) u) (CHead c (Bind b) v1) (clear_gen_bind b c (CHead d 
(Bind Abbr) u) v1 (getl_gen_O (CHead c (Bind b) v1) (CHead d (Bind Abbr) u) 
H7))) in ((let H10 \def (f_equal C B (\lambda (e: C).(match e in C return 
(\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u) 
(CHead c (Bind b) v1) (clear_gen_bind b c (CHead d (Bind Abbr) u) v1 
(getl_gen_O (CHead c (Bind b) v1) (CHead d (Bind Abbr) u) H7))) in ((let H11 
\def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) (CHead d 
(Bind Abbr) u) (CHead c (Bind b) v1) (clear_gen_bind b c (CHead d (Bind Abbr) 
u) v1 (getl_gen_O (CHead c (Bind b) v1) (CHead d (Bind Abbr) u) H7))) in 
(\lambda (H12: (eq B Abbr b)).(\lambda (_: (eq C d c)).(let H14 \def (eq_ind 
T u (\lambda (t0: T).(subst0 O t0 t4 t)) H8 v1 H11) in (let H15 \def 
(eq_ind_r B b (\lambda (b0: B).(not (eq B b0 Abbr))) H Abbr H12) in (eq_ind B 
Abbr (\lambda (b0: B).(pr2 (CHead c (Bind b0) v2) t3 t)) (let H16 \def (match 
(H15 (refl_equal B Abbr)) in False return (\lambda (_: False).(pr2 (CHead c 
(Bind Abbr) v2) t3 t)) with []) in H16) b H12)))))) H10)) H9)))) (\lambda 
(i0: nat).(\lambda (_: (((getl i0 (CHead c (Bind b) v1) (CHead d (Bind Abbr) 
u)) \to ((subst0 i0 u t4 t) \to (pr2 (CHead c (Bind b) v2) t3 t))))).(\lambda 
(H7: (getl (S i0) (CHead c (Bind b) v1) (CHead d (Bind Abbr) u))).(\lambda 
(H8: (subst0 (S i0) u t4 t)).(pr2_delta (CHead c (Bind b) v2) d u (S i0) 
(getl_head (Bind b) i0 c (CHead d (Bind Abbr) u) (getl_gen_S (Bind b) c 
(CHead d (Bind Abbr) u) v1 i0 H7) v2) t3 t4 H3 t H8))))) i H6 H4))))))))))))) 
y t1 t2 H1))) H0)))))))).

theorem pr2_lift:
 \forall (c: C).(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h 
d c e) \to (\forall (t1: T).(\forall (t2: T).((pr2 e t1 t2) \to (pr2 c (lift 
h d t1) (lift h d t2)))))))))
\def
 \lambda (c: C).(\lambda (e: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda 
(H: (drop h d c e)).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pr2 e t1 
t2)).(let H1 \def (match H0 in pr2 return (\lambda (c0: C).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (_: (pr2 c0 t t0)).((eq C c0 e) \to ((eq T t t1) 
\to ((eq T t0 t2) \to (pr2 c (lift h d t1) (lift h d t2))))))))) with 
[(pr2_free c0 t0 t3 H1) \Rightarrow (\lambda (H2: (eq C c0 e)).(\lambda (H3: 
(eq T t0 t1)).(\lambda (H4: (eq T t3 t2)).(eq_ind C e (\lambda (_: C).((eq T 
t0 t1) \to ((eq T t3 t2) \to ((pr0 t0 t3) \to (pr2 c (lift h d t1) (lift h d 
t2)))))) (\lambda (H5: (eq T t0 t1)).(eq_ind T t1 (\lambda (t: T).((eq T t3 
t2) \to ((pr0 t t3) \to (pr2 c (lift h d t1) (lift h d t2))))) (\lambda (H6: 
(eq T t3 t2)).(eq_ind T t2 (\lambda (t: T).((pr0 t1 t) \to (pr2 c (lift h d 
t1) (lift h d t2)))) (\lambda (H7: (pr0 t1 t2)).(pr2_free c (lift h d t1) 
(lift h d t2) (pr0_lift t1 t2 H7 h d))) t3 (sym_eq T t3 t2 H6))) t0 (sym_eq T 
t0 t1 H5))) c0 (sym_eq C c0 e H2) H3 H4 H1)))) | (pr2_delta c0 d0 u i H1 t0 
t3 H2 t H3) \Rightarrow (\lambda (H4: (eq C c0 e)).(\lambda (H5: (eq T t0 
t1)).(\lambda (H6: (eq T t t2)).(eq_ind C e (\lambda (c1: C).((eq T t0 t1) 
\to ((eq T t t2) \to ((getl i c1 (CHead d0 (Bind Abbr) u)) \to ((pr0 t0 t3) 
\to ((subst0 i u t3 t) \to (pr2 c (lift h d t1) (lift h d t2)))))))) (\lambda 
(H7: (eq T t0 t1)).(eq_ind T t1 (\lambda (t4: T).((eq T t t2) \to ((getl i e 
(CHead d0 (Bind Abbr) u)) \to ((pr0 t4 t3) \to ((subst0 i u t3 t) \to (pr2 c 
(lift h d t1) (lift h d t2))))))) (\lambda (H8: (eq T t t2)).(eq_ind T t2 
(\lambda (t4: T).((getl i e (CHead d0 (Bind Abbr) u)) \to ((pr0 t1 t3) \to 
((subst0 i u t3 t4) \to (pr2 c (lift h d t1) (lift h d t2)))))) (\lambda (H9: 
(getl i e (CHead d0 (Bind Abbr) u))).(\lambda (H10: (pr0 t1 t3)).(\lambda 
(H11: (subst0 i u t3 t2)).(lt_le_e i d (pr2 c (lift h d t1) (lift h d t2)) 
(\lambda (H12: (lt i d)).(let H13 \def (drop_getl_trans_le i d (le_S_n i d 
(le_S (S i) d H12)) c e h H (CHead d0 (Bind Abbr) u) H9) in (ex3_2_ind C C 
(\lambda (e0: C).(\lambda (_: C).(drop i O c e0))) (\lambda (e0: C).(\lambda 
(e1: C).(drop h (minus d i) e0 e1))) (\lambda (_: C).(\lambda (e1: C).(clear 
e1 (CHead d0 (Bind Abbr) u)))) (pr2 c (lift h d t1) (lift h d t2)) (\lambda 
(x0: C).(\lambda (x1: C).(\lambda (H14: (drop i O c x0)).(\lambda (H15: (drop 
h (minus d i) x0 x1)).(\lambda (H16: (clear x1 (CHead d0 (Bind Abbr) 
u))).(let H17 \def (eq_ind nat (minus d i) (\lambda (n: nat).(drop h n x0 
x1)) H15 (S (minus d (S i))) (minus_x_Sy d i H12)) in (let H18 \def 
(drop_clear_S x1 x0 h (minus d (S i)) H17 Abbr d0 u H16) in (ex2_ind C 
(\lambda (c1: C).(clear x0 (CHead c1 (Bind Abbr) (lift h (minus d (S i)) 
u)))) (\lambda (c1: C).(drop h (minus d (S i)) c1 d0)) (pr2 c (lift h d t1) 
(lift h d t2)) (\lambda (x: C).(\lambda (H19: (clear x0 (CHead x (Bind Abbr) 
(lift h (minus d (S i)) u)))).(\lambda (_: (drop h (minus d (S i)) x 
d0)).(pr2_delta c x (lift h (minus d (S i)) u) i (getl_intro i c (CHead x 
(Bind Abbr) (lift h (minus d (S i)) u)) x0 H14 H19) (lift h d t1) (lift h d 
t3) (pr0_lift t1 t3 H10 h d) (lift h d t2) (subst0_lift_lt t3 t2 u i H11 d 
H12 h))))) H18)))))))) H13))) (\lambda (H12: (le d i)).(pr2_delta c d0 u 
(plus i h) (drop_getl_trans_ge i c e d h H (CHead d0 (Bind Abbr) u) H9 H12) 
(lift h d t1) (lift h d t3) (pr0_lift t1 t3 H10 h d) (lift h d t2) 
(subst0_lift_ge t3 t2 u i h H11 d H12))))))) t (sym_eq T t t2 H8))) t0 
(sym_eq T t0 t1 H7))) c0 (sym_eq C c0 e H4) H5 H6 H1 H2 H3))))]) in (H1 
(refl_equal C e) (refl_equal T t1) (refl_equal T t2)))))))))).

