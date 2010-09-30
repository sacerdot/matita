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

include "Basic-1/nf2/defs.ma".

include "Basic-1/pr2/clen.ma".

include "Basic-1/subst0/dec.ma".

include "Basic-1/T/props.ma".

theorem nf2_gen_lref:
 \forall (c: C).(\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c 
(CHead d (Bind Abbr) u)) \to ((nf2 c (TLRef i)) \to (\forall (P: Prop).P))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead d (Bind Abbr) u))).(\lambda (H0: ((\forall (t2: T).((pr2 
c (TLRef i) t2) \to (eq T (TLRef i) t2))))).(\lambda (P: 
Prop).(lift_gen_lref_false (S i) O i (le_O_n i) (le_n (plus O (S i))) u (H0 
(lift (S i) O u) (pr2_delta c d u i H (TLRef i) (TLRef i) (pr0_refl (TLRef 
i)) (lift (S i) O u) (subst0_lref u i))) P))))))).
(* COMMENTS
Initial nodes: 129
END *)

theorem nf2_gen_abst:
 \forall (c: C).(\forall (u: T).(\forall (t: T).((nf2 c (THead (Bind Abst) u 
t)) \to (land (nf2 c u) (nf2 (CHead c (Bind Abst) u) t)))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: ((\forall (t2: 
T).((pr2 c (THead (Bind Abst) u t) t2) \to (eq T (THead (Bind Abst) u t) 
t2))))).(conj (\forall (t2: T).((pr2 c u t2) \to (eq T u t2))) (\forall (t2: 
T).((pr2 (CHead c (Bind Abst) u) t t2) \to (eq T t t2))) (\lambda (t2: 
T).(\lambda (H0: (pr2 c u t2)).(let H1 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u | 
(TLRef _) \Rightarrow u | (THead _ t0 _) \Rightarrow t0])) (THead (Bind Abst) 
u t) (THead (Bind Abst) t2 t) (H (THead (Bind Abst) t2 t) (pr2_head_1 c u t2 
H0 (Bind Abst) t))) in (let H2 \def (eq_ind_r T t2 (\lambda (t0: T).(pr2 c u 
t0)) H0 u H1) in (eq_ind T u (\lambda (t0: T).(eq T u t0)) (refl_equal T u) 
t2 H1))))) (\lambda (t2: T).(\lambda (H0: (pr2 (CHead c (Bind Abst) u) t 
t2)).(let H1 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda 
(_: T).T) with [(TSort _) \Rightarrow t | (TLRef _) \Rightarrow t | (THead _ 
_ t0) \Rightarrow t0])) (THead (Bind Abst) u t) (THead (Bind Abst) u t2) (H 
(THead (Bind Abst) u t2) (let H_y \def (pr2_gen_cbind Abst c u t t2 H0) in 
H_y))) in (let H2 \def (eq_ind_r T t2 (\lambda (t0: T).(pr2 (CHead c (Bind 
Abst) u) t t0)) H0 t H1) in (eq_ind T t (\lambda (t0: T).(eq T t t0)) 
(refl_equal T t) t2 H1))))))))).
(* COMMENTS
Initial nodes: 353
END *)

theorem nf2_gen_cast:
 \forall (c: C).(\forall (u: T).(\forall (t: T).((nf2 c (THead (Flat Cast) u 
t)) \to (\forall (P: Prop).P))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: (nf2 c (THead 
(Flat Cast) u t))).(\lambda (P: Prop).(thead_x_y_y (Flat Cast) u t (H t 
(pr2_free c (THead (Flat Cast) u t) t (pr0_tau t t (pr0_refl t) u))) P))))).
(* COMMENTS
Initial nodes: 65
END *)

theorem nf2_gen_beta:
 \forall (c: C).(\forall (u: T).(\forall (v: T).(\forall (t: T).((nf2 c 
(THead (Flat Appl) u (THead (Bind Abst) v t))) \to (\forall (P: Prop).P)))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (v: T).(\lambda (t: T).(\lambda (H: 
((\forall (t2: T).((pr2 c (THead (Flat Appl) u (THead (Bind Abst) v t)) t2) 
\to (eq T (THead (Flat Appl) u (THead (Bind Abst) v t)) t2))))).(\lambda (P: 
Prop).(let H0 \def (eq_ind T (THead (Flat Appl) u (THead (Bind Abst) v t)) 
(\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) with [(TSort _) 
\Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow 
(match k in K return (\lambda (_: K).Prop) with [(Bind _) \Rightarrow False | 
(Flat _) \Rightarrow True])])) I (THead (Bind Abbr) u t) (H (THead (Bind 
Abbr) u t) (pr2_free c (THead (Flat Appl) u (THead (Bind Abst) v t)) (THead 
(Bind Abbr) u t) (pr0_beta v u u (pr0_refl u) t t (pr0_refl t))))) in 
(False_ind P H0))))))).
(* COMMENTS
Initial nodes: 183
END *)

theorem nf2_gen_flat:
 \forall (f: F).(\forall (c: C).(\forall (u: T).(\forall (t: T).((nf2 c 
(THead (Flat f) u t)) \to (land (nf2 c u) (nf2 c t))))))
\def
 \lambda (f: F).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: 
((\forall (t2: T).((pr2 c (THead (Flat f) u t) t2) \to (eq T (THead (Flat f) 
u t) t2))))).(conj (\forall (t2: T).((pr2 c u t2) \to (eq T u t2))) (\forall 
(t2: T).((pr2 c t t2) \to (eq T t t2))) (\lambda (t2: T).(\lambda (H0: (pr2 c 
u t2)).(let H1 \def (f_equal T T (\lambda (e: T).(match e in T return 
(\lambda (_: T).T) with [(TSort _) \Rightarrow u | (TLRef _) \Rightarrow u | 
(THead _ t0 _) \Rightarrow t0])) (THead (Flat f) u t) (THead (Flat f) t2 t) 
(H (THead (Flat f) t2 t) (pr2_head_1 c u t2 H0 (Flat f) t))) in H1))) 
(\lambda (t2: T).(\lambda (H0: (pr2 c t t2)).(let H1 \def (f_equal T T 
(\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow t | (TLRef _) \Rightarrow t | (THead _ _ t0) \Rightarrow t0])) 
(THead (Flat f) u t) (THead (Flat f) u t2) (H (THead (Flat f) u t2) 
(pr2_head_2 c u t t2 (Flat f) (pr2_cflat c t t2 H0 f u)))) in H1)))))))).
(* COMMENTS
Initial nodes: 251
END *)

theorem nf2_gen__nf2_gen_aux:
 \forall (b: B).(\forall (x: T).(\forall (u: T).(\forall (d: nat).((eq T 
(THead (Bind b) u (lift (S O) d x)) x) \to (\forall (P: Prop).P)))))
\def
 \lambda (b: B).(\lambda (x: T).(T_ind (\lambda (t: T).(\forall (u: 
T).(\forall (d: nat).((eq T (THead (Bind b) u (lift (S O) d t)) t) \to 
(\forall (P: Prop).P))))) (\lambda (n: nat).(\lambda (u: T).(\lambda (d: 
nat).(\lambda (H: (eq T (THead (Bind b) u (lift (S O) d (TSort n))) (TSort 
n))).(\lambda (P: Prop).(let H0 \def (eq_ind T (THead (Bind b) u (lift (S O) 
d (TSort n))) (\lambda (ee: T).(match ee in T return (\lambda (_: T).Prop) 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead _ _ 
_) \Rightarrow True])) I (TSort n) H) in (False_ind P H0))))))) (\lambda (n: 
nat).(\lambda (u: T).(\lambda (d: nat).(\lambda (H: (eq T (THead (Bind b) u 
(lift (S O) d (TLRef n))) (TLRef n))).(\lambda (P: Prop).(let H0 \def (eq_ind 
T (THead (Bind b) u (lift (S O) d (TLRef n))) (\lambda (ee: T).(match ee in T 
return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TLRef n) H) in 
(False_ind P H0))))))) (\lambda (k: K).(\lambda (t: T).(\lambda (_: ((\forall 
(u: T).(\forall (d: nat).((eq T (THead (Bind b) u (lift (S O) d t)) t) \to 
(\forall (P: Prop).P)))))).(\lambda (t0: T).(\lambda (H0: ((\forall (u: 
T).(\forall (d: nat).((eq T (THead (Bind b) u (lift (S O) d t0)) t0) \to 
(\forall (P: Prop).P)))))).(\lambda (u: T).(\lambda (d: nat).(\lambda (H1: 
(eq T (THead (Bind b) u (lift (S O) d (THead k t t0))) (THead k t 
t0))).(\lambda (P: Prop).(let H2 \def (f_equal T K (\lambda (e: T).(match e 
in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow (Bind b) | (TLRef 
_) \Rightarrow (Bind b) | (THead k0 _ _) \Rightarrow k0])) (THead (Bind b) u 
(lift (S O) d (THead k t t0))) (THead k t t0) H1) in ((let H3 \def (f_equal T 
T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with [(TSort _) 
\Rightarrow u | (TLRef _) \Rightarrow u | (THead _ t1 _) \Rightarrow t1])) 
(THead (Bind b) u (lift (S O) d (THead k t t0))) (THead k t t0) H1) in ((let 
H4 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow (THead k ((let rec lref_map (f: ((nat \to nat))) 
(d0: nat) (t1: T) on t1: T \def (match t1 with [(TSort n) \Rightarrow (TSort 
n) | (TLRef i) \Rightarrow (TLRef (match (blt i d0) with [true \Rightarrow i 
| false \Rightarrow (f i)])) | (THead k0 u0 t2) \Rightarrow (THead k0 
(lref_map f d0 u0) (lref_map f (s k0 d0) t2))]) in lref_map) (\lambda (x0: 
nat).(plus x0 (S O))) d t) ((let rec lref_map (f: ((nat \to nat))) (d0: nat) 
(t1: T) on t1: T \def (match t1 with [(TSort n) \Rightarrow (TSort n) | 
(TLRef i) \Rightarrow (TLRef (match (blt i d0) with [true \Rightarrow i | 
false \Rightarrow (f i)])) | (THead k0 u0 t2) \Rightarrow (THead k0 (lref_map 
f d0 u0) (lref_map f (s k0 d0) t2))]) in lref_map) (\lambda (x0: nat).(plus 
x0 (S O))) (s k d) t0)) | (TLRef _) \Rightarrow (THead k ((let rec lref_map 
(f: ((nat \to nat))) (d0: nat) (t1: T) on t1: T \def (match t1 with [(TSort 
n) \Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d0) 
with [true \Rightarrow i | false \Rightarrow (f i)])) | (THead k0 u0 t2) 
\Rightarrow (THead k0 (lref_map f d0 u0) (lref_map f (s k0 d0) t2))]) in 
lref_map) (\lambda (x0: nat).(plus x0 (S O))) d t) ((let rec lref_map (f: 
((nat \to nat))) (d0: nat) (t1: T) on t1: T \def (match t1 with [(TSort n) 
\Rightarrow (TSort n) | (TLRef i) \Rightarrow (TLRef (match (blt i d0) with 
[true \Rightarrow i | false \Rightarrow (f i)])) | (THead k0 u0 t2) 
\Rightarrow (THead k0 (lref_map f d0 u0) (lref_map f (s k0 d0) t2))]) in 
lref_map) (\lambda (x0: nat).(plus x0 (S O))) (s k d) t0)) | (THead _ _ t1) 
\Rightarrow t1])) (THead (Bind b) u (lift (S O) d (THead k t t0))) (THead k t 
t0) H1) in (\lambda (_: (eq T u t)).(\lambda (H6: (eq K (Bind b) k)).(let H7 
\def (eq_ind_r K k (\lambda (k0: K).(eq T (lift (S O) d (THead k0 t t0)) t0)) 
H4 (Bind b) H6) in (let H8 \def (eq_ind T (lift (S O) d (THead (Bind b) t 
t0)) (\lambda (t1: T).(eq T t1 t0)) H7 (THead (Bind b) (lift (S O) d t) (lift 
(S O) (S d) t0)) (lift_bind b t t0 (S O) d)) in (H0 (lift (S O) d t) (S d) H8 
P)))))) H3)) H2))))))))))) x)).
(* COMMENTS
Initial nodes: 935
END *)

theorem nf2_gen_abbr:
 \forall (c: C).(\forall (u: T).(\forall (t: T).((nf2 c (THead (Bind Abbr) u 
t)) \to (\forall (P: Prop).P))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: ((\forall (t2: 
T).((pr2 c (THead (Bind Abbr) u t) t2) \to (eq T (THead (Bind Abbr) u t) 
t2))))).(\lambda (P: Prop).(let H_x \def (dnf_dec u t O) in (let H0 \def H_x 
in (ex_ind T (\lambda (v: T).(or (subst0 O u t (lift (S O) O v)) (eq T t 
(lift (S O) O v)))) P (\lambda (x: T).(\lambda (H1: (or (subst0 O u t (lift 
(S O) O x)) (eq T t (lift (S O) O x)))).(or_ind (subst0 O u t (lift (S O) O 
x)) (eq T t (lift (S O) O x)) P (\lambda (H2: (subst0 O u t (lift (S O) O 
x))).(let H3 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda 
(_: T).T) with [(TSort _) \Rightarrow t | (TLRef _) \Rightarrow t | (THead _ 
_ t0) \Rightarrow t0])) (THead (Bind Abbr) u t) (THead (Bind Abbr) u (lift (S 
O) O x)) (H (THead (Bind Abbr) u (lift (S O) O x)) (pr2_free c (THead (Bind 
Abbr) u t) (THead (Bind Abbr) u (lift (S O) O x)) (pr0_delta u u (pr0_refl u) 
t t (pr0_refl t) (lift (S O) O x) H2)))) in (let H4 \def (eq_ind T t (\lambda 
(t0: T).(subst0 O u t0 (lift (S O) O x))) H2 (lift (S O) O x) H3) in 
(subst0_refl u (lift (S O) O x) O H4 P)))) (\lambda (H2: (eq T t (lift (S O) 
O x))).(let H3 \def (eq_ind T t (\lambda (t0: T).(\forall (t2: T).((pr2 c 
(THead (Bind Abbr) u t0) t2) \to (eq T (THead (Bind Abbr) u t0) t2)))) H 
(lift (S O) O x) H2) in (nf2_gen__nf2_gen_aux Abbr x u O (H3 x (pr2_free c 
(THead (Bind Abbr) u (lift (S O) O x)) x (pr0_zeta Abbr not_abbr_abst x x 
(pr0_refl x) u))) P))) H1))) H0))))))).
(* COMMENTS
Initial nodes: 511
END *)

theorem nf2_gen_void:
 \forall (c: C).(\forall (u: T).(\forall (t: T).((nf2 c (THead (Bind Void) u 
(lift (S O) O t))) \to (\forall (P: Prop).P))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: ((\forall (t2: 
T).((pr2 c (THead (Bind Void) u (lift (S O) O t)) t2) \to (eq T (THead (Bind 
Void) u (lift (S O) O t)) t2))))).(\lambda (P: Prop).(nf2_gen__nf2_gen_aux 
Void t u O (H t (pr2_free c (THead (Bind Void) u (lift (S O) O t)) t 
(pr0_zeta Void (sym_not_eq B Abst Void not_abst_void) t t (pr0_refl t) u))) 
P))))).
(* COMMENTS
Initial nodes: 121
END *)

