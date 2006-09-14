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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/nf2/fwd".

include "nf2/defs.ma".

include "pr2/clen.ma".

theorem nf2_gen_base__aux:
 \forall (k: K).(\forall (t: T).(\forall (u: T).((eq T (THead k u t) t) \to 
(\forall (P: Prop).P))))
\def
 \lambda (k: K).(\lambda (t: T).(T_ind (\lambda (t0: T).(\forall (u: T).((eq 
T (THead k u t0) t0) \to (\forall (P: Prop).P)))) (\lambda (n: nat).(\lambda 
(u: T).(\lambda (H: (eq T (THead k u (TSort n)) (TSort n))).(\lambda (P: 
Prop).(let H0 \def (eq_ind T (THead k u (TSort n)) (\lambda (ee: T).(match ee 
in T return (\lambda (_: T).Prop) with [(TSort _) \Rightarrow False | (TLRef 
_) \Rightarrow False | (THead _ _ _) \Rightarrow True])) I (TSort n) H) in 
(False_ind P H0)))))) (\lambda (n: nat).(\lambda (u: T).(\lambda (H: (eq T 
(THead k u (TLRef n)) (TLRef n))).(\lambda (P: Prop).(let H0 \def (eq_ind T 
(THead k u (TLRef n)) (\lambda (ee: T).(match ee in T return (\lambda (_: 
T).Prop) with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | 
(THead _ _ _) \Rightarrow True])) I (TLRef n) H) in (False_ind P H0)))))) 
(\lambda (k0: K).(\lambda (t0: T).(\lambda (_: ((\forall (u: T).((eq T (THead 
k u t0) t0) \to (\forall (P: Prop).P))))).(\lambda (t1: T).(\lambda (H0: 
((\forall (u: T).((eq T (THead k u t1) t1) \to (\forall (P: 
Prop).P))))).(\lambda (u: T).(\lambda (H1: (eq T (THead k u (THead k0 t0 t1)) 
(THead k0 t0 t1))).(\lambda (P: Prop).(let H2 \def (f_equal T K (\lambda (e: 
T).(match e in T return (\lambda (_: T).K) with [(TSort _) \Rightarrow k | 
(TLRef _) \Rightarrow k | (THead k1 _ _) \Rightarrow k1])) (THead k u (THead 
k0 t0 t1)) (THead k0 t0 t1) H1) in ((let H3 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow u | 
(TLRef _) \Rightarrow u | (THead _ t2 _) \Rightarrow t2])) (THead k u (THead 
k0 t0 t1)) (THead k0 t0 t1) H1) in ((let H4 \def (f_equal T T (\lambda (e: 
T).(match e in T return (\lambda (_: T).T) with [(TSort _) \Rightarrow (THead 
k0 t0 t1) | (TLRef _) \Rightarrow (THead k0 t0 t1) | (THead _ _ t2) 
\Rightarrow t2])) (THead k u (THead k0 t0 t1)) (THead k0 t0 t1) H1) in 
(\lambda (_: (eq T u t0)).(\lambda (H6: (eq K k k0)).(let H7 \def (eq_ind K k 
(\lambda (k1: K).(\forall (u0: T).((eq T (THead k1 u0 t1) t1) \to (\forall 
(P0: Prop).P0)))) H0 k0 H6) in (H7 t0 H4 P))))) H3)) H2)))))))))) t)).

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

theorem nf2_gen_cast:
 \forall (c: C).(\forall (u: T).(\forall (t: T).((nf2 c (THead (Flat Cast) u 
t)) \to (\forall (P: Prop).P))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: (nf2 c (THead 
(Flat Cast) u t))).(\lambda (P: Prop).(nf2_gen_base__aux (Flat Cast) t u (H t 
(pr2_free c (THead (Flat Cast) u t) t (pr0_epsilon t t (pr0_refl t) u))) 
P))))).

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

