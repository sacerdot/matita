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

include "basic_1/nf2/defs.ma".

include "basic_1/pr2/clen.ma".

include "basic_1/subst0/dec.ma".

include "basic_1/T/props.ma".

theorem nf2_gen_lref:
 \forall (c: C).(\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c 
(CHead d (Bind Abbr) u)) \to ((nf2 c (TLRef i)) \to (\forall (P: Prop).P))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead d (Bind Abbr) u))).(\lambda (H0: ((\forall (t2: T).((pr2 
c (TLRef i) t2) \to (eq T (TLRef i) t2))))).(\lambda (P: Prop).(let TMP_1 
\def (S i) in (let TMP_2 \def (le_O_n i) in (let TMP_3 \def (S i) in (let 
TMP_4 \def (plus O TMP_3) in (let TMP_5 \def (le_n TMP_4) in (let TMP_6 \def 
(S i) in (let TMP_7 \def (lift TMP_6 O u) in (let TMP_8 \def (TLRef i) in 
(let TMP_9 \def (TLRef i) in (let TMP_10 \def (TLRef i) in (let TMP_11 \def 
(pr0_refl TMP_10) in (let TMP_12 \def (S i) in (let TMP_13 \def (lift TMP_12 
O u) in (let TMP_14 \def (subst0_lref u i) in (let TMP_15 \def (pr2_delta c d 
u i H TMP_8 TMP_9 TMP_11 TMP_13 TMP_14) in (let TMP_16 \def (H0 TMP_7 TMP_15) 
in (lift_gen_lref_false TMP_1 O i TMP_2 TMP_5 u TMP_16 
P))))))))))))))))))))))).

theorem nf2_gen_abst:
 \forall (c: C).(\forall (u: T).(\forall (t: T).((nf2 c (THead (Bind Abst) u 
t)) \to (land (nf2 c u) (nf2 (CHead c (Bind Abst) u) t)))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: ((\forall (t2: 
T).((pr2 c (THead (Bind Abst) u t) t2) \to (eq T (THead (Bind Abst) u t) 
t2))))).(let TMP_1 \def (\forall (t2: T).((pr2 c u t2) \to (eq T u t2))) in 
(let TMP_2 \def (\forall (t2: T).((pr2 (CHead c (Bind Abst) u) t t2) \to (eq 
T t t2))) in (let TMP_16 \def (\lambda (t2: T).(\lambda (H0: (pr2 c u 
t2)).(let TMP_3 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow u | 
(TLRef _) \Rightarrow u | (THead _ t0 _) \Rightarrow t0])) in (let TMP_4 \def 
(Bind Abst) in (let TMP_5 \def (THead TMP_4 u t) in (let TMP_6 \def (Bind 
Abst) in (let TMP_7 \def (THead TMP_6 t2 t) in (let TMP_8 \def (Bind Abst) in 
(let TMP_9 \def (THead TMP_8 t2 t) in (let TMP_10 \def (Bind Abst) in (let 
TMP_11 \def (pr2_head_1 c u t2 H0 TMP_10 t) in (let TMP_12 \def (H TMP_9 
TMP_11) in (let H1 \def (f_equal T T TMP_3 TMP_5 TMP_7 TMP_12) in (let TMP_13 
\def (\lambda (t0: T).(pr2 c u t0)) in (let H2 \def (eq_ind_r T t2 TMP_13 H0 
u H1) in (let TMP_14 \def (\lambda (t0: T).(eq T u t0)) in (let TMP_15 \def 
(refl_equal T u) in (eq_ind T u TMP_14 TMP_15 t2 H1)))))))))))))))))) in (let 
TMP_30 \def (\lambda (t2: T).(\lambda (H0: (pr2 (CHead c (Bind Abst) u) t 
t2)).(let TMP_17 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow t 
| (TLRef _) \Rightarrow t | (THead _ _ t0) \Rightarrow t0])) in (let TMP_18 
\def (Bind Abst) in (let TMP_19 \def (THead TMP_18 u t) in (let TMP_20 \def 
(Bind Abst) in (let TMP_21 \def (THead TMP_20 u t2) in (let TMP_22 \def (Bind 
Abst) in (let TMP_23 \def (THead TMP_22 u t2) in (let H_y \def (pr2_gen_cbind 
Abst c u t t2 H0) in (let TMP_24 \def (H TMP_23 H_y) in (let H1 \def (f_equal 
T T TMP_17 TMP_19 TMP_21 TMP_24) in (let TMP_27 \def (\lambda (t0: T).(let 
TMP_25 \def (Bind Abst) in (let TMP_26 \def (CHead c TMP_25 u) in (pr2 TMP_26 
t t0)))) in (let H2 \def (eq_ind_r T t2 TMP_27 H0 t H1) in (let TMP_28 \def 
(\lambda (t0: T).(eq T t t0)) in (let TMP_29 \def (refl_equal T t) in (eq_ind 
T t TMP_28 TMP_29 t2 H1))))))))))))))))) in (conj TMP_1 TMP_2 TMP_16 
TMP_30)))))))).

theorem nf2_gen_cast:
 \forall (c: C).(\forall (u: T).(\forall (t: T).((nf2 c (THead (Flat Cast) u 
t)) \to (\forall (P: Prop).P))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: (nf2 c (THead 
(Flat Cast) u t))).(\lambda (P: Prop).(let TMP_1 \def (Flat Cast) in (let 
TMP_2 \def (Flat Cast) in (let TMP_3 \def (THead TMP_2 u t) in (let TMP_4 
\def (pr0_refl t) in (let TMP_5 \def (pr0_tau t t TMP_4 u) in (let TMP_6 \def 
(pr2_free c TMP_3 t TMP_5) in (let TMP_7 \def (H t TMP_6) in (thead_x_y_y 
TMP_1 u t TMP_7 P)))))))))))).

theorem nf2_gen_beta:
 \forall (c: C).(\forall (u: T).(\forall (v: T).(\forall (t: T).((nf2 c 
(THead (Flat Appl) u (THead (Bind Abst) v t))) \to (\forall (P: Prop).P)))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (v: T).(\lambda (t: T).(\lambda (H: 
((\forall (t2: T).((pr2 c (THead (Flat Appl) u (THead (Bind Abst) v t)) t2) 
\to (eq T (THead (Flat Appl) u (THead (Bind Abst) v t)) t2))))).(\lambda (P: 
Prop).(let TMP_1 \def (Flat Appl) in (let TMP_2 \def (Bind Abst) in (let 
TMP_3 \def (THead TMP_2 v t) in (let TMP_4 \def (THead TMP_1 u TMP_3) in (let 
TMP_5 \def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k with [(Bind 
_) \Rightarrow False | (Flat _) \Rightarrow True])])) in (let TMP_6 \def 
(Bind Abbr) in (let TMP_7 \def (THead TMP_6 u t) in (let TMP_8 \def (Bind 
Abbr) in (let TMP_9 \def (THead TMP_8 u t) in (let TMP_10 \def (Flat Appl) in 
(let TMP_11 \def (Bind Abst) in (let TMP_12 \def (THead TMP_11 v t) in (let 
TMP_13 \def (THead TMP_10 u TMP_12) in (let TMP_14 \def (Bind Abbr) in (let 
TMP_15 \def (THead TMP_14 u t) in (let TMP_16 \def (pr0_refl u) in (let 
TMP_17 \def (pr0_refl t) in (let TMP_18 \def (pr0_beta v u u TMP_16 t t 
TMP_17) in (let TMP_19 \def (pr2_free c TMP_13 TMP_15 TMP_18) in (let TMP_20 
\def (H TMP_9 TMP_19) in (let H0 \def (eq_ind T TMP_4 TMP_5 I TMP_7 TMP_20) 
in (False_ind P H0))))))))))))))))))))))))))).

theorem nf2_gen_flat:
 \forall (f: F).(\forall (c: C).(\forall (u: T).(\forall (t: T).((nf2 c 
(THead (Flat f) u t)) \to (land (nf2 c u) (nf2 c t))))))
\def
 \lambda (f: F).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: 
((\forall (t2: T).((pr2 c (THead (Flat f) u t) t2) \to (eq T (THead (Flat f) 
u t) t2))))).(let TMP_1 \def (\forall (t2: T).((pr2 c u t2) \to (eq T u t2))) 
in (let TMP_2 \def (\forall (t2: T).((pr2 c t t2) \to (eq T t t2))) in (let 
TMP_13 \def (\lambda (t2: T).(\lambda (H0: (pr2 c u t2)).(let TMP_3 \def 
(\lambda (e: T).(match e with [(TSort _) \Rightarrow u | (TLRef _) 
\Rightarrow u | (THead _ t0 _) \Rightarrow t0])) in (let TMP_4 \def (Flat f) 
in (let TMP_5 \def (THead TMP_4 u t) in (let TMP_6 \def (Flat f) in (let 
TMP_7 \def (THead TMP_6 t2 t) in (let TMP_8 \def (Flat f) in (let TMP_9 \def 
(THead TMP_8 t2 t) in (let TMP_10 \def (Flat f) in (let TMP_11 \def 
(pr2_head_1 c u t2 H0 TMP_10 t) in (let TMP_12 \def (H TMP_9 TMP_11) in (let 
H1 \def (f_equal T T TMP_3 TMP_5 TMP_7 TMP_12) in H1))))))))))))) in (let 
TMP_25 \def (\lambda (t2: T).(\lambda (H0: (pr2 c t t2)).(let TMP_14 \def 
(\lambda (e: T).(match e with [(TSort _) \Rightarrow t | (TLRef _) 
\Rightarrow t | (THead _ _ t0) \Rightarrow t0])) in (let TMP_15 \def (Flat f) 
in (let TMP_16 \def (THead TMP_15 u t) in (let TMP_17 \def (Flat f) in (let 
TMP_18 \def (THead TMP_17 u t2) in (let TMP_19 \def (Flat f) in (let TMP_20 
\def (THead TMP_19 u t2) in (let TMP_21 \def (Flat f) in (let TMP_22 \def 
(pr2_cflat c t t2 H0 f u) in (let TMP_23 \def (pr2_head_2 c u t t2 TMP_21 
TMP_22) in (let TMP_24 \def (H TMP_20 TMP_23) in (let H1 \def (f_equal T T 
TMP_14 TMP_16 TMP_18 TMP_24) in H1)))))))))))))) in (conj TMP_1 TMP_2 TMP_13 
TMP_25))))))))).

theorem nf2_gen__nf2_gen_aux:
 \forall (b: B).(\forall (x: T).(\forall (u: T).(\forall (d: nat).((eq T 
(THead (Bind b) u (lift (S O) d x)) x) \to (\forall (P: Prop).P)))))
\def
 \lambda (b: B).(\lambda (x: T).(let TMP_1 \def (\lambda (t: T).(\forall (u: 
T).(\forall (d: nat).((eq T (THead (Bind b) u (lift (S O) d t)) t) \to 
(\forall (P: Prop).P))))) in (let TMP_9 \def (\lambda (n: nat).(\lambda (u: 
T).(\lambda (d: nat).(\lambda (H: (eq T (THead (Bind b) u (lift (S O) d 
(TSort n))) (TSort n))).(\lambda (P: Prop).(let TMP_2 \def (Bind b) in (let 
TMP_3 \def (S O) in (let TMP_4 \def (TSort n) in (let TMP_5 \def (lift TMP_3 
d TMP_4) in (let TMP_6 \def (THead TMP_2 u TMP_5) in (let TMP_7 \def (\lambda 
(ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow 
False | (THead _ _ _) \Rightarrow True])) in (let TMP_8 \def (TSort n) in 
(let H0 \def (eq_ind T TMP_6 TMP_7 I TMP_8 H) in (False_ind P 
H0)))))))))))))) in (let TMP_17 \def (\lambda (n: nat).(\lambda (u: 
T).(\lambda (d: nat).(\lambda (H: (eq T (THead (Bind b) u (lift (S O) d 
(TLRef n))) (TLRef n))).(\lambda (P: Prop).(let TMP_10 \def (Bind b) in (let 
TMP_11 \def (S O) in (let TMP_12 \def (TLRef n) in (let TMP_13 \def (lift 
TMP_11 d TMP_12) in (let TMP_14 \def (THead TMP_10 u TMP_13) in (let TMP_15 
\def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow True])) in (let TMP_16 \def 
(TLRef n) in (let H0 \def (eq_ind T TMP_14 TMP_15 I TMP_16 H) in (False_ind P 
H0)))))))))))))) in (let TMP_97 \def (\lambda (k: K).(\lambda (t: T).(\lambda 
(_: ((\forall (u: T).(\forall (d: nat).((eq T (THead (Bind b) u (lift (S O) d 
t)) t) \to (\forall (P: Prop).P)))))).(\lambda (t0: T).(\lambda (H0: 
((\forall (u: T).(\forall (d: nat).((eq T (THead (Bind b) u (lift (S O) d 
t0)) t0) \to (\forall (P: Prop).P)))))).(\lambda (u: T).(\lambda (d: 
nat).(\lambda (H1: (eq T (THead (Bind b) u (lift (S O) d (THead k t t0))) 
(THead k t t0))).(\lambda (P: Prop).(let TMP_18 \def (\lambda (e: T).(match e 
with [(TSort _) \Rightarrow (Bind b) | (TLRef _) \Rightarrow (Bind b) | 
(THead k0 _ _) \Rightarrow k0])) in (let TMP_19 \def (Bind b) in (let TMP_20 
\def (S O) in (let TMP_21 \def (THead k t t0) in (let TMP_22 \def (lift 
TMP_20 d TMP_21) in (let TMP_23 \def (THead TMP_19 u TMP_22) in (let TMP_24 
\def (THead k t t0) in (let H2 \def (f_equal T K TMP_18 TMP_23 TMP_24 H1) in 
(let TMP_25 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow u | 
(TLRef _) \Rightarrow u | (THead _ t1 _) \Rightarrow t1])) in (let TMP_26 
\def (Bind b) in (let TMP_27 \def (S O) in (let TMP_28 \def (THead k t t0) in 
(let TMP_29 \def (lift TMP_27 d TMP_28) in (let TMP_30 \def (THead TMP_26 u 
TMP_29) in (let TMP_31 \def (THead k t t0) in (let H3 \def (f_equal T T 
TMP_25 TMP_30 TMP_31 H1) in (let TMP_66 \def (\lambda (e: T).(match e with 
[(TSort _) \Rightarrow (let TMP_55 \def (\lambda (x0: nat).(let TMP_54 \def 
(S O) in (plus x0 TMP_54))) in (let TMP_56 \def (lref_map TMP_55 d t) in (let 
TMP_63 \def (\lambda (x0: nat).(let TMP_62 \def (S O) in (plus x0 TMP_62))) 
in (let TMP_64 \def (s k d) in (let TMP_65 \def (lref_map TMP_63 TMP_64 t0) 
in (THead k TMP_56 TMP_65)))))) | (TLRef _) \Rightarrow (let TMP_38 \def 
(\lambda (x0: nat).(let TMP_37 \def (S O) in (plus x0 TMP_37))) in (let 
TMP_39 \def (lref_map TMP_38 d t) in (let TMP_46 \def (\lambda (x0: nat).(let 
TMP_45 \def (S O) in (plus x0 TMP_45))) in (let TMP_47 \def (s k d) in (let 
TMP_48 \def (lref_map TMP_46 TMP_47 t0) in (THead k TMP_39 TMP_48)))))) | 
(THead _ _ t1) \Rightarrow t1])) in (let TMP_67 \def (Bind b) in (let TMP_68 
\def (S O) in (let TMP_69 \def (THead k t t0) in (let TMP_70 \def (lift 
TMP_68 d TMP_69) in (let TMP_71 \def (THead TMP_67 u TMP_70) in (let TMP_72 
\def (THead k t t0) in (let H4 \def (f_equal T T TMP_66 TMP_71 TMP_72 H1) in 
(let TMP_95 \def (\lambda (_: (eq T u t)).(\lambda (H6: (eq K (Bind b) 
k)).(let TMP_76 \def (\lambda (k0: K).(let TMP_73 \def (S O) in (let TMP_74 
\def (THead k0 t t0) in (let TMP_75 \def (lift TMP_73 d TMP_74) in (eq T 
TMP_75 t0))))) in (let TMP_77 \def (Bind b) in (let H7 \def (eq_ind_r K k 
TMP_76 H4 TMP_77 H6) in (let TMP_78 \def (S O) in (let TMP_79 \def (Bind b) 
in (let TMP_80 \def (THead TMP_79 t t0) in (let TMP_81 \def (lift TMP_78 d 
TMP_80) in (let TMP_82 \def (\lambda (t1: T).(eq T t1 t0)) in (let TMP_83 
\def (Bind b) in (let TMP_84 \def (S O) in (let TMP_85 \def (lift TMP_84 d t) 
in (let TMP_86 \def (S O) in (let TMP_87 \def (S d) in (let TMP_88 \def (lift 
TMP_86 TMP_87 t0) in (let TMP_89 \def (THead TMP_83 TMP_85 TMP_88) in (let 
TMP_90 \def (S O) in (let TMP_91 \def (lift_bind b t t0 TMP_90 d) in (let H8 
\def (eq_ind T TMP_81 TMP_82 H7 TMP_89 TMP_91) in (let TMP_92 \def (S O) in 
(let TMP_93 \def (lift TMP_92 d t) in (let TMP_94 \def (S d) in (H0 TMP_93 
TMP_94 H8 P)))))))))))))))))))))))) in (let TMP_96 \def (TMP_95 H3) in 
(TMP_96 H2)))))))))))))))))))))))))))))))))))) in (T_ind TMP_1 TMP_9 TMP_17 
TMP_97 x)))))).

theorem nf2_gen_abbr:
 \forall (c: C).(\forall (u: T).(\forall (t: T).((nf2 c (THead (Bind Abbr) u 
t)) \to (\forall (P: Prop).P))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: ((\forall (t2: 
T).((pr2 c (THead (Bind Abbr) u t) t2) \to (eq T (THead (Bind Abbr) u t) 
t2))))).(\lambda (P: Prop).(let H_x \def (dnf_dec u t O) in (let H0 \def H_x 
in (let TMP_7 \def (\lambda (v: T).(let TMP_1 \def (S O) in (let TMP_2 \def 
(lift TMP_1 O v) in (let TMP_3 \def (subst0 O u t TMP_2) in (let TMP_4 \def 
(S O) in (let TMP_5 \def (lift TMP_4 O v) in (let TMP_6 \def (eq T t TMP_5) 
in (or TMP_3 TMP_6)))))))) in (let TMP_60 \def (\lambda (x: T).(\lambda (H1: 
(or (subst0 O u t (lift (S O) O x)) (eq T t (lift (S O) O x)))).(let TMP_8 
\def (S O) in (let TMP_9 \def (lift TMP_8 O x) in (let TMP_10 \def (subst0 O 
u t TMP_9) in (let TMP_11 \def (S O) in (let TMP_12 \def (lift TMP_11 O x) in 
(let TMP_13 \def (eq T t TMP_12) in (let TMP_45 \def (\lambda (H2: (subst0 O 
u t (lift (S O) O x))).(let TMP_14 \def (\lambda (e: T).(match e with [(TSort 
_) \Rightarrow t | (TLRef _) \Rightarrow t | (THead _ _ t0) \Rightarrow t0])) 
in (let TMP_15 \def (Bind Abbr) in (let TMP_16 \def (THead TMP_15 u t) in 
(let TMP_17 \def (Bind Abbr) in (let TMP_18 \def (S O) in (let TMP_19 \def 
(lift TMP_18 O x) in (let TMP_20 \def (THead TMP_17 u TMP_19) in (let TMP_21 
\def (Bind Abbr) in (let TMP_22 \def (S O) in (let TMP_23 \def (lift TMP_22 O 
x) in (let TMP_24 \def (THead TMP_21 u TMP_23) in (let TMP_25 \def (Bind 
Abbr) in (let TMP_26 \def (THead TMP_25 u t) in (let TMP_27 \def (Bind Abbr) 
in (let TMP_28 \def (S O) in (let TMP_29 \def (lift TMP_28 O x) in (let 
TMP_30 \def (THead TMP_27 u TMP_29) in (let TMP_31 \def (pr0_refl u) in (let 
TMP_32 \def (pr0_refl t) in (let TMP_33 \def (S O) in (let TMP_34 \def (lift 
TMP_33 O x) in (let TMP_35 \def (pr0_delta u u TMP_31 t t TMP_32 TMP_34 H2) 
in (let TMP_36 \def (pr2_free c TMP_26 TMP_30 TMP_35) in (let TMP_37 \def (H 
TMP_24 TMP_36) in (let H3 \def (f_equal T T TMP_14 TMP_16 TMP_20 TMP_37) in 
(let TMP_40 \def (\lambda (t0: T).(let TMP_38 \def (S O) in (let TMP_39 \def 
(lift TMP_38 O x) in (subst0 O u t0 TMP_39)))) in (let TMP_41 \def (S O) in 
(let TMP_42 \def (lift TMP_41 O x) in (let H4 \def (eq_ind T t TMP_40 H2 
TMP_42 H3) in (let TMP_43 \def (S O) in (let TMP_44 \def (lift TMP_43 O x) in 
(subst0_refl u TMP_44 O H4 P))))))))))))))))))))))))))))))))) in (let TMP_59 
\def (\lambda (H2: (eq T t (lift (S O) O x))).(let TMP_48 \def (\lambda (t0: 
T).(\forall (t2: T).((pr2 c (THead (Bind Abbr) u t0) t2) \to (let TMP_46 \def 
(Bind Abbr) in (let TMP_47 \def (THead TMP_46 u t0) in (eq T TMP_47 t2)))))) 
in (let TMP_49 \def (S O) in (let TMP_50 \def (lift TMP_49 O x) in (let H3 
\def (eq_ind T t TMP_48 H TMP_50 H2) in (let TMP_51 \def (Bind Abbr) in (let 
TMP_52 \def (S O) in (let TMP_53 \def (lift TMP_52 O x) in (let TMP_54 \def 
(THead TMP_51 u TMP_53) in (let TMP_55 \def (pr0_refl x) in (let TMP_56 \def 
(pr0_zeta Abbr not_abbr_abst x x TMP_55 u) in (let TMP_57 \def (pr2_free c 
TMP_54 x TMP_56) in (let TMP_58 \def (H3 x TMP_57) in (nf2_gen__nf2_gen_aux 
Abbr x u O TMP_58 P)))))))))))))) in (or_ind TMP_10 TMP_13 P TMP_45 TMP_59 
H1))))))))))) in (ex_ind T TMP_7 P TMP_60 H0))))))))).

theorem nf2_gen_void:
 \forall (c: C).(\forall (u: T).(\forall (t: T).((nf2 c (THead (Bind Void) u 
(lift (S O) O t))) \to (\forall (P: Prop).P))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: ((\forall (t2: 
T).((pr2 c (THead (Bind Void) u (lift (S O) O t)) t2) \to (eq T (THead (Bind 
Void) u (lift (S O) O t)) t2))))).(\lambda (P: Prop).(let TMP_1 \def (Bind 
Void) in (let TMP_2 \def (S O) in (let TMP_3 \def (lift TMP_2 O t) in (let 
TMP_4 \def (THead TMP_1 u TMP_3) in (let TMP_5 \def (pr0_refl t) in (let 
TMP_6 \def (pr0_zeta Void not_void_abst t t TMP_5 u) in (let TMP_7 \def 
(pr2_free c TMP_4 t TMP_6) in (let TMP_8 \def (H t TMP_7) in 
(nf2_gen__nf2_gen_aux Void t u O TMP_8 P))))))))))))).

