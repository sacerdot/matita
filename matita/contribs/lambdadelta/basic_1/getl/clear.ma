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

include "basic_1/getl/props.ma".

include "basic_1/clear/drop.ma".

theorem clear_getl_trans:
 \forall (i: nat).(\forall (c2: C).(\forall (c3: C).((getl i c2 c3) \to 
(\forall (c1: C).((clear c1 c2) \to (getl i c1 c3))))))
\def
 \lambda (i: nat).(let TMP_1 \def (\lambda (n: nat).(\forall (c2: C).(\forall 
(c3: C).((getl n c2 c3) \to (\forall (c1: C).((clear c1 c2) \to (getl n c1 
c3))))))) in (let TMP_5 \def (\lambda (c2: C).(\lambda (c3: C).(\lambda (H: 
(getl O c2 c3)).(\lambda (c1: C).(\lambda (H0: (clear c1 c2)).(let TMP_2 \def 
(drop_refl c1) in (let TMP_3 \def (getl_gen_O c2 c3 H) in (let TMP_4 \def 
(clear_trans c1 c2 H0 c3 TMP_3) in (getl_intro O c1 c3 c1 TMP_2 
TMP_4))))))))) in (let TMP_30 \def (\lambda (n: nat).(\lambda (_: ((\forall 
(c2: C).(\forall (c3: C).((getl n c2 c3) \to (\forall (c1: C).((clear c1 c2) 
\to (getl n c1 c3)))))))).(\lambda (c2: C).(let TMP_7 \def (\lambda (c: 
C).(\forall (c3: C).((getl (S n) c c3) \to (\forall (c1: C).((clear c1 c) \to 
(let TMP_6 \def (S n) in (getl TMP_6 c1 c3))))))) in (let TMP_11 \def 
(\lambda (n0: nat).(\lambda (c3: C).(\lambda (H0: (getl (S n) (CSort n0) 
c3)).(\lambda (c1: C).(\lambda (_: (clear c1 (CSort n0))).(let TMP_8 \def (S 
n) in (let TMP_9 \def (S n) in (let TMP_10 \def (getl TMP_9 c1 c3) in 
(getl_gen_sort n0 TMP_8 c3 H0 TMP_10))))))))) in (let TMP_29 \def (\lambda 
(c: C).(\lambda (_: ((\forall (c3: C).((getl (S n) c c3) \to (\forall (c1: 
C).((clear c1 c) \to (getl (S n) c1 c3))))))).(\lambda (k: K).(\lambda (t: 
T).(\lambda (c3: C).(\lambda (H1: (getl (S n) (CHead c k t) c3)).(\lambda 
(c1: C).(\lambda (H2: (clear c1 (CHead c k t))).(let TMP_13 \def (\lambda 
(k0: K).((getl (S n) (CHead c k0 t) c3) \to ((clear c1 (CHead c k0 t)) \to 
(let TMP_12 \def (S n) in (getl TMP_12 c1 c3))))) in (let TMP_25 \def 
(\lambda (b: B).(\lambda (H3: (getl (S n) (CHead c (Bind b) t) c3)).(\lambda 
(H4: (clear c1 (CHead c (Bind b) t))).(let TMP_14 \def (Bind b) in (let 
TMP_15 \def (r TMP_14 n) in (let TMP_16 \def (Bind b) in (let TMP_17 \def 
(getl_gen_S TMP_16 c c3 t n H3) in (let H5 \def (getl_gen_all c c3 TMP_15 
TMP_17) in (let TMP_18 \def (\lambda (e: C).(drop n O c e)) in (let TMP_19 
\def (\lambda (e: C).(clear e c3)) in (let TMP_20 \def (S n) in (let TMP_21 
\def (getl TMP_20 c1 c3) in (let TMP_24 \def (\lambda (x: C).(\lambda (H6: 
(drop n O c x)).(\lambda (H7: (clear x c3)).(let TMP_22 \def (S n) in (let 
TMP_23 \def (drop_clear_O b c1 c t H4 x n H6) in (getl_intro TMP_22 c1 c3 x 
TMP_23 H7)))))) in (ex2_ind C TMP_18 TMP_19 TMP_21 TMP_24 H5)))))))))))))) in 
(let TMP_28 \def (\lambda (f: F).(\lambda (_: (getl (S n) (CHead c (Flat f) 
t) c3)).(\lambda (H4: (clear c1 (CHead c (Flat f) t))).(let TMP_26 \def (S n) 
in (let TMP_27 \def (getl TMP_26 c1 c3) in (clear_gen_flat_r f c1 c t H4 
TMP_27)))))) in (K_ind TMP_13 TMP_25 TMP_28 k H1 H2)))))))))))) in (C_ind 
TMP_7 TMP_11 TMP_29 c2))))))) in (nat_ind TMP_1 TMP_5 TMP_30 i)))).

theorem getl_clear_trans:
 \forall (i: nat).(\forall (c1: C).(\forall (c2: C).((getl i c1 c2) \to 
(\forall (c3: C).((clear c2 c3) \to (getl i c1 c3))))))
\def
 \lambda (i: nat).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (getl i c1 
c2)).(\lambda (c3: C).(\lambda (H0: (clear c2 c3)).(let H1 \def (getl_gen_all 
c1 c2 i H) in (let TMP_1 \def (\lambda (e: C).(drop i O c1 e)) in (let TMP_2 
\def (\lambda (e: C).(clear e c2)) in (let TMP_3 \def (getl i c1 c3) in (let 
TMP_22 \def (\lambda (x: C).(\lambda (H2: (drop i O c1 x)).(\lambda (H3: 
(clear x c2)).(let H4 \def (clear_gen_all x c2 H3) in (let TMP_6 \def 
(\lambda (b: B).(\lambda (e: C).(\lambda (u: T).(let TMP_4 \def (Bind b) in 
(let TMP_5 \def (CHead e TMP_4 u) in (eq C c2 TMP_5)))))) in (let TMP_7 \def 
(getl i c1 c3) in (let TMP_21 \def (\lambda (x0: B).(\lambda (x1: C).(\lambda 
(x2: T).(\lambda (H5: (eq C c2 (CHead x1 (Bind x0) x2))).(let TMP_8 \def 
(\lambda (c: C).(clear x c)) in (let TMP_9 \def (Bind x0) in (let TMP_10 \def 
(CHead x1 TMP_9 x2) in (let H6 \def (eq_ind C c2 TMP_8 H3 TMP_10 H5) in (let 
TMP_11 \def (\lambda (c: C).(clear c c3)) in (let TMP_12 \def (Bind x0) in 
(let TMP_13 \def (CHead x1 TMP_12 x2) in (let H7 \def (eq_ind C c2 TMP_11 H0 
TMP_13 H5) in (let TMP_14 \def (Bind x0) in (let TMP_15 \def (CHead x1 TMP_14 
x2) in (let TMP_16 \def (\lambda (c: C).(getl i c1 c)) in (let TMP_17 \def 
(Bind x0) in (let TMP_18 \def (CHead x1 TMP_17 x2) in (let TMP_19 \def 
(getl_intro i c1 TMP_18 x H2 H6) in (let TMP_20 \def (clear_gen_bind x0 x1 c3 
x2 H7) in (eq_ind_r C TMP_15 TMP_16 TMP_19 c3 TMP_20)))))))))))))))))))) in 
(ex_3_ind B C T TMP_6 TMP_7 TMP_21 H4)))))))) in (ex2_ind C TMP_1 TMP_2 TMP_3 
TMP_22 H1))))))))))).

theorem getl_clear_bind:
 \forall (b: B).(\forall (c: C).(\forall (e1: C).(\forall (v: T).((clear c 
(CHead e1 (Bind b) v)) \to (\forall (e2: C).(\forall (n: nat).((getl n e1 e2) 
\to (getl (S n) c e2))))))))
\def
 \lambda (b: B).(\lambda (c: C).(let TMP_2 \def (\lambda (c0: C).(\forall 
(e1: C).(\forall (v: T).((clear c0 (CHead e1 (Bind b) v)) \to (\forall (e2: 
C).(\forall (n: nat).((getl n e1 e2) \to (let TMP_1 \def (S n) in (getl TMP_1 
c0 e2))))))))) in (let TMP_8 \def (\lambda (n: nat).(\lambda (e1: C).(\lambda 
(v: T).(\lambda (H: (clear (CSort n) (CHead e1 (Bind b) v))).(\lambda (e2: 
C).(\lambda (n0: nat).(\lambda (_: (getl n0 e1 e2)).(let TMP_3 \def (Bind b) 
in (let TMP_4 \def (CHead e1 TMP_3 v) in (let TMP_5 \def (S n0) in (let TMP_6 
\def (CSort n) in (let TMP_7 \def (getl TMP_5 TMP_6 e2) in (clear_gen_sort 
TMP_4 n H TMP_7))))))))))))) in (let TMP_52 \def (\lambda (c0: C).(\lambda 
(H: ((\forall (e1: C).(\forall (v: T).((clear c0 (CHead e1 (Bind b) v)) \to 
(\forall (e2: C).(\forall (n: nat).((getl n e1 e2) \to (getl (S n) c0 
e2))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (e1: C).(\lambda (v: 
T).(\lambda (H0: (clear (CHead c0 k t) (CHead e1 (Bind b) v))).(\lambda (e2: 
C).(\lambda (n: nat).(\lambda (H1: (getl n e1 e2)).(let TMP_11 \def (\lambda 
(k0: K).((clear (CHead c0 k0 t) (CHead e1 (Bind b) v)) \to (let TMP_9 \def (S 
n) in (let TMP_10 \def (CHead c0 k0 t) in (getl TMP_9 TMP_10 e2))))) in (let 
TMP_45 \def (\lambda (b0: B).(\lambda (H2: (clear (CHead c0 (Bind b0) t) 
(CHead e1 (Bind b) v))).(let TMP_12 \def (\lambda (e: C).(match e with 
[(CSort _) \Rightarrow e1 | (CHead c1 _ _) \Rightarrow c1])) in (let TMP_13 
\def (Bind b) in (let TMP_14 \def (CHead e1 TMP_13 v) in (let TMP_15 \def 
(Bind b0) in (let TMP_16 \def (CHead c0 TMP_15 t) in (let TMP_17 \def (Bind 
b) in (let TMP_18 \def (CHead e1 TMP_17 v) in (let TMP_19 \def 
(clear_gen_bind b0 c0 TMP_18 t H2) in (let H3 \def (f_equal C C TMP_12 TMP_14 
TMP_16 TMP_19) in (let TMP_20 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow b | (CHead _ k0 _) \Rightarrow (match k0 with [(Bind b1) 
\Rightarrow b1 | (Flat _) \Rightarrow b])])) in (let TMP_21 \def (Bind b) in 
(let TMP_22 \def (CHead e1 TMP_21 v) in (let TMP_23 \def (Bind b0) in (let 
TMP_24 \def (CHead c0 TMP_23 t) in (let TMP_25 \def (Bind b) in (let TMP_26 
\def (CHead e1 TMP_25 v) in (let TMP_27 \def (clear_gen_bind b0 c0 TMP_26 t 
H2) in (let H4 \def (f_equal C B TMP_20 TMP_22 TMP_24 TMP_27) in (let TMP_28 
\def (\lambda (e: C).(match e with [(CSort _) \Rightarrow v | (CHead _ _ t0) 
\Rightarrow t0])) in (let TMP_29 \def (Bind b) in (let TMP_30 \def (CHead e1 
TMP_29 v) in (let TMP_31 \def (Bind b0) in (let TMP_32 \def (CHead c0 TMP_31 
t) in (let TMP_33 \def (Bind b) in (let TMP_34 \def (CHead e1 TMP_33 v) in 
(let TMP_35 \def (clear_gen_bind b0 c0 TMP_34 t H2) in (let H5 \def (f_equal 
C T TMP_28 TMP_30 TMP_32 TMP_35) in (let TMP_43 \def (\lambda (H6: (eq B b 
b0)).(\lambda (H7: (eq C e1 c0)).(let TMP_36 \def (\lambda (c1: C).(getl n c1 
e2)) in (let H8 \def (eq_ind C e1 TMP_36 H1 c0 H7) in (let TMP_40 \def 
(\lambda (b1: B).(let TMP_37 \def (S n) in (let TMP_38 \def (Bind b1) in (let 
TMP_39 \def (CHead c0 TMP_38 t) in (getl TMP_37 TMP_39 e2))))) in (let TMP_41 
\def (Bind b) in (let TMP_42 \def (getl_head TMP_41 n c0 e2 H8 t) in (eq_ind 
B b TMP_40 TMP_42 b0 H6)))))))) in (let TMP_44 \def (TMP_43 H4) in (TMP_44 
H3)))))))))))))))))))))))))))))))) in (let TMP_51 \def (\lambda (f: 
F).(\lambda (H2: (clear (CHead c0 (Flat f) t) (CHead e1 (Bind b) v))).(let 
TMP_46 \def (S n) in (let TMP_47 \def (Bind b) in (let TMP_48 \def (CHead e1 
TMP_47 v) in (let TMP_49 \def (clear_gen_flat f c0 TMP_48 t H2) in (let 
TMP_50 \def (H e1 v TMP_49 e2 n H1) in (getl_flat c0 e2 TMP_46 TMP_50 f 
t)))))))) in (K_ind TMP_11 TMP_45 TMP_51 k H0)))))))))))))) in (C_ind TMP_2 
TMP_8 TMP_52 c))))).

theorem getl_clear_conf:
 \forall (i: nat).(\forall (c1: C).(\forall (c3: C).((getl i c1 c3) \to 
(\forall (c2: C).((clear c1 c2) \to (getl i c2 c3))))))
\def
 \lambda (i: nat).(let TMP_1 \def (\lambda (n: nat).(\forall (c1: C).(\forall 
(c3: C).((getl n c1 c3) \to (\forall (c2: C).((clear c1 c2) \to (getl n c2 
c3))))))) in (let TMP_20 \def (\lambda (c1: C).(\lambda (c3: C).(\lambda (H: 
(getl O c1 c3)).(\lambda (c2: C).(\lambda (H0: (clear c1 c2)).(let TMP_2 \def 
(\lambda (c: C).(getl O c c3)) in (let TMP_3 \def (getl_gen_O c1 c3 H) in 
(let H1 \def (clear_gen_all c1 c3 TMP_3) in (let TMP_6 \def (\lambda (b: 
B).(\lambda (e: C).(\lambda (u: T).(let TMP_4 \def (Bind b) in (let TMP_5 
\def (CHead e TMP_4 u) in (eq C c3 TMP_5)))))) in (let TMP_7 \def (getl O c3 
c3) in (let TMP_16 \def (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: 
T).(\lambda (H2: (eq C c3 (CHead x1 (Bind x0) x2))).(let TMP_8 \def (\lambda 
(c: C).(clear c1 c)) in (let TMP_9 \def (getl_gen_O c1 c3 H) in (let TMP_10 
\def (Bind x0) in (let TMP_11 \def (CHead x1 TMP_10 x2) in (let H3 \def 
(eq_ind C c3 TMP_8 TMP_9 TMP_11 H2) in (let TMP_12 \def (Bind x0) in (let 
TMP_13 \def (CHead x1 TMP_12 x2) in (let TMP_14 \def (\lambda (c: C).(getl O 
c c)) in (let TMP_15 \def (getl_refl x0 x1 x2) in (eq_ind_r C TMP_13 TMP_14 
TMP_15 c3 H2)))))))))))))) in (let TMP_17 \def (ex_3_ind B C T TMP_6 TMP_7 
TMP_16 H1) in (let TMP_18 \def (getl_gen_O c1 c3 H) in (let TMP_19 \def 
(clear_mono c1 c3 TMP_18 c2 H0) in (eq_ind C c3 TMP_2 TMP_17 c2 
TMP_19))))))))))))))) in (let TMP_44 \def (\lambda (n: nat).(\lambda (_: 
((\forall (c1: C).(\forall (c3: C).((getl n c1 c3) \to (\forall (c2: 
C).((clear c1 c2) \to (getl n c2 c3)))))))).(\lambda (c1: C).(let TMP_22 \def 
(\lambda (c: C).(\forall (c3: C).((getl (S n) c c3) \to (\forall (c2: 
C).((clear c c2) \to (let TMP_21 \def (S n) in (getl TMP_21 c2 c3))))))) in 
(let TMP_26 \def (\lambda (n0: nat).(\lambda (c3: C).(\lambda (H0: (getl (S 
n) (CSort n0) c3)).(\lambda (c2: C).(\lambda (_: (clear (CSort n0) c2)).(let 
TMP_23 \def (S n) in (let TMP_24 \def (S n) in (let TMP_25 \def (getl TMP_24 
c2 c3) in (getl_gen_sort n0 TMP_23 c3 H0 TMP_25))))))))) in (let TMP_43 \def 
(\lambda (c: C).(\lambda (H0: ((\forall (c3: C).((getl (S n) c c3) \to 
(\forall (c2: C).((clear c c2) \to (getl (S n) c2 c3))))))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (c3: C).(\lambda (H1: (getl (S n) (CHead c k t) 
c3)).(\lambda (c2: C).(\lambda (H2: (clear (CHead c k t) c2)).(let TMP_28 
\def (\lambda (k0: K).((getl (S n) (CHead c k0 t) c3) \to ((clear (CHead c k0 
t) c2) \to (let TMP_27 \def (S n) in (getl TMP_27 c2 c3))))) in (let TMP_38 
\def (\lambda (b: B).(\lambda (H3: (getl (S n) (CHead c (Bind b) t) 
c3)).(\lambda (H4: (clear (CHead c (Bind b) t) c2)).(let TMP_29 \def (Bind b) 
in (let TMP_30 \def (CHead c TMP_29 t) in (let TMP_32 \def (\lambda (c0: 
C).(let TMP_31 \def (S n) in (getl TMP_31 c0 c3))) in (let TMP_33 \def (Bind 
b) in (let TMP_34 \def (Bind b) in (let TMP_35 \def (getl_gen_S TMP_34 c c3 t 
n H3) in (let TMP_36 \def (getl_head TMP_33 n c c3 TMP_35 t) in (let TMP_37 
\def (clear_gen_bind b c c2 t H4) in (eq_ind_r C TMP_30 TMP_32 TMP_36 c2 
TMP_37)))))))))))) in (let TMP_42 \def (\lambda (f: F).(\lambda (H3: (getl (S 
n) (CHead c (Flat f) t) c3)).(\lambda (H4: (clear (CHead c (Flat f) t) 
c2)).(let TMP_39 \def (Flat f) in (let TMP_40 \def (getl_gen_S TMP_39 c c3 t 
n H3) in (let TMP_41 \def (clear_gen_flat f c c2 t H4) in (H0 c3 TMP_40 c2 
TMP_41))))))) in (K_ind TMP_28 TMP_38 TMP_42 k H1 H2)))))))))))) in (C_ind 
TMP_22 TMP_26 TMP_43 c1))))))) in (nat_ind TMP_1 TMP_20 TMP_44 i)))).

