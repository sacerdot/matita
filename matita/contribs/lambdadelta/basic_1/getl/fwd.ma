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

include "basic_1/getl/defs.ma".

include "basic_1/drop/fwd.ma".

include "basic_1/clear/fwd.ma".

theorem getl_ind:
 \forall (h: nat).(\forall (c1: C).(\forall (c2: C).(\forall (P: 
Prop).(((\forall (e: C).((drop h O c1 e) \to ((clear e c2) \to P)))) \to 
((getl h c1 c2) \to P)))))
\def
 \lambda (h: nat).(\lambda (c1: C).(\lambda (c2: C).(\lambda (P: 
Prop).(\lambda (f: ((\forall (e: C).((drop h O c1 e) \to ((clear e c2) \to 
P))))).(\lambda (g: (getl h c1 c2)).(match g with [(getl_intro x x0 x1) 
\Rightarrow (f x x0 x1)])))))).

theorem getl_gen_all:
 \forall (c1: C).(\forall (c2: C).(\forall (i: nat).((getl i c1 c2) \to (ex2 
C (\lambda (e: C).(drop i O c1 e)) (\lambda (e: C).(clear e c2))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (i: nat).(\lambda (H: (getl i c1 
c2)).(let TMP_1 \def (\lambda (e: C).(drop i O c1 e)) in (let TMP_2 \def 
(\lambda (e: C).(clear e c2)) in (let TMP_3 \def (ex2 C TMP_1 TMP_2) in (let 
TMP_6 \def (\lambda (e: C).(\lambda (H0: (drop i O c1 e)).(\lambda (H1: 
(clear e c2)).(let TMP_4 \def (\lambda (e0: C).(drop i O c1 e0)) in (let 
TMP_5 \def (\lambda (e0: C).(clear e0 c2)) in (ex_intro2 C TMP_4 TMP_5 e H0 
H1)))))) in (getl_ind i c1 c2 TMP_3 TMP_6 H)))))))).

theorem getl_gen_sort:
 \forall (n: nat).(\forall (h: nat).(\forall (x: C).((getl h (CSort n) x) \to 
(\forall (P: Prop).P))))
\def
 \lambda (n: nat).(\lambda (h: nat).(\lambda (x: C).(\lambda (H: (getl h 
(CSort n) x)).(\lambda (P: Prop).(let TMP_1 \def (CSort n) in (let H0 \def 
(getl_gen_all TMP_1 x h H) in (let TMP_3 \def (\lambda (e: C).(let TMP_2 \def 
(CSort n) in (drop h O TMP_2 e))) in (let TMP_4 \def (\lambda (e: C).(clear e 
x)) in (let TMP_13 \def (\lambda (x0: C).(\lambda (H1: (drop h O (CSort n) 
x0)).(\lambda (H2: (clear x0 x)).(let TMP_5 \def (CSort n) in (let TMP_6 \def 
(eq C x0 TMP_5) in (let TMP_7 \def (eq nat h O) in (let TMP_8 \def (eq nat O 
O) in (let TMP_11 \def (\lambda (H3: (eq C x0 (CSort n))).(\lambda (_: (eq 
nat h O)).(\lambda (_: (eq nat O O)).(let TMP_9 \def (\lambda (c: C).(clear c 
x)) in (let TMP_10 \def (CSort n) in (let H6 \def (eq_ind C x0 TMP_9 H2 
TMP_10 H3) in (clear_gen_sort x n H6 P))))))) in (let TMP_12 \def 
(drop_gen_sort n h O x0 H1) in (and3_ind TMP_6 TMP_7 TMP_8 P TMP_11 
TMP_12)))))))))) in (ex2_ind C TMP_3 TMP_4 P TMP_13 H0)))))))))).

theorem getl_gen_O:
 \forall (e: C).(\forall (x: C).((getl O e x) \to (clear e x)))
\def
 \lambda (e: C).(\lambda (x: C).(\lambda (H: (getl O e x)).(let H0 \def 
(getl_gen_all e x O H) in (let TMP_1 \def (\lambda (e0: C).(drop O O e e0)) 
in (let TMP_2 \def (\lambda (e0: C).(clear e0 x)) in (let TMP_3 \def (clear e 
x) in (let TMP_6 \def (\lambda (x0: C).(\lambda (H1: (drop O O e 
x0)).(\lambda (H2: (clear x0 x)).(let TMP_4 \def (\lambda (c: C).(clear c x)) 
in (let TMP_5 \def (drop_gen_refl e x0 H1) in (let H3 \def (eq_ind_r C x0 
TMP_4 H2 e TMP_5) in H3)))))) in (ex2_ind C TMP_1 TMP_2 TMP_3 TMP_6 
H0)))))))).

theorem getl_gen_S:
 \forall (k: K).(\forall (c: C).(\forall (x: C).(\forall (u: T).(\forall (h: 
nat).((getl (S h) (CHead c k u) x) \to (getl (r k h) c x))))))
\def
 \lambda (k: K).(\lambda (c: C).(\lambda (x: C).(\lambda (u: T).(\lambda (h: 
nat).(\lambda (H: (getl (S h) (CHead c k u) x)).(let TMP_1 \def (CHead c k u) 
in (let TMP_2 \def (S h) in (let H0 \def (getl_gen_all TMP_1 x TMP_2 H) in 
(let TMP_5 \def (\lambda (e: C).(let TMP_3 \def (S h) in (let TMP_4 \def 
(CHead c k u) in (drop TMP_3 O TMP_4 e)))) in (let TMP_6 \def (\lambda (e: 
C).(clear e x)) in (let TMP_7 \def (r k h) in (let TMP_8 \def (getl TMP_7 c 
x) in (let TMP_11 \def (\lambda (x0: C).(\lambda (H1: (drop (S h) O (CHead c 
k u) x0)).(\lambda (H2: (clear x0 x)).(let TMP_9 \def (r k h) in (let TMP_10 
\def (drop_gen_drop k c x0 u h H1) in (getl_intro TMP_9 c x x0 TMP_10 
H2)))))) in (ex2_ind C TMP_5 TMP_6 TMP_8 TMP_11 H0)))))))))))))).

theorem getl_gen_2:
 \forall (c1: C).(\forall (c2: C).(\forall (i: nat).((getl i c1 c2) \to (ex_3 
B C T (\lambda (b: B).(\lambda (c: C).(\lambda (v: T).(eq C c2 (CHead c (Bind 
b) v)))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (i: nat).(\lambda (H: (getl i c1 
c2)).(let H0 \def (getl_gen_all c1 c2 i H) in (let TMP_1 \def (\lambda (e: 
C).(drop i O c1 e)) in (let TMP_2 \def (\lambda (e: C).(clear e c2)) in (let 
TMP_5 \def (\lambda (b: B).(\lambda (c: C).(\lambda (v: T).(let TMP_3 \def 
(Bind b) in (let TMP_4 \def (CHead c TMP_3 v) in (eq C c2 TMP_4)))))) in (let 
TMP_6 \def (ex_3 B C T TMP_5) in (let TMP_33 \def (\lambda (x: C).(\lambda 
(_: (drop i O c1 x)).(\lambda (H2: (clear x c2)).(let H3 \def (clear_gen_all 
x c2 H2) in (let TMP_9 \def (\lambda (b: B).(\lambda (e: C).(\lambda (u: 
T).(let TMP_7 \def (Bind b) in (let TMP_8 \def (CHead e TMP_7 u) in (eq C c2 
TMP_8)))))) in (let TMP_12 \def (\lambda (b: B).(\lambda (c: C).(\lambda (v: 
T).(let TMP_10 \def (Bind b) in (let TMP_11 \def (CHead c TMP_10 v) in (eq C 
c2 TMP_11)))))) in (let TMP_13 \def (ex_3 B C T TMP_12) in (let TMP_32 \def 
(\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: T).(\lambda (H4: (eq C c2 
(CHead x1 (Bind x0) x2))).(let TMP_14 \def (\lambda (c: C).(clear x c)) in 
(let TMP_15 \def (Bind x0) in (let TMP_16 \def (CHead x1 TMP_15 x2) in (let 
H5 \def (eq_ind C c2 TMP_14 H2 TMP_16 H4) in (let TMP_17 \def (Bind x0) in 
(let TMP_18 \def (CHead x1 TMP_17 x2) in (let TMP_22 \def (\lambda (c: 
C).(let TMP_21 \def (\lambda (b: B).(\lambda (c0: C).(\lambda (v: T).(let 
TMP_19 \def (Bind b) in (let TMP_20 \def (CHead c0 TMP_19 v) in (eq C c 
TMP_20)))))) in (ex_3 B C T TMP_21))) in (let TMP_27 \def (\lambda (b: 
B).(\lambda (c: C).(\lambda (v: T).(let TMP_23 \def (Bind x0) in (let TMP_24 
\def (CHead x1 TMP_23 x2) in (let TMP_25 \def (Bind b) in (let TMP_26 \def 
(CHead c TMP_25 v) in (eq C TMP_24 TMP_26)))))))) in (let TMP_28 \def (Bind 
x0) in (let TMP_29 \def (CHead x1 TMP_28 x2) in (let TMP_30 \def (refl_equal 
C TMP_29) in (let TMP_31 \def (ex_3_intro B C T TMP_27 x0 x1 x2 TMP_30) in 
(eq_ind_r C TMP_18 TMP_22 TMP_31 c2 H4))))))))))))))))) in (ex_3_ind B C T 
TMP_9 TMP_13 TMP_32 H3))))))))) in (ex2_ind C TMP_1 TMP_2 TMP_6 TMP_33 
H0)))))))))).

theorem getl_gen_flat:
 \forall (f: F).(\forall (e: C).(\forall (d: C).(\forall (v: T).(\forall (i: 
nat).((getl i (CHead e (Flat f) v) d) \to (getl i e d))))))
\def
 \lambda (f: F).(\lambda (e: C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: 
nat).(let TMP_1 \def (\lambda (n: nat).((getl n (CHead e (Flat f) v) d) \to 
(getl n e d))) in (let TMP_7 \def (\lambda (H: (getl O (CHead e (Flat f) v) 
d)).(let TMP_2 \def (drop_refl e) in (let TMP_3 \def (Flat f) in (let TMP_4 
\def (CHead e TMP_3 v) in (let TMP_5 \def (getl_gen_O TMP_4 d H) in (let 
TMP_6 \def (clear_gen_flat f e d v TMP_5) in (getl_intro O e d e TMP_2 
TMP_6))))))) in (let TMP_9 \def (\lambda (n: nat).(\lambda (_: (((getl n 
(CHead e (Flat f) v) d) \to (getl n e d)))).(\lambda (H0: (getl (S n) (CHead 
e (Flat f) v) d)).(let TMP_8 \def (Flat f) in (getl_gen_S TMP_8 e d v n 
H0))))) in (nat_ind TMP_1 TMP_7 TMP_9 i)))))))).

theorem getl_gen_bind:
 \forall (b: B).(\forall (e: C).(\forall (d: C).(\forall (v: T).(\forall (i: 
nat).((getl i (CHead e (Bind b) v) d) \to (or (land (eq nat i O) (eq C d 
(CHead e (Bind b) v))) (ex2 nat (\lambda (j: nat).(eq nat i (S j))) (\lambda 
(j: nat).(getl j e d)))))))))
\def
 \lambda (b: B).(\lambda (e: C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: 
nat).(let TMP_10 \def (\lambda (n: nat).((getl n (CHead e (Bind b) v) d) \to 
(let TMP_1 \def (eq nat n O) in (let TMP_2 \def (Bind b) in (let TMP_3 \def 
(CHead e TMP_2 v) in (let TMP_4 \def (eq C d TMP_3) in (let TMP_5 \def (land 
TMP_1 TMP_4) in (let TMP_7 \def (\lambda (j: nat).(let TMP_6 \def (S j) in 
(eq nat n TMP_6))) in (let TMP_8 \def (\lambda (j: nat).(getl j e d)) in (let 
TMP_9 \def (ex2 nat TMP_7 TMP_8) in (or TMP_5 TMP_9))))))))))) in (let TMP_52 
\def (\lambda (H: (getl O (CHead e (Bind b) v) d)).(let TMP_11 \def (Bind b) 
in (let TMP_12 \def (CHead e TMP_11 v) in (let TMP_22 \def (\lambda (c: 
C).(let TMP_13 \def (eq nat O O) in (let TMP_14 \def (Bind b) in (let TMP_15 
\def (CHead e TMP_14 v) in (let TMP_16 \def (eq C c TMP_15) in (let TMP_17 
\def (land TMP_13 TMP_16) in (let TMP_19 \def (\lambda (j: nat).(let TMP_18 
\def (S j) in (eq nat O TMP_18))) in (let TMP_20 \def (\lambda (j: nat).(getl 
j e c)) in (let TMP_21 \def (ex2 nat TMP_19 TMP_20) in (or TMP_17 
TMP_21)))))))))) in (let TMP_23 \def (eq nat O O) in (let TMP_24 \def (Bind 
b) in (let TMP_25 \def (CHead e TMP_24 v) in (let TMP_26 \def (Bind b) in 
(let TMP_27 \def (CHead e TMP_26 v) in (let TMP_28 \def (eq C TMP_25 TMP_27) 
in (let TMP_29 \def (land TMP_23 TMP_28) in (let TMP_31 \def (\lambda (j: 
nat).(let TMP_30 \def (S j) in (eq nat O TMP_30))) in (let TMP_34 \def 
(\lambda (j: nat).(let TMP_32 \def (Bind b) in (let TMP_33 \def (CHead e 
TMP_32 v) in (getl j e TMP_33)))) in (let TMP_35 \def (ex2 nat TMP_31 TMP_34) 
in (let TMP_36 \def (eq nat O O) in (let TMP_37 \def (Bind b) in (let TMP_38 
\def (CHead e TMP_37 v) in (let TMP_39 \def (Bind b) in (let TMP_40 \def 
(CHead e TMP_39 v) in (let TMP_41 \def (eq C TMP_38 TMP_40) in (let TMP_42 
\def (refl_equal nat O) in (let TMP_43 \def (Bind b) in (let TMP_44 \def 
(CHead e TMP_43 v) in (let TMP_45 \def (refl_equal C TMP_44) in (let TMP_46 
\def (conj TMP_36 TMP_41 TMP_42 TMP_45) in (let TMP_47 \def (or_introl TMP_29 
TMP_35 TMP_46) in (let TMP_48 \def (Bind b) in (let TMP_49 \def (CHead e 
TMP_48 v) in (let TMP_50 \def (getl_gen_O TMP_49 d H) in (let TMP_51 \def 
(clear_gen_bind b e d v TMP_50) in (eq_ind_r C TMP_12 TMP_22 TMP_47 d 
TMP_51))))))))))))))))))))))))))))))) in (let TMP_73 \def (\lambda (n: 
nat).(\lambda (_: (((getl n (CHead e (Bind b) v) d) \to (or (land (eq nat n 
O) (eq C d (CHead e (Bind b) v))) (ex2 nat (\lambda (j: nat).(eq nat n (S 
j))) (\lambda (j: nat).(getl j e d))))))).(\lambda (H0: (getl (S n) (CHead e 
(Bind b) v) d)).(let TMP_53 \def (S n) in (let TMP_54 \def (eq nat TMP_53 O) 
in (let TMP_55 \def (Bind b) in (let TMP_56 \def (CHead e TMP_55 v) in (let 
TMP_57 \def (eq C d TMP_56) in (let TMP_58 \def (land TMP_54 TMP_57) in (let 
TMP_61 \def (\lambda (j: nat).(let TMP_59 \def (S n) in (let TMP_60 \def (S 
j) in (eq nat TMP_59 TMP_60)))) in (let TMP_62 \def (\lambda (j: nat).(getl j 
e d)) in (let TMP_63 \def (ex2 nat TMP_61 TMP_62) in (let TMP_66 \def 
(\lambda (j: nat).(let TMP_64 \def (S n) in (let TMP_65 \def (S j) in (eq nat 
TMP_64 TMP_65)))) in (let TMP_67 \def (\lambda (j: nat).(getl j e d)) in (let 
TMP_68 \def (S n) in (let TMP_69 \def (refl_equal nat TMP_68) in (let TMP_70 
\def (Bind b) in (let TMP_71 \def (getl_gen_S TMP_70 e d v n H0) in (let 
TMP_72 \def (ex_intro2 nat TMP_66 TMP_67 n TMP_69 TMP_71) in (or_intror 
TMP_58 TMP_63 TMP_72)))))))))))))))))))) in (nat_ind TMP_10 TMP_52 TMP_73 
i)))))))).

theorem getl_mono:
 \forall (c: C).(\forall (x1: C).(\forall (h: nat).((getl h c x1) \to 
(\forall (x2: C).((getl h c x2) \to (eq C x1 x2))))))
\def
 \lambda (c: C).(\lambda (x1: C).(\lambda (h: nat).(\lambda (H: (getl h c 
x1)).(\lambda (x2: C).(\lambda (H0: (getl h c x2)).(let H1 \def (getl_gen_all 
c x2 h H0) in (let TMP_1 \def (\lambda (e: C).(drop h O c e)) in (let TMP_2 
\def (\lambda (e: C).(clear e x2)) in (let TMP_3 \def (eq C x1 x2) in (let 
TMP_14 \def (\lambda (x: C).(\lambda (H2: (drop h O c x)).(\lambda (H3: 
(clear x x2)).(let H4 \def (getl_gen_all c x1 h H) in (let TMP_4 \def 
(\lambda (e: C).(drop h O c e)) in (let TMP_5 \def (\lambda (e: C).(clear e 
x1)) in (let TMP_6 \def (eq C x1 x2) in (let TMP_13 \def (\lambda (x0: 
C).(\lambda (H5: (drop h O c x0)).(\lambda (H6: (clear x0 x1)).(let TMP_7 
\def (\lambda (c0: C).(drop h O c c0)) in (let TMP_8 \def (drop_mono c x O h 
H2 x0 H5) in (let H7 \def (eq_ind C x TMP_7 H2 x0 TMP_8) in (let TMP_9 \def 
(\lambda (c0: C).(drop h O c c0)) in (let TMP_10 \def (drop_mono c x O h H2 
x0 H5) in (let H8 \def (eq_ind_r C x0 TMP_9 H7 x TMP_10) in (let TMP_11 \def 
(\lambda (c0: C).(clear c0 x1)) in (let TMP_12 \def (drop_mono c x O h H2 x0 
H5) in (let H9 \def (eq_ind_r C x0 TMP_11 H6 x TMP_12) in (clear_mono x x1 H9 
x2 H3))))))))))))) in (ex2_ind C TMP_4 TMP_5 TMP_6 TMP_13 H4))))))))) in 
(ex2_ind C TMP_1 TMP_2 TMP_3 TMP_14 H1))))))))))).

