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

include "basic_1/subst1/defs.ma".

include "basic_1/subst0/fwd.ma".

theorem subst1_ind:
 \forall (i: nat).(\forall (v: T).(\forall (t1: T).(\forall (P: ((T \to 
Prop))).((P t1) \to (((\forall (t2: T).((subst0 i v t1 t2) \to (P t2)))) \to 
(\forall (t: T).((subst1 i v t1 t) \to (P t))))))))
\def
 \lambda (i: nat).(\lambda (v: T).(\lambda (t1: T).(\lambda (P: ((T \to 
Prop))).(\lambda (f: (P t1)).(\lambda (f0: ((\forall (t2: T).((subst0 i v t1 
t2) \to (P t2))))).(\lambda (t: T).(\lambda (s0: (subst1 i v t1 t)).(match s0 
with [subst1_refl \Rightarrow f | (subst1_single x x0) \Rightarrow (f0 x 
x0)])))))))).

theorem subst1_gen_sort:
 \forall (v: T).(\forall (x: T).(\forall (i: nat).(\forall (n: nat).((subst1 
i v (TSort n) x) \to (eq T x (TSort n))))))
\def
 \lambda (v: T).(\lambda (x: T).(\lambda (i: nat).(\lambda (n: nat).(\lambda 
(H: (subst1 i v (TSort n) x)).(let TMP_1 \def (TSort n) in (let TMP_3 \def 
(\lambda (t: T).(let TMP_2 \def (TSort n) in (eq T t TMP_2))) in (let TMP_4 
\def (TSort n) in (let TMP_5 \def (refl_equal T TMP_4) in (let TMP_8 \def 
(\lambda (t2: T).(\lambda (H0: (subst0 i v (TSort n) t2)).(let TMP_6 \def 
(TSort n) in (let TMP_7 \def (eq T t2 TMP_6) in (subst0_gen_sort v t2 i n H0 
TMP_7))))) in (subst1_ind i v TMP_1 TMP_3 TMP_5 TMP_8 x H)))))))))).

theorem subst1_gen_lref:
 \forall (v: T).(\forall (x: T).(\forall (i: nat).(\forall (n: nat).((subst1 
i v (TLRef n) x) \to (or (eq T x (TLRef n)) (land (eq nat n i) (eq T x (lift 
(S n) O v))))))))
\def
 \lambda (v: T).(\lambda (x: T).(\lambda (i: nat).(\lambda (n: nat).(\lambda 
(H: (subst1 i v (TLRef n) x)).(let TMP_1 \def (TLRef n) in (let TMP_9 \def 
(\lambda (t: T).(let TMP_2 \def (TLRef n) in (let TMP_3 \def (eq T t TMP_2) 
in (let TMP_4 \def (eq nat n i) in (let TMP_5 \def (S n) in (let TMP_6 \def 
(lift TMP_5 O v) in (let TMP_7 \def (eq T t TMP_6) in (let TMP_8 \def (land 
TMP_4 TMP_7) in (or TMP_3 TMP_8))))))))) in (let TMP_10 \def (TLRef n) in 
(let TMP_11 \def (TLRef n) in (let TMP_12 \def (eq T TMP_10 TMP_11) in (let 
TMP_13 \def (eq nat n i) in (let TMP_14 \def (TLRef n) in (let TMP_15 \def (S 
n) in (let TMP_16 \def (lift TMP_15 O v) in (let TMP_17 \def (eq T TMP_14 
TMP_16) in (let TMP_18 \def (land TMP_13 TMP_17) in (let TMP_19 \def (TLRef 
n) in (let TMP_20 \def (refl_equal T TMP_19) in (let TMP_21 \def (or_introl 
TMP_12 TMP_18 TMP_20) in (let TMP_48 \def (\lambda (t2: T).(\lambda (H0: 
(subst0 i v (TLRef n) t2)).(let TMP_22 \def (eq nat n i) in (let TMP_23 \def 
(S n) in (let TMP_24 \def (lift TMP_23 O v) in (let TMP_25 \def (eq T t2 
TMP_24) in (let TMP_26 \def (TLRef n) in (let TMP_27 \def (eq T t2 TMP_26) in 
(let TMP_28 \def (eq nat n i) in (let TMP_29 \def (S n) in (let TMP_30 \def 
(lift TMP_29 O v) in (let TMP_31 \def (eq T t2 TMP_30) in (let TMP_32 \def 
(land TMP_28 TMP_31) in (let TMP_33 \def (or TMP_27 TMP_32) in (let TMP_46 
\def (\lambda (H1: (eq nat n i)).(\lambda (H2: (eq T t2 (lift (S n) O 
v))).(let TMP_34 \def (TLRef n) in (let TMP_35 \def (eq T t2 TMP_34) in (let 
TMP_36 \def (eq nat n i) in (let TMP_37 \def (S n) in (let TMP_38 \def (lift 
TMP_37 O v) in (let TMP_39 \def (eq T t2 TMP_38) in (let TMP_40 \def (land 
TMP_36 TMP_39) in (let TMP_41 \def (eq nat n i) in (let TMP_42 \def (S n) in 
(let TMP_43 \def (lift TMP_42 O v) in (let TMP_44 \def (eq T t2 TMP_43) in 
(let TMP_45 \def (conj TMP_41 TMP_44 H1 H2) in (or_intror TMP_35 TMP_40 
TMP_45))))))))))))))) in (let TMP_47 \def (subst0_gen_lref v t2 i n H0) in 
(land_ind TMP_22 TMP_25 TMP_33 TMP_46 TMP_47))))))))))))))))) in (subst1_ind 
i v TMP_1 TMP_9 TMP_21 TMP_48 x H)))))))))))))))))))).

theorem subst1_gen_head:
 \forall (k: K).(\forall (v: T).(\forall (u1: T).(\forall (t1: T).(\forall 
(x: T).(\forall (i: nat).((subst1 i v (THead k u1 t1) x) \to (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T x (THead k u2 t2)))) (\lambda (u2: 
T).(\lambda (_: T).(subst1 i v u1 u2))) (\lambda (_: T).(\lambda (t2: 
T).(subst1 (s k i) v t1 t2))))))))))
\def
 \lambda (k: K).(\lambda (v: T).(\lambda (u1: T).(\lambda (t1: T).(\lambda 
(x: T).(\lambda (i: nat).(\lambda (H: (subst1 i v (THead k u1 t1) x)).(let 
TMP_1 \def (THead k u1 t1) in (let TMP_7 \def (\lambda (t: T).(let TMP_3 \def 
(\lambda (u2: T).(\lambda (t2: T).(let TMP_2 \def (THead k u2 t2) in (eq T t 
TMP_2)))) in (let TMP_4 \def (\lambda (u2: T).(\lambda (_: T).(subst1 i v u1 
u2))) in (let TMP_6 \def (\lambda (_: T).(\lambda (t2: T).(let TMP_5 \def (s 
k i) in (subst1 TMP_5 v t1 t2)))) in (ex3_2 T T TMP_3 TMP_4 TMP_6))))) in 
(let TMP_10 \def (\lambda (u2: T).(\lambda (t2: T).(let TMP_8 \def (THead k 
u1 t1) in (let TMP_9 \def (THead k u2 t2) in (eq T TMP_8 TMP_9))))) in (let 
TMP_11 \def (\lambda (u2: T).(\lambda (_: T).(subst1 i v u1 u2))) in (let 
TMP_13 \def (\lambda (_: T).(\lambda (t2: T).(let TMP_12 \def (s k i) in 
(subst1 TMP_12 v t1 t2)))) in (let TMP_14 \def (THead k u1 t1) in (let TMP_15 
\def (refl_equal T TMP_14) in (let TMP_16 \def (subst1_refl i v u1) in (let 
TMP_17 \def (s k i) in (let TMP_18 \def (subst1_refl TMP_17 v t1) in (let 
TMP_19 \def (ex3_2_intro T T TMP_10 TMP_11 TMP_13 u1 t1 TMP_15 TMP_16 TMP_18) 
in (let TMP_102 \def (\lambda (t2: T).(\lambda (H0: (subst0 i v (THead k u1 
t1) t2)).(let TMP_21 \def (\lambda (u2: T).(let TMP_20 \def (THead k u2 t1) 
in (eq T t2 TMP_20))) in (let TMP_22 \def (\lambda (u2: T).(subst0 i v u1 
u2)) in (let TMP_23 \def (ex2 T TMP_21 TMP_22) in (let TMP_25 \def (\lambda 
(t3: T).(let TMP_24 \def (THead k u1 t3) in (eq T t2 TMP_24))) in (let TMP_27 
\def (\lambda (t3: T).(let TMP_26 \def (s k i) in (subst0 TMP_26 v t1 t3))) 
in (let TMP_28 \def (ex2 T TMP_25 TMP_27) in (let TMP_30 \def (\lambda (u2: 
T).(\lambda (t3: T).(let TMP_29 \def (THead k u2 t3) in (eq T t2 TMP_29)))) 
in (let TMP_31 \def (\lambda (u2: T).(\lambda (_: T).(subst0 i v u1 u2))) in 
(let TMP_33 \def (\lambda (_: T).(\lambda (t3: T).(let TMP_32 \def (s k i) in 
(subst0 TMP_32 v t1 t3)))) in (let TMP_34 \def (ex3_2 T T TMP_30 TMP_31 
TMP_33) in (let TMP_36 \def (\lambda (u2: T).(\lambda (t3: T).(let TMP_35 
\def (THead k u2 t3) in (eq T t2 TMP_35)))) in (let TMP_37 \def (\lambda (u2: 
T).(\lambda (_: T).(subst1 i v u1 u2))) in (let TMP_39 \def (\lambda (_: 
T).(\lambda (t3: T).(let TMP_38 \def (s k i) in (subst1 TMP_38 v t1 t3)))) in 
(let TMP_40 \def (ex3_2 T T TMP_36 TMP_37 TMP_39) in (let TMP_59 \def 
(\lambda (H1: (ex2 T (\lambda (u2: T).(eq T t2 (THead k u2 t1))) (\lambda 
(u2: T).(subst0 i v u1 u2)))).(let TMP_42 \def (\lambda (u2: T).(let TMP_41 
\def (THead k u2 t1) in (eq T t2 TMP_41))) in (let TMP_43 \def (\lambda (u2: 
T).(subst0 i v u1 u2)) in (let TMP_45 \def (\lambda (u2: T).(\lambda (t3: 
T).(let TMP_44 \def (THead k u2 t3) in (eq T t2 TMP_44)))) in (let TMP_46 
\def (\lambda (u2: T).(\lambda (_: T).(subst1 i v u1 u2))) in (let TMP_48 
\def (\lambda (_: T).(\lambda (t3: T).(let TMP_47 \def (s k i) in (subst1 
TMP_47 v t1 t3)))) in (let TMP_49 \def (ex3_2 T T TMP_45 TMP_46 TMP_48) in 
(let TMP_58 \def (\lambda (x0: T).(\lambda (H2: (eq T t2 (THead k x0 
t1))).(\lambda (H3: (subst0 i v u1 x0)).(let TMP_51 \def (\lambda (u2: 
T).(\lambda (t3: T).(let TMP_50 \def (THead k u2 t3) in (eq T t2 TMP_50)))) 
in (let TMP_52 \def (\lambda (u2: T).(\lambda (_: T).(subst1 i v u1 u2))) in 
(let TMP_54 \def (\lambda (_: T).(\lambda (t3: T).(let TMP_53 \def (s k i) in 
(subst1 TMP_53 v t1 t3)))) in (let TMP_55 \def (subst1_single i v u1 x0 H3) 
in (let TMP_56 \def (s k i) in (let TMP_57 \def (subst1_refl TMP_56 v t1) in 
(ex3_2_intro T T TMP_51 TMP_52 TMP_54 x0 t1 H2 TMP_55 TMP_57)))))))))) in 
(ex2_ind T TMP_42 TMP_43 TMP_49 TMP_58 H1))))))))) in (let TMP_79 \def 
(\lambda (H1: (ex2 T (\lambda (t3: T).(eq T t2 (THead k u1 t3))) (\lambda 
(t3: T).(subst0 (s k i) v t1 t3)))).(let TMP_61 \def (\lambda (t3: T).(let 
TMP_60 \def (THead k u1 t3) in (eq T t2 TMP_60))) in (let TMP_63 \def 
(\lambda (t3: T).(let TMP_62 \def (s k i) in (subst0 TMP_62 v t1 t3))) in 
(let TMP_65 \def (\lambda (u2: T).(\lambda (t3: T).(let TMP_64 \def (THead k 
u2 t3) in (eq T t2 TMP_64)))) in (let TMP_66 \def (\lambda (u2: T).(\lambda 
(_: T).(subst1 i v u1 u2))) in (let TMP_68 \def (\lambda (_: T).(\lambda (t3: 
T).(let TMP_67 \def (s k i) in (subst1 TMP_67 v t1 t3)))) in (let TMP_69 \def 
(ex3_2 T T TMP_65 TMP_66 TMP_68) in (let TMP_78 \def (\lambda (x0: 
T).(\lambda (H2: (eq T t2 (THead k u1 x0))).(\lambda (H3: (subst0 (s k i) v 
t1 x0)).(let TMP_71 \def (\lambda (u2: T).(\lambda (t3: T).(let TMP_70 \def 
(THead k u2 t3) in (eq T t2 TMP_70)))) in (let TMP_72 \def (\lambda (u2: 
T).(\lambda (_: T).(subst1 i v u1 u2))) in (let TMP_74 \def (\lambda (_: 
T).(\lambda (t3: T).(let TMP_73 \def (s k i) in (subst1 TMP_73 v t1 t3)))) in 
(let TMP_75 \def (subst1_refl i v u1) in (let TMP_76 \def (s k i) in (let 
TMP_77 \def (subst1_single TMP_76 v t1 x0 H3) in (ex3_2_intro T T TMP_71 
TMP_72 TMP_74 u1 x0 H2 TMP_75 TMP_77)))))))))) in (ex2_ind T TMP_61 TMP_63 
TMP_69 TMP_78 H1))))))))) in (let TMP_100 \def (\lambda (H1: (ex3_2 T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T t2 (THead k u2 t3)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i v u1 u2))) (\lambda (_: T).(\lambda (t3: 
T).(subst0 (s k i) v t1 t3))))).(let TMP_81 \def (\lambda (u2: T).(\lambda 
(t3: T).(let TMP_80 \def (THead k u2 t3) in (eq T t2 TMP_80)))) in (let 
TMP_82 \def (\lambda (u2: T).(\lambda (_: T).(subst0 i v u1 u2))) in (let 
TMP_84 \def (\lambda (_: T).(\lambda (t3: T).(let TMP_83 \def (s k i) in 
(subst0 TMP_83 v t1 t3)))) in (let TMP_86 \def (\lambda (u2: T).(\lambda (t3: 
T).(let TMP_85 \def (THead k u2 t3) in (eq T t2 TMP_85)))) in (let TMP_87 
\def (\lambda (u2: T).(\lambda (_: T).(subst1 i v u1 u2))) in (let TMP_89 
\def (\lambda (_: T).(\lambda (t3: T).(let TMP_88 \def (s k i) in (subst1 
TMP_88 v t1 t3)))) in (let TMP_90 \def (ex3_2 T T TMP_86 TMP_87 TMP_89) in 
(let TMP_99 \def (\lambda (x0: T).(\lambda (x1: T).(\lambda (H2: (eq T t2 
(THead k x0 x1))).(\lambda (H3: (subst0 i v u1 x0)).(\lambda (H4: (subst0 (s 
k i) v t1 x1)).(let TMP_92 \def (\lambda (u2: T).(\lambda (t3: T).(let TMP_91 
\def (THead k u2 t3) in (eq T t2 TMP_91)))) in (let TMP_93 \def (\lambda (u2: 
T).(\lambda (_: T).(subst1 i v u1 u2))) in (let TMP_95 \def (\lambda (_: 
T).(\lambda (t3: T).(let TMP_94 \def (s k i) in (subst1 TMP_94 v t1 t3)))) in 
(let TMP_96 \def (subst1_single i v u1 x0 H3) in (let TMP_97 \def (s k i) in 
(let TMP_98 \def (subst1_single TMP_97 v t1 x1 H4) in (ex3_2_intro T T TMP_92 
TMP_93 TMP_95 x0 x1 H2 TMP_96 TMP_98)))))))))))) in (ex3_2_ind T T TMP_81 
TMP_82 TMP_84 TMP_90 TMP_99 H1)))))))))) in (let TMP_101 \def 
(subst0_gen_head k v u1 t1 t2 i H0) in (or3_ind TMP_23 TMP_28 TMP_34 TMP_40 
TMP_59 TMP_79 TMP_100 TMP_101))))))))))))))))))))) in (subst1_ind i v TMP_1 
TMP_7 TMP_19 TMP_102 x H))))))))))))))))))).

theorem subst1_gen_lift_lt:
 \forall (u: T).(\forall (t1: T).(\forall (x: T).(\forall (i: nat).(\forall 
(h: nat).(\forall (d: nat).((subst1 i (lift h d u) (lift h (S (plus i d)) t1) 
x) \to (ex2 T (\lambda (t2: T).(eq T x (lift h (S (plus i d)) t2))) (\lambda 
(t2: T).(subst1 i u t1 t2)))))))))
\def
 \lambda (u: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (i: nat).(\lambda 
(h: nat).(\lambda (d: nat).(\lambda (H: (subst1 i (lift h d u) (lift h (S 
(plus i d)) t1) x)).(let TMP_1 \def (lift h d u) in (let TMP_2 \def (plus i 
d) in (let TMP_3 \def (S TMP_2) in (let TMP_4 \def (lift h TMP_3 t1) in (let 
TMP_10 \def (\lambda (t: T).(let TMP_8 \def (\lambda (t2: T).(let TMP_5 \def 
(plus i d) in (let TMP_6 \def (S TMP_5) in (let TMP_7 \def (lift h TMP_6 t2) 
in (eq T t TMP_7))))) in (let TMP_9 \def (\lambda (t2: T).(subst1 i u t1 t2)) 
in (ex2 T TMP_8 TMP_9)))) in (let TMP_17 \def (\lambda (t2: T).(let TMP_11 
\def (plus i d) in (let TMP_12 \def (S TMP_11) in (let TMP_13 \def (lift h 
TMP_12 t1) in (let TMP_14 \def (plus i d) in (let TMP_15 \def (S TMP_14) in 
(let TMP_16 \def (lift h TMP_15 t2) in (eq T TMP_13 TMP_16)))))))) in (let 
TMP_18 \def (\lambda (t2: T).(subst1 i u t1 t2)) in (let TMP_19 \def (plus i 
d) in (let TMP_20 \def (S TMP_19) in (let TMP_21 \def (lift h TMP_20 t1) in 
(let TMP_22 \def (refl_equal T TMP_21) in (let TMP_23 \def (subst1_refl i u 
t1) in (let TMP_24 \def (ex_intro2 T TMP_17 TMP_18 t1 TMP_22 TMP_23) in (let 
TMP_44 \def (\lambda (t2: T).(\lambda (H0: (subst0 i (lift h d u) (lift h (S 
(plus i d)) t1) t2)).(let TMP_28 \def (\lambda (t3: T).(let TMP_25 \def (plus 
i d) in (let TMP_26 \def (S TMP_25) in (let TMP_27 \def (lift h TMP_26 t3) in 
(eq T t2 TMP_27))))) in (let TMP_29 \def (\lambda (t3: T).(subst0 i u t1 t3)) 
in (let TMP_33 \def (\lambda (t3: T).(let TMP_30 \def (plus i d) in (let 
TMP_31 \def (S TMP_30) in (let TMP_32 \def (lift h TMP_31 t3) in (eq T t2 
TMP_32))))) in (let TMP_34 \def (\lambda (t3: T).(subst1 i u t1 t3)) in (let 
TMP_35 \def (ex2 T TMP_33 TMP_34) in (let TMP_42 \def (\lambda (x0: 
T).(\lambda (H1: (eq T t2 (lift h (S (plus i d)) x0))).(\lambda (H2: (subst0 
i u t1 x0)).(let TMP_39 \def (\lambda (t3: T).(let TMP_36 \def (plus i d) in 
(let TMP_37 \def (S TMP_36) in (let TMP_38 \def (lift h TMP_37 t3) in (eq T 
t2 TMP_38))))) in (let TMP_40 \def (\lambda (t3: T).(subst1 i u t1 t3)) in 
(let TMP_41 \def (subst1_single i u t1 x0 H2) in (ex_intro2 T TMP_39 TMP_40 
x0 H1 TMP_41))))))) in (let TMP_43 \def (subst0_gen_lift_lt u t1 t2 i h d H0) 
in (ex2_ind T TMP_28 TMP_29 TMP_35 TMP_42 TMP_43)))))))))) in (subst1_ind i 
TMP_1 TMP_4 TMP_10 TMP_24 TMP_44 x H))))))))))))))))))))).

theorem subst1_gen_lift_eq:
 \forall (t: T).(\forall (u: T).(\forall (x: T).(\forall (h: nat).(\forall 
(d: nat).(\forall (i: nat).((le d i) \to ((lt i (plus d h)) \to ((subst1 i u 
(lift h d t) x) \to (eq T x (lift h d t))))))))))
\def
 \lambda (t: T).(\lambda (u: T).(\lambda (x: T).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (i: nat).(\lambda (H: (le d i)).(\lambda (H0: (lt i (plus d 
h))).(\lambda (H1: (subst1 i u (lift h d t) x)).(let TMP_1 \def (lift h d t) 
in (let TMP_3 \def (\lambda (t0: T).(let TMP_2 \def (lift h d t) in (eq T t0 
TMP_2))) in (let TMP_4 \def (lift h d t) in (let TMP_5 \def (refl_equal T 
TMP_4) in (let TMP_8 \def (\lambda (t2: T).(\lambda (H2: (subst0 i u (lift h 
d t) t2)).(let TMP_6 \def (lift h d t) in (let TMP_7 \def (eq T t2 TMP_6) in 
(subst0_gen_lift_false t u t2 h d i H H0 H2 TMP_7))))) in (subst1_ind i u 
TMP_1 TMP_3 TMP_5 TMP_8 x H1)))))))))))))).

theorem subst1_gen_lift_ge:
 \forall (u: T).(\forall (t1: T).(\forall (x: T).(\forall (i: nat).(\forall 
(h: nat).(\forall (d: nat).((subst1 i u (lift h d t1) x) \to ((le (plus d h) 
i) \to (ex2 T (\lambda (t2: T).(eq T x (lift h d t2))) (\lambda (t2: 
T).(subst1 (minus i h) u t1 t2))))))))))
\def
 \lambda (u: T).(\lambda (t1: T).(\lambda (x: T).(\lambda (i: nat).(\lambda 
(h: nat).(\lambda (d: nat).(\lambda (H: (subst1 i u (lift h d t1) 
x)).(\lambda (H0: (le (plus d h) i)).(let TMP_1 \def (lift h d t1) in (let 
TMP_6 \def (\lambda (t: T).(let TMP_3 \def (\lambda (t2: T).(let TMP_2 \def 
(lift h d t2) in (eq T t TMP_2))) in (let TMP_5 \def (\lambda (t2: T).(let 
TMP_4 \def (minus i h) in (subst1 TMP_4 u t1 t2))) in (ex2 T TMP_3 TMP_5)))) 
in (let TMP_9 \def (\lambda (t2: T).(let TMP_7 \def (lift h d t1) in (let 
TMP_8 \def (lift h d t2) in (eq T TMP_7 TMP_8)))) in (let TMP_11 \def 
(\lambda (t2: T).(let TMP_10 \def (minus i h) in (subst1 TMP_10 u t1 t2))) in 
(let TMP_12 \def (lift h d t1) in (let TMP_13 \def (refl_equal T TMP_12) in 
(let TMP_14 \def (minus i h) in (let TMP_15 \def (subst1_refl TMP_14 u t1) in 
(let TMP_16 \def (ex_intro2 T TMP_9 TMP_11 t1 TMP_13 TMP_15) in (let TMP_34 
\def (\lambda (t2: T).(\lambda (H1: (subst0 i u (lift h d t1) t2)).(let 
TMP_18 \def (\lambda (t3: T).(let TMP_17 \def (lift h d t3) in (eq T t2 
TMP_17))) in (let TMP_20 \def (\lambda (t3: T).(let TMP_19 \def (minus i h) 
in (subst0 TMP_19 u t1 t3))) in (let TMP_22 \def (\lambda (t3: T).(let TMP_21 
\def (lift h d t3) in (eq T t2 TMP_21))) in (let TMP_24 \def (\lambda (t3: 
T).(let TMP_23 \def (minus i h) in (subst1 TMP_23 u t1 t3))) in (let TMP_25 
\def (ex2 T TMP_22 TMP_24) in (let TMP_32 \def (\lambda (x0: T).(\lambda (H2: 
(eq T t2 (lift h d x0))).(\lambda (H3: (subst0 (minus i h) u t1 x0)).(let 
TMP_27 \def (\lambda (t3: T).(let TMP_26 \def (lift h d t3) in (eq T t2 
TMP_26))) in (let TMP_29 \def (\lambda (t3: T).(let TMP_28 \def (minus i h) 
in (subst1 TMP_28 u t1 t3))) in (let TMP_30 \def (minus i h) in (let TMP_31 
\def (subst1_single TMP_30 u t1 x0 H3) in (ex_intro2 T TMP_27 TMP_29 x0 H2 
TMP_31)))))))) in (let TMP_33 \def (subst0_gen_lift_ge u t1 t2 i h d H1 H0) 
in (ex2_ind T TMP_18 TMP_20 TMP_25 TMP_32 TMP_33)))))))))) in (subst1_ind i u 
TMP_1 TMP_6 TMP_16 TMP_34 x H)))))))))))))))))).

