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

include "basic_1/drop/fwd.ma".

theorem drop_skip_bind:
 \forall (h: nat).(\forall (d: nat).(\forall (c: C).(\forall (e: C).((drop h 
d c e) \to (\forall (b: B).(\forall (u: T).(drop h (S d) (CHead c (Bind b) 
(lift h d u)) (CHead e (Bind b) u))))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (c: C).(\lambda (e: C).(\lambda 
(H: (drop h d c e)).(\lambda (b: B).(\lambda (u: T).(let TMP_1 \def (Bind b) 
in (let TMP_2 \def (r TMP_1 d) in (let TMP_9 \def (\lambda (n: nat).(let 
TMP_3 \def (S d) in (let TMP_4 \def (Bind b) in (let TMP_5 \def (lift h n u) 
in (let TMP_6 \def (CHead c TMP_4 TMP_5) in (let TMP_7 \def (Bind b) in (let 
TMP_8 \def (CHead e TMP_7 u) in (drop h TMP_3 TMP_6 TMP_8)))))))) in (let 
TMP_10 \def (Bind b) in (let TMP_11 \def (drop_skip TMP_10 h d c e H u) in 
(let TMP_12 \def (refl_equal nat d) in (eq_ind nat TMP_2 TMP_9 TMP_11 d 
TMP_12))))))))))))).

theorem drop_skip_flat:
 \forall (h: nat).(\forall (d: nat).(\forall (c: C).(\forall (e: C).((drop h 
(S d) c e) \to (\forall (f: F).(\forall (u: T).(drop h (S d) (CHead c (Flat 
f) (lift h (S d) u)) (CHead e (Flat f) u))))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (c: C).(\lambda (e: C).(\lambda 
(H: (drop h (S d) c e)).(\lambda (f: F).(\lambda (u: T).(let TMP_1 \def (Flat 
f) in (let TMP_2 \def (r TMP_1 d) in (let TMP_9 \def (\lambda (n: nat).(let 
TMP_3 \def (S d) in (let TMP_4 \def (Flat f) in (let TMP_5 \def (lift h n u) 
in (let TMP_6 \def (CHead c TMP_4 TMP_5) in (let TMP_7 \def (Flat f) in (let 
TMP_8 \def (CHead e TMP_7 u) in (drop h TMP_3 TMP_6 TMP_8)))))))) in (let 
TMP_10 \def (Flat f) in (let TMP_11 \def (drop_skip TMP_10 h d c e H u) in 
(let TMP_12 \def (S d) in (let TMP_13 \def (S d) in (let TMP_14 \def 
(refl_equal nat TMP_13) in (eq_ind nat TMP_2 TMP_9 TMP_11 TMP_12 
TMP_14))))))))))))))).

theorem drop_ctail:
 \forall (c1: C).(\forall (c2: C).(\forall (d: nat).(\forall (h: nat).((drop 
h d c1 c2) \to (\forall (k: K).(\forall (u: T).(drop h d (CTail k u c1) 
(CTail k u c2))))))))
\def
 \lambda (c1: C).(let TMP_3 \def (\lambda (c: C).(\forall (c2: C).(\forall 
(d: nat).(\forall (h: nat).((drop h d c c2) \to (\forall (k: K).(\forall (u: 
T).(let TMP_1 \def (CTail k u c) in (let TMP_2 \def (CTail k u c2) in (drop h 
d TMP_1 TMP_2)))))))))) in (let TMP_32 \def (\lambda (n: nat).(\lambda (c2: 
C).(\lambda (d: nat).(\lambda (h: nat).(\lambda (H: (drop h d (CSort n) 
c2)).(\lambda (k: K).(\lambda (u: T).(let TMP_4 \def (CSort n) in (let TMP_5 
\def (eq C c2 TMP_4) in (let TMP_6 \def (eq nat h O) in (let TMP_7 \def (eq 
nat d O) in (let TMP_8 \def (CSort n) in (let TMP_9 \def (CTail k u TMP_8) in 
(let TMP_10 \def (CTail k u c2) in (let TMP_11 \def (drop h d TMP_9 TMP_10) 
in (let TMP_30 \def (\lambda (H0: (eq C c2 (CSort n))).(\lambda (H1: (eq nat 
h O)).(\lambda (H2: (eq nat d O)).(let TMP_15 \def (\lambda (n0: nat).(let 
TMP_12 \def (CSort n) in (let TMP_13 \def (CTail k u TMP_12) in (let TMP_14 
\def (CTail k u c2) in (drop n0 d TMP_13 TMP_14))))) in (let TMP_19 \def 
(\lambda (n0: nat).(let TMP_16 \def (CSort n) in (let TMP_17 \def (CTail k u 
TMP_16) in (let TMP_18 \def (CTail k u c2) in (drop O n0 TMP_17 TMP_18))))) 
in (let TMP_20 \def (CSort n) in (let TMP_24 \def (\lambda (c: C).(let TMP_21 
\def (CSort n) in (let TMP_22 \def (CTail k u TMP_21) in (let TMP_23 \def 
(CTail k u c) in (drop O O TMP_22 TMP_23))))) in (let TMP_25 \def (CSort n) 
in (let TMP_26 \def (CTail k u TMP_25) in (let TMP_27 \def (drop_refl TMP_26) 
in (let TMP_28 \def (eq_ind_r C TMP_20 TMP_24 TMP_27 c2 H0) in (let TMP_29 
\def (eq_ind_r nat O TMP_19 TMP_28 d H2) in (eq_ind_r nat O TMP_15 TMP_29 h 
H1))))))))))))) in (let TMP_31 \def (drop_gen_sort n h d c2 H) in (and3_ind 
TMP_5 TMP_6 TMP_7 TMP_11 TMP_30 TMP_31)))))))))))))))))) in (let TMP_106 \def 
(\lambda (c2: C).(\lambda (IHc: ((\forall (c3: C).(\forall (d: nat).(\forall 
(h: nat).((drop h d c2 c3) \to (\forall (k: K).(\forall (u: T).(drop h d 
(CTail k u c2) (CTail k u c3)))))))))).(\lambda (k: K).(\lambda (t: 
T).(\lambda (c3: C).(\lambda (d: nat).(let TMP_36 \def (\lambda (n: 
nat).(\forall (h: nat).((drop h n (CHead c2 k t) c3) \to (\forall (k0: 
K).(\forall (u: T).(let TMP_33 \def (CHead c2 k t) in (let TMP_34 \def (CTail 
k0 u TMP_33) in (let TMP_35 \def (CTail k0 u c3) in (drop h n TMP_34 
TMP_35))))))))) in (let TMP_58 \def (\lambda (h: nat).(let TMP_40 \def 
(\lambda (n: nat).((drop n O (CHead c2 k t) c3) \to (\forall (k0: K).(\forall 
(u: T).(let TMP_37 \def (CHead c2 k t) in (let TMP_38 \def (CTail k0 u 
TMP_37) in (let TMP_39 \def (CTail k0 u c3) in (drop n O TMP_38 
TMP_39)))))))) in (let TMP_51 \def (\lambda (H: (drop O O (CHead c2 k t) 
c3)).(\lambda (k0: K).(\lambda (u: T).(let TMP_41 \def (CHead c2 k t) in (let 
TMP_45 \def (\lambda (c: C).(let TMP_42 \def (CHead c2 k t) in (let TMP_43 
\def (CTail k0 u TMP_42) in (let TMP_44 \def (CTail k0 u c) in (drop O O 
TMP_43 TMP_44))))) in (let TMP_46 \def (CHead c2 k t) in (let TMP_47 \def 
(CTail k0 u TMP_46) in (let TMP_48 \def (drop_refl TMP_47) in (let TMP_49 
\def (CHead c2 k t) in (let TMP_50 \def (drop_gen_refl TMP_49 c3 H) in 
(eq_ind C TMP_41 TMP_45 TMP_48 c3 TMP_50))))))))))) in (let TMP_57 \def 
(\lambda (n: nat).(\lambda (_: (((drop n O (CHead c2 k t) c3) \to (\forall 
(k0: K).(\forall (u: T).(drop n O (CTail k0 u (CHead c2 k t)) (CTail k0 u 
c3))))))).(\lambda (H0: (drop (S n) O (CHead c2 k t) c3)).(\lambda (k0: 
K).(\lambda (u: T).(let TMP_52 \def (CTail k0 u c2) in (let TMP_53 \def 
(CTail k0 u c3) in (let TMP_54 \def (r k n) in (let TMP_55 \def 
(drop_gen_drop k c2 c3 t n H0) in (let TMP_56 \def (IHc c3 O TMP_54 TMP_55 k0 
u) in (drop_drop k n TMP_52 TMP_53 TMP_56 t))))))))))) in (nat_ind TMP_40 
TMP_51 TMP_57 h))))) in (let TMP_105 \def (\lambda (n: nat).(\lambda (H: 
((\forall (h: nat).((drop h n (CHead c2 k t) c3) \to (\forall (k0: 
K).(\forall (u: T).(drop h n (CTail k0 u (CHead c2 k t)) (CTail k0 u 
c3)))))))).(\lambda (h: nat).(\lambda (H0: (drop h (S n) (CHead c2 k t) 
c3)).(\lambda (k0: K).(\lambda (u: T).(let TMP_60 \def (\lambda (e: 
C).(\lambda (v: T).(let TMP_59 \def (CHead e k v) in (eq C c3 TMP_59)))) in 
(let TMP_63 \def (\lambda (_: C).(\lambda (v: T).(let TMP_61 \def (r k n) in 
(let TMP_62 \def (lift h TMP_61 v) in (eq T t TMP_62))))) in (let TMP_65 \def 
(\lambda (e: C).(\lambda (_: T).(let TMP_64 \def (r k n) in (drop h TMP_64 c2 
e)))) in (let TMP_66 \def (S n) in (let TMP_67 \def (CHead c2 k t) in (let 
TMP_68 \def (CTail k0 u TMP_67) in (let TMP_69 \def (CTail k0 u c3) in (let 
TMP_70 \def (drop h TMP_66 TMP_68 TMP_69) in (let TMP_103 \def (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H1: (eq C c3 (CHead x0 k x1))).(\lambda (H2: 
(eq T t (lift h (r k n) x1))).(\lambda (H3: (drop h (r k n) c2 x0)).(let 
TMP_74 \def (\lambda (c: C).(\forall (h0: nat).((drop h0 n (CHead c2 k t) c) 
\to (\forall (k1: K).(\forall (u0: T).(let TMP_71 \def (CHead c2 k t) in (let 
TMP_72 \def (CTail k1 u0 TMP_71) in (let TMP_73 \def (CTail k1 u0 c) in (drop 
h0 n TMP_72 TMP_73))))))))) in (let TMP_75 \def (CHead x0 k x1) in (let H4 
\def (eq_ind C c3 TMP_74 H TMP_75 H1) in (let TMP_76 \def (CHead x0 k x1) in 
(let TMP_81 \def (\lambda (c: C).(let TMP_77 \def (S n) in (let TMP_78 \def 
(CHead c2 k t) in (let TMP_79 \def (CTail k0 u TMP_78) in (let TMP_80 \def 
(CTail k0 u c) in (drop h TMP_77 TMP_79 TMP_80)))))) in (let TMP_86 \def 
(\lambda (t0: T).(\forall (h0: nat).((drop h0 n (CHead c2 k t0) (CHead x0 k 
x1)) \to (\forall (k1: K).(\forall (u0: T).(let TMP_82 \def (CHead c2 k t0) 
in (let TMP_83 \def (CTail k1 u0 TMP_82) in (let TMP_84 \def (CHead x0 k x1) 
in (let TMP_85 \def (CTail k1 u0 TMP_84) in (drop h0 n TMP_83 
TMP_85)))))))))) in (let TMP_87 \def (r k n) in (let TMP_88 \def (lift h 
TMP_87 x1) in (let H5 \def (eq_ind T t TMP_86 H4 TMP_88 H2) in (let TMP_89 
\def (r k n) in (let TMP_90 \def (lift h TMP_89 x1) in (let TMP_96 \def 
(\lambda (t0: T).(let TMP_91 \def (S n) in (let TMP_92 \def (CHead c2 k t0) 
in (let TMP_93 \def (CTail k0 u TMP_92) in (let TMP_94 \def (CHead x0 k x1) 
in (let TMP_95 \def (CTail k0 u TMP_94) in (drop h TMP_91 TMP_93 
TMP_95))))))) in (let TMP_97 \def (CTail k0 u c2) in (let TMP_98 \def (CTail 
k0 u x0) in (let TMP_99 \def (r k n) in (let TMP_100 \def (IHc x0 TMP_99 h H3 
k0 u) in (let TMP_101 \def (drop_skip k h n TMP_97 TMP_98 TMP_100 x1) in (let 
TMP_102 \def (eq_ind_r T TMP_90 TMP_96 TMP_101 t H2) in (eq_ind_r C TMP_76 
TMP_81 TMP_102 c3 H1)))))))))))))))))))))))) in (let TMP_104 \def 
(drop_gen_skip_l c2 c3 t h n k H0) in (ex3_2_ind C T TMP_60 TMP_63 TMP_65 
TMP_70 TMP_103 TMP_104))))))))))))))))) in (nat_ind TMP_36 TMP_58 TMP_105 
d)))))))))) in (C_ind TMP_3 TMP_32 TMP_106 c1)))).

theorem drop_conf_lt:
 \forall (k: K).(\forall (i: nat).(\forall (u: T).(\forall (c0: C).(\forall 
(c: C).((drop i O c (CHead c0 k u)) \to (\forall (e: C).(\forall (h: 
nat).(\forall (d: nat).((drop h (S (plus i d)) c e) \to (ex3_2 T C (\lambda 
(v: T).(\lambda (_: C).(eq T u (lift h (r k d) v)))) (\lambda (v: T).(\lambda 
(e0: C).(drop i O e (CHead e0 k v)))) (\lambda (_: T).(\lambda (e0: C).(drop 
h (r k d) c0 e0)))))))))))))
\def
 \lambda (k: K).(\lambda (i: nat).(let TMP_8 \def (\lambda (n: nat).(\forall 
(u: T).(\forall (c0: C).(\forall (c: C).((drop n O c (CHead c0 k u)) \to 
(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h (S (plus n d)) c 
e) \to (let TMP_3 \def (\lambda (v: T).(\lambda (_: C).(let TMP_1 \def (r k 
d) in (let TMP_2 \def (lift h TMP_1 v) in (eq T u TMP_2))))) in (let TMP_5 
\def (\lambda (v: T).(\lambda (e0: C).(let TMP_4 \def (CHead e0 k v) in (drop 
n O e TMP_4)))) in (let TMP_7 \def (\lambda (_: T).(\lambda (e0: C).(let 
TMP_6 \def (r k d) in (drop h TMP_6 c0 e0)))) in (ex3_2 T C TMP_3 TMP_5 
TMP_7))))))))))))) in (let TMP_74 \def (\lambda (u: T).(\lambda (c0: 
C).(\lambda (c: C).(\lambda (H: (drop O O c (CHead c0 k u))).(\lambda (e: 
C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H0: (drop h (S (plus O d)) c 
e)).(let TMP_11 \def (\lambda (c1: C).(let TMP_9 \def (plus O d) in (let 
TMP_10 \def (S TMP_9) in (drop h TMP_10 c1 e)))) in (let TMP_12 \def (CHead 
c0 k u) in (let TMP_13 \def (CHead c0 k u) in (let TMP_14 \def (drop_gen_refl 
c TMP_13 H) in (let H1 \def (eq_ind C c TMP_11 H0 TMP_12 TMP_14) in (let 
TMP_16 \def (\lambda (e0: C).(\lambda (v: T).(let TMP_15 \def (CHead e0 k v) 
in (eq C e TMP_15)))) in (let TMP_20 \def (\lambda (_: C).(\lambda (v: 
T).(let TMP_17 \def (plus O d) in (let TMP_18 \def (r k TMP_17) in (let 
TMP_19 \def (lift h TMP_18 v) in (eq T u TMP_19)))))) in (let TMP_23 \def 
(\lambda (e0: C).(\lambda (_: T).(let TMP_21 \def (plus O d) in (let TMP_22 
\def (r k TMP_21) in (drop h TMP_22 c0 e0))))) in (let TMP_26 \def (\lambda 
(v: T).(\lambda (_: C).(let TMP_24 \def (r k d) in (let TMP_25 \def (lift h 
TMP_24 v) in (eq T u TMP_25))))) in (let TMP_28 \def (\lambda (v: T).(\lambda 
(e0: C).(let TMP_27 \def (CHead e0 k v) in (drop O O e TMP_27)))) in (let 
TMP_30 \def (\lambda (_: T).(\lambda (e0: C).(let TMP_29 \def (r k d) in 
(drop h TMP_29 c0 e0)))) in (let TMP_31 \def (ex3_2 T C TMP_26 TMP_28 TMP_30) 
in (let TMP_71 \def (\lambda (x0: C).(\lambda (x1: T).(\lambda (H2: (eq C e 
(CHead x0 k x1))).(\lambda (H3: (eq T u (lift h (r k (plus O d)) 
x1))).(\lambda (H4: (drop h (r k (plus O d)) c0 x0)).(let TMP_32 \def (CHead 
x0 k x1) in (let TMP_40 \def (\lambda (c1: C).(let TMP_35 \def (\lambda (v: 
T).(\lambda (_: C).(let TMP_33 \def (r k d) in (let TMP_34 \def (lift h 
TMP_33 v) in (eq T u TMP_34))))) in (let TMP_37 \def (\lambda (v: T).(\lambda 
(e0: C).(let TMP_36 \def (CHead e0 k v) in (drop O O c1 TMP_36)))) in (let 
TMP_39 \def (\lambda (_: T).(\lambda (e0: C).(let TMP_38 \def (r k d) in 
(drop h TMP_38 c0 e0)))) in (ex3_2 T C TMP_35 TMP_37 TMP_39))))) in (let 
TMP_41 \def (plus O d) in (let TMP_42 \def (r k TMP_41) in (let TMP_43 \def 
(lift h TMP_42 x1) in (let TMP_52 \def (\lambda (t: T).(let TMP_46 \def 
(\lambda (v: T).(\lambda (_: C).(let TMP_44 \def (r k d) in (let TMP_45 \def 
(lift h TMP_44 v) in (eq T t TMP_45))))) in (let TMP_49 \def (\lambda (v: 
T).(\lambda (e0: C).(let TMP_47 \def (CHead x0 k x1) in (let TMP_48 \def 
(CHead e0 k v) in (drop O O TMP_47 TMP_48))))) in (let TMP_51 \def (\lambda 
(_: T).(\lambda (e0: C).(let TMP_50 \def (r k d) in (drop h TMP_50 c0 e0)))) 
in (ex3_2 T C TMP_46 TMP_49 TMP_51))))) in (let TMP_58 \def (\lambda (v: 
T).(\lambda (_: C).(let TMP_53 \def (plus O d) in (let TMP_54 \def (r k 
TMP_53) in (let TMP_55 \def (lift h TMP_54 x1) in (let TMP_56 \def (r k d) in 
(let TMP_57 \def (lift h TMP_56 v) in (eq T TMP_55 TMP_57)))))))) in (let 
TMP_61 \def (\lambda (v: T).(\lambda (e0: C).(let TMP_59 \def (CHead x0 k x1) 
in (let TMP_60 \def (CHead e0 k v) in (drop O O TMP_59 TMP_60))))) in (let 
TMP_63 \def (\lambda (_: T).(\lambda (e0: C).(let TMP_62 \def (r k d) in 
(drop h TMP_62 c0 e0)))) in (let TMP_64 \def (r k d) in (let TMP_65 \def 
(lift h TMP_64 x1) in (let TMP_66 \def (refl_equal T TMP_65) in (let TMP_67 
\def (CHead x0 k x1) in (let TMP_68 \def (drop_refl TMP_67) in (let TMP_69 
\def (ex3_2_intro T C TMP_58 TMP_61 TMP_63 x1 x0 TMP_66 TMP_68 H4) in (let 
TMP_70 \def (eq_ind_r T TMP_43 TMP_52 TMP_69 u H3) in (eq_ind_r C TMP_32 
TMP_40 TMP_70 e H2)))))))))))))))))))))) in (let TMP_72 \def (plus O d) in 
(let TMP_73 \def (drop_gen_skip_l c0 e u h TMP_72 k H1) in (ex3_2_ind C T 
TMP_16 TMP_20 TMP_23 TMP_31 TMP_71 TMP_73)))))))))))))))))))))))) in (let 
TMP_283 \def (\lambda (i0: nat).(\lambda (H: ((\forall (u: T).(\forall (c0: 
C).(\forall (c: C).((drop i0 O c (CHead c0 k u)) \to (\forall (e: C).(\forall 
(h: nat).(\forall (d: nat).((drop h (S (plus i0 d)) c e) \to (ex3_2 T C 
(\lambda (v: T).(\lambda (_: C).(eq T u (lift h (r k d) v)))) (\lambda (v: 
T).(\lambda (e0: C).(drop i0 O e (CHead e0 k v)))) (\lambda (_: T).(\lambda 
(e0: C).(drop h (r k d) c0 e0)))))))))))))).(\lambda (u: T).(\lambda (c0: 
C).(\lambda (c: C).(let TMP_83 \def (\lambda (c1: C).((drop (S i0) O c1 
(CHead c0 k u)) \to (\forall (e: C).(\forall (h: nat).(\forall (d: 
nat).((drop h (S (plus (S i0) d)) c1 e) \to (let TMP_77 \def (\lambda (v: 
T).(\lambda (_: C).(let TMP_75 \def (r k d) in (let TMP_76 \def (lift h 
TMP_75 v) in (eq T u TMP_76))))) in (let TMP_80 \def (\lambda (v: T).(\lambda 
(e0: C).(let TMP_78 \def (S i0) in (let TMP_79 \def (CHead e0 k v) in (drop 
TMP_78 O e TMP_79))))) in (let TMP_82 \def (\lambda (_: T).(\lambda (e0: 
C).(let TMP_81 \def (r k d) in (drop h TMP_81 c0 e0)))) in (ex3_2 T C TMP_77 
TMP_80 TMP_82)))))))))) in (let TMP_118 \def (\lambda (n: nat).(\lambda (_: 
(drop (S i0) O (CSort n) (CHead c0 k u))).(\lambda (e: C).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H1: (drop h (S (plus (S i0) d)) (CSort n) 
e)).(let TMP_84 \def (CSort n) in (let TMP_85 \def (eq C e TMP_84) in (let 
TMP_86 \def (eq nat h O) in (let TMP_87 \def (S i0) in (let TMP_88 \def (plus 
TMP_87 d) in (let TMP_89 \def (S TMP_88) in (let TMP_90 \def (eq nat TMP_89 
O) in (let TMP_93 \def (\lambda (v: T).(\lambda (_: C).(let TMP_91 \def (r k 
d) in (let TMP_92 \def (lift h TMP_91 v) in (eq T u TMP_92))))) in (let 
TMP_96 \def (\lambda (v: T).(\lambda (e0: C).(let TMP_94 \def (S i0) in (let 
TMP_95 \def (CHead e0 k v) in (drop TMP_94 O e TMP_95))))) in (let TMP_98 
\def (\lambda (_: T).(\lambda (e0: C).(let TMP_97 \def (r k d) in (drop h 
TMP_97 c0 e0)))) in (let TMP_99 \def (ex3_2 T C TMP_93 TMP_96 TMP_98) in (let 
TMP_113 \def (\lambda (_: (eq C e (CSort n))).(\lambda (_: (eq nat h 
O)).(\lambda (H4: (eq nat (S (plus (S i0) d)) O)).(let TMP_100 \def (S i0) in 
(let TMP_101 \def (plus TMP_100 d) in (let TMP_102 \def (S TMP_101) in (let 
TMP_103 \def (\lambda (ee: nat).(match ee with [O \Rightarrow False | (S _) 
\Rightarrow True])) in (let H5 \def (eq_ind nat TMP_102 TMP_103 I O H4) in 
(let TMP_106 \def (\lambda (v: T).(\lambda (_: C).(let TMP_104 \def (r k d) 
in (let TMP_105 \def (lift h TMP_104 v) in (eq T u TMP_105))))) in (let 
TMP_109 \def (\lambda (v: T).(\lambda (e0: C).(let TMP_107 \def (S i0) in 
(let TMP_108 \def (CHead e0 k v) in (drop TMP_107 O e TMP_108))))) in (let 
TMP_111 \def (\lambda (_: T).(\lambda (e0: C).(let TMP_110 \def (r k d) in 
(drop h TMP_110 c0 e0)))) in (let TMP_112 \def (ex3_2 T C TMP_106 TMP_109 
TMP_111) in (False_ind TMP_112 H5))))))))))))) in (let TMP_114 \def (S i0) in 
(let TMP_115 \def (plus TMP_114 d) in (let TMP_116 \def (S TMP_115) in (let 
TMP_117 \def (drop_gen_sort n h TMP_116 e H1) in (and3_ind TMP_85 TMP_86 
TMP_90 TMP_99 TMP_113 TMP_117))))))))))))))))))))))) in (let TMP_282 \def 
(\lambda (c1: C).(\lambda (H0: (((drop (S i0) O c1 (CHead c0 k u)) \to 
(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h (S (plus (S i0) 
d)) c1 e) \to (ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h (r k 
d) v)))) (\lambda (v: T).(\lambda (e0: C).(drop (S i0) O e (CHead e0 k v)))) 
(\lambda (_: T).(\lambda (e0: C).(drop h (r k d) c0 e0))))))))))).(\lambda 
(k0: K).(let TMP_127 \def (\lambda (k1: K).(\forall (t: T).((drop (S i0) O 
(CHead c1 k1 t) (CHead c0 k u)) \to (\forall (e: C).(\forall (h: 
nat).(\forall (d: nat).((drop h (S (plus (S i0) d)) (CHead c1 k1 t) e) \to 
(let TMP_121 \def (\lambda (v: T).(\lambda (_: C).(let TMP_119 \def (r k d) 
in (let TMP_120 \def (lift h TMP_119 v) in (eq T u TMP_120))))) in (let 
TMP_124 \def (\lambda (v: T).(\lambda (e0: C).(let TMP_122 \def (S i0) in 
(let TMP_123 \def (CHead e0 k v) in (drop TMP_122 O e TMP_123))))) in (let 
TMP_126 \def (\lambda (_: T).(\lambda (e0: C).(let TMP_125 \def (r k d) in 
(drop h TMP_125 c0 e0)))) in (ex3_2 T C TMP_121 TMP_124 TMP_126))))))))))) in 
(let TMP_203 \def (\lambda (b: B).(\lambda (t: T).(\lambda (H1: (drop (S i0) 
O (CHead c1 (Bind b) t) (CHead c0 k u))).(\lambda (e: C).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H2: (drop h (S (plus (S i0) d)) (CHead c1 
(Bind b) t) e)).(let TMP_130 \def (\lambda (e0: C).(\lambda (v: T).(let 
TMP_128 \def (Bind b) in (let TMP_129 \def (CHead e0 TMP_128 v) in (eq C e 
TMP_129))))) in (let TMP_136 \def (\lambda (_: C).(\lambda (v: T).(let 
TMP_131 \def (Bind b) in (let TMP_132 \def (S i0) in (let TMP_133 \def (plus 
TMP_132 d) in (let TMP_134 \def (r TMP_131 TMP_133) in (let TMP_135 \def 
(lift h TMP_134 v) in (eq T t TMP_135)))))))) in (let TMP_141 \def (\lambda 
(e0: C).(\lambda (_: T).(let TMP_137 \def (Bind b) in (let TMP_138 \def (S 
i0) in (let TMP_139 \def (plus TMP_138 d) in (let TMP_140 \def (r TMP_137 
TMP_139) in (drop h TMP_140 c1 e0))))))) in (let TMP_144 \def (\lambda (v: 
T).(\lambda (_: C).(let TMP_142 \def (r k d) in (let TMP_143 \def (lift h 
TMP_142 v) in (eq T u TMP_143))))) in (let TMP_147 \def (\lambda (v: 
T).(\lambda (e0: C).(let TMP_145 \def (S i0) in (let TMP_146 \def (CHead e0 k 
v) in (drop TMP_145 O e TMP_146))))) in (let TMP_149 \def (\lambda (_: 
T).(\lambda (e0: C).(let TMP_148 \def (r k d) in (drop h TMP_148 c0 e0)))) in 
(let TMP_150 \def (ex3_2 T C TMP_144 TMP_147 TMP_149) in (let TMP_198 \def 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (H3: (eq C e (CHead x0 (Bind b) 
x1))).(\lambda (_: (eq T t (lift h (r (Bind b) (plus (S i0) d)) 
x1))).(\lambda (H5: (drop h (r (Bind b) (plus (S i0) d)) c1 x0)).(let TMP_151 
\def (Bind b) in (let TMP_152 \def (CHead x0 TMP_151 x1) in (let TMP_161 \def 
(\lambda (c2: C).(let TMP_155 \def (\lambda (v: T).(\lambda (_: C).(let 
TMP_153 \def (r k d) in (let TMP_154 \def (lift h TMP_153 v) in (eq T u 
TMP_154))))) in (let TMP_158 \def (\lambda (v: T).(\lambda (e0: C).(let 
TMP_156 \def (S i0) in (let TMP_157 \def (CHead e0 k v) in (drop TMP_156 O c2 
TMP_157))))) in (let TMP_160 \def (\lambda (_: T).(\lambda (e0: C).(let 
TMP_159 \def (r k d) in (drop h TMP_159 c0 e0)))) in (ex3_2 T C TMP_155 
TMP_158 TMP_160))))) in (let TMP_162 \def (Bind b) in (let TMP_163 \def 
(CHead c0 k u) in (let TMP_164 \def (drop_gen_drop TMP_162 c1 TMP_163 t i0 
H1) in (let H6 \def (H u c0 c1 TMP_164 x0 h d H5) in (let TMP_167 \def 
(\lambda (v: T).(\lambda (_: C).(let TMP_165 \def (r k d) in (let TMP_166 
\def (lift h TMP_165 v) in (eq T u TMP_166))))) in (let TMP_169 \def (\lambda 
(v: T).(\lambda (e0: C).(let TMP_168 \def (CHead e0 k v) in (drop i0 O x0 
TMP_168)))) in (let TMP_171 \def (\lambda (_: T).(\lambda (e0: C).(let 
TMP_170 \def (r k d) in (drop h TMP_170 c0 e0)))) in (let TMP_174 \def 
(\lambda (v: T).(\lambda (_: C).(let TMP_172 \def (r k d) in (let TMP_173 
\def (lift h TMP_172 v) in (eq T u TMP_173))))) in (let TMP_179 \def (\lambda 
(v: T).(\lambda (e0: C).(let TMP_175 \def (S i0) in (let TMP_176 \def (Bind 
b) in (let TMP_177 \def (CHead x0 TMP_176 x1) in (let TMP_178 \def (CHead e0 
k v) in (drop TMP_175 O TMP_177 TMP_178))))))) in (let TMP_181 \def (\lambda 
(_: T).(\lambda (e0: C).(let TMP_180 \def (r k d) in (drop h TMP_180 c0 
e0)))) in (let TMP_182 \def (ex3_2 T C TMP_174 TMP_179 TMP_181) in (let 
TMP_196 \def (\lambda (x2: T).(\lambda (x3: C).(\lambda (H7: (eq T u (lift h 
(r k d) x2))).(\lambda (H8: (drop i0 O x0 (CHead x3 k x2))).(\lambda (H9: 
(drop h (r k d) c0 x3)).(let TMP_185 \def (\lambda (v: T).(\lambda (_: 
C).(let TMP_183 \def (r k d) in (let TMP_184 \def (lift h TMP_183 v) in (eq T 
u TMP_184))))) in (let TMP_190 \def (\lambda (v: T).(\lambda (e0: C).(let 
TMP_186 \def (S i0) in (let TMP_187 \def (Bind b) in (let TMP_188 \def (CHead 
x0 TMP_187 x1) in (let TMP_189 \def (CHead e0 k v) in (drop TMP_186 O TMP_188 
TMP_189))))))) in (let TMP_192 \def (\lambda (_: T).(\lambda (e0: C).(let 
TMP_191 \def (r k d) in (drop h TMP_191 c0 e0)))) in (let TMP_193 \def (Bind 
b) in (let TMP_194 \def (CHead x3 k x2) in (let TMP_195 \def (drop_drop 
TMP_193 i0 x0 TMP_194 H8 x1) in (ex3_2_intro T C TMP_185 TMP_190 TMP_192 x2 
x3 H7 TMP_195 H9)))))))))))) in (let TMP_197 \def (ex3_2_ind T C TMP_167 
TMP_169 TMP_171 TMP_182 TMP_196 H6) in (eq_ind_r C TMP_152 TMP_161 TMP_197 e 
H3)))))))))))))))))))))) in (let TMP_199 \def (S i0) in (let TMP_200 \def 
(plus TMP_199 d) in (let TMP_201 \def (Bind b) in (let TMP_202 \def 
(drop_gen_skip_l c1 e t h TMP_200 TMP_201 H2) in (ex3_2_ind C T TMP_130 
TMP_136 TMP_141 TMP_150 TMP_198 TMP_202)))))))))))))))))))) in (let TMP_281 
\def (\lambda (f: F).(\lambda (t: T).(\lambda (H1: (drop (S i0) O (CHead c1 
(Flat f) t) (CHead c0 k u))).(\lambda (e: C).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H2: (drop h (S (plus (S i0) d)) (CHead c1 (Flat f) t) e)).(let 
TMP_206 \def (\lambda (e0: C).(\lambda (v: T).(let TMP_204 \def (Flat f) in 
(let TMP_205 \def (CHead e0 TMP_204 v) in (eq C e TMP_205))))) in (let 
TMP_212 \def (\lambda (_: C).(\lambda (v: T).(let TMP_207 \def (Flat f) in 
(let TMP_208 \def (S i0) in (let TMP_209 \def (plus TMP_208 d) in (let 
TMP_210 \def (r TMP_207 TMP_209) in (let TMP_211 \def (lift h TMP_210 v) in 
(eq T t TMP_211)))))))) in (let TMP_217 \def (\lambda (e0: C).(\lambda (_: 
T).(let TMP_213 \def (Flat f) in (let TMP_214 \def (S i0) in (let TMP_215 
\def (plus TMP_214 d) in (let TMP_216 \def (r TMP_213 TMP_215) in (drop h 
TMP_216 c1 e0))))))) in (let TMP_220 \def (\lambda (v: T).(\lambda (_: 
C).(let TMP_218 \def (r k d) in (let TMP_219 \def (lift h TMP_218 v) in (eq T 
u TMP_219))))) in (let TMP_223 \def (\lambda (v: T).(\lambda (e0: C).(let 
TMP_221 \def (S i0) in (let TMP_222 \def (CHead e0 k v) in (drop TMP_221 O e 
TMP_222))))) in (let TMP_225 \def (\lambda (_: T).(\lambda (e0: C).(let 
TMP_224 \def (r k d) in (drop h TMP_224 c0 e0)))) in (let TMP_226 \def (ex3_2 
T C TMP_220 TMP_223 TMP_225) in (let TMP_276 \def (\lambda (x0: C).(\lambda 
(x1: T).(\lambda (H3: (eq C e (CHead x0 (Flat f) x1))).(\lambda (_: (eq T t 
(lift h (r (Flat f) (plus (S i0) d)) x1))).(\lambda (H5: (drop h (r (Flat f) 
(plus (S i0) d)) c1 x0)).(let TMP_227 \def (Flat f) in (let TMP_228 \def 
(CHead x0 TMP_227 x1) in (let TMP_237 \def (\lambda (c2: C).(let TMP_231 \def 
(\lambda (v: T).(\lambda (_: C).(let TMP_229 \def (r k d) in (let TMP_230 
\def (lift h TMP_229 v) in (eq T u TMP_230))))) in (let TMP_234 \def (\lambda 
(v: T).(\lambda (e0: C).(let TMP_232 \def (S i0) in (let TMP_233 \def (CHead 
e0 k v) in (drop TMP_232 O c2 TMP_233))))) in (let TMP_236 \def (\lambda (_: 
T).(\lambda (e0: C).(let TMP_235 \def (r k d) in (drop h TMP_235 c0 e0)))) in 
(ex3_2 T C TMP_231 TMP_234 TMP_236))))) in (let TMP_240 \def (\lambda (v: 
T).(\lambda (_: C).(let TMP_238 \def (r k d) in (let TMP_239 \def (lift h 
TMP_238 v) in (eq T u TMP_239))))) in (let TMP_243 \def (\lambda (v: 
T).(\lambda (e0: C).(let TMP_241 \def (S i0) in (let TMP_242 \def (CHead e0 k 
v) in (drop TMP_241 O x0 TMP_242))))) in (let TMP_245 \def (\lambda (_: 
T).(\lambda (e0: C).(let TMP_244 \def (r k d) in (drop h TMP_244 c0 e0)))) in 
(let TMP_248 \def (\lambda (v: T).(\lambda (_: C).(let TMP_246 \def (r k d) 
in (let TMP_247 \def (lift h TMP_246 v) in (eq T u TMP_247))))) in (let 
TMP_253 \def (\lambda (v: T).(\lambda (e0: C).(let TMP_249 \def (S i0) in 
(let TMP_250 \def (Flat f) in (let TMP_251 \def (CHead x0 TMP_250 x1) in (let 
TMP_252 \def (CHead e0 k v) in (drop TMP_249 O TMP_251 TMP_252))))))) in (let 
TMP_255 \def (\lambda (_: T).(\lambda (e0: C).(let TMP_254 \def (r k d) in 
(drop h TMP_254 c0 e0)))) in (let TMP_256 \def (ex3_2 T C TMP_248 TMP_253 
TMP_255) in (let TMP_270 \def (\lambda (x2: T).(\lambda (x3: C).(\lambda (H6: 
(eq T u (lift h (r k d) x2))).(\lambda (H7: (drop (S i0) O x0 (CHead x3 k 
x2))).(\lambda (H8: (drop h (r k d) c0 x3)).(let TMP_259 \def (\lambda (v: 
T).(\lambda (_: C).(let TMP_257 \def (r k d) in (let TMP_258 \def (lift h 
TMP_257 v) in (eq T u TMP_258))))) in (let TMP_264 \def (\lambda (v: 
T).(\lambda (e0: C).(let TMP_260 \def (S i0) in (let TMP_261 \def (Flat f) in 
(let TMP_262 \def (CHead x0 TMP_261 x1) in (let TMP_263 \def (CHead e0 k v) 
in (drop TMP_260 O TMP_262 TMP_263))))))) in (let TMP_266 \def (\lambda (_: 
T).(\lambda (e0: C).(let TMP_265 \def (r k d) in (drop h TMP_265 c0 e0)))) in 
(let TMP_267 \def (Flat f) in (let TMP_268 \def (CHead x3 k x2) in (let 
TMP_269 \def (drop_drop TMP_267 i0 x0 TMP_268 H7 x1) in (ex3_2_intro T C 
TMP_259 TMP_264 TMP_266 x2 x3 H6 TMP_269 H8)))))))))))) in (let TMP_271 \def 
(Flat f) in (let TMP_272 \def (CHead c0 k u) in (let TMP_273 \def 
(drop_gen_drop TMP_271 c1 TMP_272 t i0 H1) in (let TMP_274 \def (H0 TMP_273 
x0 h d H5) in (let TMP_275 \def (ex3_2_ind T C TMP_240 TMP_243 TMP_245 
TMP_256 TMP_270 TMP_274) in (eq_ind_r C TMP_228 TMP_237 TMP_275 e 
H3)))))))))))))))))))))) in (let TMP_277 \def (S i0) in (let TMP_278 \def 
(plus TMP_277 d) in (let TMP_279 \def (Flat f) in (let TMP_280 \def 
(drop_gen_skip_l c1 e t h TMP_278 TMP_279 H2) in (ex3_2_ind C T TMP_206 
TMP_212 TMP_217 TMP_226 TMP_276 TMP_280)))))))))))))))))))) in (K_ind TMP_127 
TMP_203 TMP_281 k0))))))) in (C_ind TMP_83 TMP_118 TMP_282 c))))))))) in 
(nat_ind TMP_8 TMP_74 TMP_283 i))))).

theorem drop_conf_ge:
 \forall (i: nat).(\forall (a: C).(\forall (c: C).((drop i O c a) \to 
(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) \to ((le 
(plus d h) i) \to (drop (minus i h) O e a)))))))))
\def
 \lambda (i: nat).(let TMP_2 \def (\lambda (n: nat).(\forall (a: C).(\forall 
(c: C).((drop n O c a) \to (\forall (e: C).(\forall (h: nat).(\forall (d: 
nat).((drop h d c e) \to ((le (plus d h) n) \to (let TMP_1 \def (minus n h) 
in (drop TMP_1 O e a))))))))))) in (let TMP_23 \def (\lambda (a: C).(\lambda 
(c: C).(\lambda (H: (drop O O c a)).(\lambda (e: C).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H0: (drop h d c e)).(\lambda (H1: (le (plus 
d h) O)).(let TMP_3 \def (\lambda (c0: C).(drop h d c0 e)) in (let TMP_4 \def 
(drop_gen_refl c a H) in (let H2 \def (eq_ind C c TMP_3 H0 a TMP_4) in (let 
TMP_5 \def (plus d h) in (let H_y \def (le_n_O_eq TMP_5 H1) in (let TMP_6 
\def (eq nat d O) in (let TMP_7 \def (eq nat h O) in (let TMP_8 \def (minus O 
h) in (let TMP_9 \def (drop TMP_8 O e a) in (let TMP_19 \def (\lambda (H3: 
(eq nat d O)).(\lambda (H4: (eq nat h O)).(let TMP_10 \def (\lambda (n: 
nat).(drop h n a e)) in (let H5 \def (eq_ind nat d TMP_10 H2 O H3) in (let 
TMP_11 \def (\lambda (n: nat).(drop n O a e)) in (let H6 \def (eq_ind nat h 
TMP_11 H5 O H4) in (let TMP_13 \def (\lambda (n: nat).(let TMP_12 \def (minus 
O n) in (drop TMP_12 O e a))) in (let TMP_15 \def (\lambda (c0: C).(let 
TMP_14 \def (minus O O) in (drop TMP_14 O c0 a))) in (let TMP_16 \def 
(drop_refl a) in (let TMP_17 \def (drop_gen_refl a e H6) in (let TMP_18 \def 
(eq_ind C a TMP_15 TMP_16 e TMP_17) in (eq_ind_r nat O TMP_13 TMP_18 h 
H4)))))))))))) in (let TMP_20 \def (plus d h) in (let TMP_21 \def (sym_eq nat 
O TMP_20 H_y) in (let TMP_22 \def (plus_O d h TMP_21) in (land_ind TMP_6 
TMP_7 TMP_9 TMP_19 TMP_22)))))))))))))))))))))) in (let TMP_227 \def (\lambda 
(i0: nat).(\lambda (H: ((\forall (a: C).(\forall (c: C).((drop i0 O c a) \to 
(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) \to ((le 
(plus d h) i0) \to (drop (minus i0 h) O e a))))))))))).(\lambda (a: 
C).(\lambda (c: C).(let TMP_26 \def (\lambda (c0: C).((drop (S i0) O c0 a) 
\to (\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h d c0 e) \to 
((le (plus d h) (S i0)) \to (let TMP_24 \def (S i0) in (let TMP_25 \def 
(minus TMP_24 h) in (drop TMP_25 O e a)))))))))) in (let TMP_75 \def (\lambda 
(n: nat).(\lambda (H0: (drop (S i0) O (CSort n) a)).(\lambda (e: C).(\lambda 
(h: nat).(\lambda (d: nat).(\lambda (H1: (drop h d (CSort n) e)).(\lambda 
(H2: (le (plus d h) (S i0))).(let TMP_27 \def (CSort n) in (let TMP_28 \def 
(eq C e TMP_27) in (let TMP_29 \def (eq nat h O) in (let TMP_30 \def (eq nat 
d O) in (let TMP_31 \def (S i0) in (let TMP_32 \def (minus TMP_31 h) in (let 
TMP_33 \def (drop TMP_32 O e a) in (let TMP_73 \def (\lambda (H3: (eq C e 
(CSort n))).(\lambda (H4: (eq nat h O)).(\lambda (H5: (eq nat d O)).(let 
TMP_34 \def (CSort n) in (let TMP_35 \def (eq C a TMP_34) in (let TMP_36 \def 
(S i0) in (let TMP_37 \def (eq nat TMP_36 O) in (let TMP_38 \def (eq nat O O) 
in (let TMP_39 \def (S i0) in (let TMP_40 \def (minus TMP_39 h) in (let 
TMP_41 \def (drop TMP_40 O e a) in (let TMP_70 \def (\lambda (H6: (eq C a 
(CSort n))).(\lambda (H7: (eq nat (S i0) O)).(\lambda (_: (eq nat O O)).(let 
TMP_44 \def (\lambda (n0: nat).(let TMP_42 \def (plus n0 h) in (let TMP_43 
\def (S i0) in (le TMP_42 TMP_43)))) in (let H9 \def (eq_ind nat d TMP_44 H2 
O H5) in (let TMP_47 \def (\lambda (n0: nat).(let TMP_45 \def (plus O n0) in 
(let TMP_46 \def (S i0) in (le TMP_45 TMP_46)))) in (let H10 \def (eq_ind nat 
h TMP_47 H9 O H4) in (let TMP_50 \def (\lambda (n0: nat).(let TMP_48 \def (S 
i0) in (let TMP_49 \def (minus TMP_48 n0) in (drop TMP_49 O e a)))) in (let 
TMP_51 \def (CSort n) in (let TMP_54 \def (\lambda (c0: C).(let TMP_52 \def 
(S i0) in (let TMP_53 \def (minus TMP_52 O) in (drop TMP_53 O c0 a)))) in 
(let TMP_55 \def (CSort n) in (let TMP_59 \def (\lambda (c0: C).(let TMP_56 
\def (S i0) in (let TMP_57 \def (minus TMP_56 O) in (let TMP_58 \def (CSort 
n) in (drop TMP_57 O TMP_58 c0))))) in (let TMP_60 \def (S i0) in (let TMP_61 
\def (\lambda (ee: nat).(match ee with [O \Rightarrow False | (S _) 
\Rightarrow True])) in (let H11 \def (eq_ind nat TMP_60 TMP_61 I O H7) in 
(let TMP_62 \def (S i0) in (let TMP_63 \def (minus TMP_62 O) in (let TMP_64 
\def (CSort n) in (let TMP_65 \def (CSort n) in (let TMP_66 \def (drop TMP_63 
O TMP_64 TMP_65) in (let TMP_67 \def (False_ind TMP_66 H11) in (let TMP_68 
\def (eq_ind_r C TMP_55 TMP_59 TMP_67 a H6) in (let TMP_69 \def (eq_ind_r C 
TMP_51 TMP_54 TMP_68 e H3) in (eq_ind_r nat O TMP_50 TMP_69 h 
H4)))))))))))))))))))))))) in (let TMP_71 \def (S i0) in (let TMP_72 \def 
(drop_gen_sort n TMP_71 O a H0) in (and3_ind TMP_35 TMP_37 TMP_38 TMP_41 
TMP_70 TMP_72))))))))))))))) in (let TMP_74 \def (drop_gen_sort n h d e H1) 
in (and3_ind TMP_28 TMP_29 TMP_30 TMP_33 TMP_73 TMP_74))))))))))))))))) in 
(let TMP_226 \def (\lambda (c0: C).(\lambda (H0: (((drop (S i0) O c0 a) \to 
(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h d c0 e) \to ((le 
(plus d h) (S i0)) \to (drop (minus (S i0) h) O e a))))))))).(\lambda (k: 
K).(let TMP_78 \def (\lambda (k0: K).(\forall (t: T).((drop (S i0) O (CHead 
c0 k0 t) a) \to (\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h 
d (CHead c0 k0 t) e) \to ((le (plus d h) (S i0)) \to (let TMP_76 \def (S i0) 
in (let TMP_77 \def (minus TMP_76 h) in (drop TMP_77 O e a))))))))))) in (let 
TMP_148 \def (\lambda (b: B).(\lambda (t: T).(\lambda (H1: (drop (S i0) O 
(CHead c0 (Bind b) t) a)).(\lambda (e: C).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H2: (drop h d (CHead c0 (Bind b) t) e)).(\lambda (H3: (le 
(plus d h) (S i0))).(let TMP_81 \def (\lambda (n: nat).((drop h n (CHead c0 
(Bind b) t) e) \to ((le (plus n h) (S i0)) \to (let TMP_79 \def (S i0) in 
(let TMP_80 \def (minus TMP_79 h) in (drop TMP_80 O e a)))))) in (let TMP_105 
\def (\lambda (H4: (drop h O (CHead c0 (Bind b) t) e)).(\lambda (H5: (le 
(plus O h) (S i0))).(let TMP_84 \def (\lambda (n: nat).((drop n O (CHead c0 
(Bind b) t) e) \to ((le (plus O n) (S i0)) \to (let TMP_82 \def (S i0) in 
(let TMP_83 \def (minus TMP_82 n) in (drop TMP_83 O e a)))))) in (let TMP_97 
\def (\lambda (H6: (drop O O (CHead c0 (Bind b) t) e)).(\lambda (_: (le (plus 
O O) (S i0))).(let TMP_85 \def (Bind b) in (let TMP_86 \def (CHead c0 TMP_85 
t) in (let TMP_89 \def (\lambda (c1: C).(let TMP_87 \def (S i0) in (let 
TMP_88 \def (minus TMP_87 O) in (drop TMP_88 O c1 a)))) in (let TMP_90 \def 
(Bind b) in (let TMP_91 \def (Bind b) in (let TMP_92 \def (drop_gen_drop 
TMP_91 c0 a t i0 H1) in (let TMP_93 \def (drop_drop TMP_90 i0 c0 a TMP_92 t) 
in (let TMP_94 \def (Bind b) in (let TMP_95 \def (CHead c0 TMP_94 t) in (let 
TMP_96 \def (drop_gen_refl TMP_95 e H6) in (eq_ind C TMP_86 TMP_89 TMP_93 e 
TMP_96))))))))))))) in (let TMP_104 \def (\lambda (h0: nat).(\lambda (_: 
(((drop h0 O (CHead c0 (Bind b) t) e) \to ((le (plus O h0) (S i0)) \to (drop 
(minus (S i0) h0) O e a))))).(\lambda (H6: (drop (S h0) O (CHead c0 (Bind b) 
t) e)).(\lambda (H7: (le (plus O (S h0)) (S i0))).(let TMP_98 \def (Bind b) 
in (let TMP_99 \def (drop_gen_drop TMP_98 c0 a t i0 H1) in (let TMP_100 \def 
(Bind b) in (let TMP_101 \def (drop_gen_drop TMP_100 c0 e t h0 H6) in (let 
TMP_102 \def (plus O h0) in (let TMP_103 \def (le_S_n TMP_102 i0 H7) in (H a 
c0 TMP_99 e h0 O TMP_101 TMP_103))))))))))) in (nat_ind TMP_84 TMP_97 TMP_104 
h H4 H5)))))) in (let TMP_147 \def (\lambda (d0: nat).(\lambda (_: (((drop h 
d0 (CHead c0 (Bind b) t) e) \to ((le (plus d0 h) (S i0)) \to (drop (minus (S 
i0) h) O e a))))).(\lambda (H4: (drop h (S d0) (CHead c0 (Bind b) t) 
e)).(\lambda (H5: (le (plus (S d0) h) (S i0))).(let TMP_108 \def (\lambda 
(e0: C).(\lambda (v: T).(let TMP_106 \def (Bind b) in (let TMP_107 \def 
(CHead e0 TMP_106 v) in (eq C e TMP_107))))) in (let TMP_112 \def (\lambda 
(_: C).(\lambda (v: T).(let TMP_109 \def (Bind b) in (let TMP_110 \def (r 
TMP_109 d0) in (let TMP_111 \def (lift h TMP_110 v) in (eq T t TMP_111)))))) 
in (let TMP_115 \def (\lambda (e0: C).(\lambda (_: T).(let TMP_113 \def (Bind 
b) in (let TMP_114 \def (r TMP_113 d0) in (drop h TMP_114 c0 e0))))) in (let 
TMP_116 \def (S i0) in (let TMP_117 \def (minus TMP_116 h) in (let TMP_118 
\def (drop TMP_117 O e a) in (let TMP_144 \def (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H6: (eq C e (CHead x0 (Bind b) x1))).(\lambda (_: (eq T t (lift 
h (r (Bind b) d0) x1))).(\lambda (H8: (drop h (r (Bind b) d0) c0 x0)).(let 
TMP_119 \def (Bind b) in (let TMP_120 \def (CHead x0 TMP_119 x1) in (let 
TMP_123 \def (\lambda (c1: C).(let TMP_121 \def (S i0) in (let TMP_122 \def 
(minus TMP_121 h) in (drop TMP_122 O c1 a)))) in (let TMP_124 \def (minus i0 
h) in (let TMP_125 \def (S TMP_124) in (let TMP_128 \def (\lambda (n: 
nat).(let TMP_126 \def (Bind b) in (let TMP_127 \def (CHead x0 TMP_126 x1) in 
(drop n O TMP_127 a)))) in (let TMP_129 \def (Bind b) in (let TMP_130 \def 
(minus i0 h) in (let TMP_131 \def (Bind b) in (let TMP_132 \def 
(drop_gen_drop TMP_131 c0 a t i0 H1) in (let TMP_133 \def (plus d0 h) in (let 
TMP_134 \def (le_S_n TMP_133 i0 H5) in (let TMP_135 \def (H a c0 TMP_132 x0 h 
d0 H8 TMP_134) in (let TMP_136 \def (drop_drop TMP_129 TMP_130 x0 a TMP_135 
x1) in (let TMP_137 \def (S i0) in (let TMP_138 \def (minus TMP_137 h) in 
(let TMP_139 \def (plus d0 h) in (let TMP_140 \def (le_S_n TMP_139 i0 H5) in 
(let TMP_141 \def (le_trans_plus_r d0 h i0 TMP_140) in (let TMP_142 \def 
(minus_Sn_m i0 h TMP_141) in (let TMP_143 \def (eq_ind nat TMP_125 TMP_128 
TMP_136 TMP_138 TMP_142) in (eq_ind_r C TMP_120 TMP_123 TMP_143 e 
H6))))))))))))))))))))))))))) in (let TMP_145 \def (Bind b) in (let TMP_146 
\def (drop_gen_skip_l c0 e t h d0 TMP_145 H4) in (ex3_2_ind C T TMP_108 
TMP_112 TMP_115 TMP_118 TMP_144 TMP_146)))))))))))))) in (nat_ind TMP_81 
TMP_105 TMP_147 d H2 H3)))))))))))) in (let TMP_225 \def (\lambda (f: 
F).(\lambda (t: T).(\lambda (H1: (drop (S i0) O (CHead c0 (Flat f) t) 
a)).(\lambda (e: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H2: (drop h 
d (CHead c0 (Flat f) t) e)).(\lambda (H3: (le (plus d h) (S i0))).(let 
TMP_151 \def (\lambda (n: nat).((drop h n (CHead c0 (Flat f) t) e) \to ((le 
(plus n h) (S i0)) \to (let TMP_149 \def (S i0) in (let TMP_150 \def (minus 
TMP_149 h) in (drop TMP_150 O e a)))))) in (let TMP_174 \def (\lambda (H4: 
(drop h O (CHead c0 (Flat f) t) e)).(\lambda (H5: (le (plus O h) (S 
i0))).(let TMP_154 \def (\lambda (n: nat).((drop n O (CHead c0 (Flat f) t) e) 
\to ((le (plus O n) (S i0)) \to (let TMP_152 \def (S i0) in (let TMP_153 \def 
(minus TMP_152 n) in (drop TMP_153 O e a)))))) in (let TMP_167 \def (\lambda 
(H6: (drop O O (CHead c0 (Flat f) t) e)).(\lambda (_: (le (plus O O) (S 
i0))).(let TMP_155 \def (Flat f) in (let TMP_156 \def (CHead c0 TMP_155 t) in 
(let TMP_159 \def (\lambda (c1: C).(let TMP_157 \def (S i0) in (let TMP_158 
\def (minus TMP_157 O) in (drop TMP_158 O c1 a)))) in (let TMP_160 \def (Flat 
f) in (let TMP_161 \def (Flat f) in (let TMP_162 \def (drop_gen_drop TMP_161 
c0 a t i0 H1) in (let TMP_163 \def (drop_drop TMP_160 i0 c0 a TMP_162 t) in 
(let TMP_164 \def (Flat f) in (let TMP_165 \def (CHead c0 TMP_164 t) in (let 
TMP_166 \def (drop_gen_refl TMP_165 e H6) in (eq_ind C TMP_156 TMP_159 
TMP_163 e TMP_166))))))))))))) in (let TMP_173 \def (\lambda (h0: 
nat).(\lambda (_: (((drop h0 O (CHead c0 (Flat f) t) e) \to ((le (plus O h0) 
(S i0)) \to (drop (minus (S i0) h0) O e a))))).(\lambda (H6: (drop (S h0) O 
(CHead c0 (Flat f) t) e)).(\lambda (H7: (le (plus O (S h0)) (S i0))).(let 
TMP_168 \def (Flat f) in (let TMP_169 \def (drop_gen_drop TMP_168 c0 a t i0 
H1) in (let TMP_170 \def (S h0) in (let TMP_171 \def (Flat f) in (let TMP_172 
\def (drop_gen_drop TMP_171 c0 e t h0 H6) in (H0 TMP_169 e TMP_170 O TMP_172 
H7)))))))))) in (nat_ind TMP_154 TMP_167 TMP_173 h H4 H5)))))) in (let 
TMP_224 \def (\lambda (d0: nat).(\lambda (_: (((drop h d0 (CHead c0 (Flat f) 
t) e) \to ((le (plus d0 h) (S i0)) \to (drop (minus (S i0) h) O e 
a))))).(\lambda (H4: (drop h (S d0) (CHead c0 (Flat f) t) e)).(\lambda (H5: 
(le (plus (S d0) h) (S i0))).(let TMP_177 \def (\lambda (e0: C).(\lambda (v: 
T).(let TMP_175 \def (Flat f) in (let TMP_176 \def (CHead e0 TMP_175 v) in 
(eq C e TMP_176))))) in (let TMP_181 \def (\lambda (_: C).(\lambda (v: 
T).(let TMP_178 \def (Flat f) in (let TMP_179 \def (r TMP_178 d0) in (let 
TMP_180 \def (lift h TMP_179 v) in (eq T t TMP_180)))))) in (let TMP_184 \def 
(\lambda (e0: C).(\lambda (_: T).(let TMP_182 \def (Flat f) in (let TMP_183 
\def (r TMP_182 d0) in (drop h TMP_183 c0 e0))))) in (let TMP_185 \def (S i0) 
in (let TMP_186 \def (minus TMP_185 h) in (let TMP_187 \def (drop TMP_186 O e 
a) in (let TMP_221 \def (\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: (eq C 
e (CHead x0 (Flat f) x1))).(\lambda (_: (eq T t (lift h (r (Flat f) d0) 
x1))).(\lambda (H8: (drop h (r (Flat f) d0) c0 x0)).(let TMP_188 \def (Flat 
f) in (let TMP_189 \def (CHead x0 TMP_188 x1) in (let TMP_192 \def (\lambda 
(c1: C).(let TMP_190 \def (S i0) in (let TMP_191 \def (minus TMP_190 h) in 
(drop TMP_191 O c1 a)))) in (let TMP_193 \def (S i0) in (let TMP_194 \def 
(minus TMP_193 h) in (let TMP_195 \def (\lambda (n: nat).(drop n O x0 a)) in 
(let TMP_196 \def (Flat f) in (let TMP_197 \def (drop_gen_drop TMP_196 c0 a t 
i0 H1) in (let TMP_198 \def (S d0) in (let TMP_199 \def (H0 TMP_197 x0 h 
TMP_198 H8 H5) in (let TMP_200 \def (minus i0 h) in (let TMP_201 \def (S 
TMP_200) in (let TMP_202 \def (plus d0 h) in (let TMP_203 \def (le_S_n 
TMP_202 i0 H5) in (let TMP_204 \def (le_trans_plus_r d0 h i0 TMP_203) in (let 
TMP_205 \def (minus_Sn_m i0 h TMP_204) in (let H9 \def (eq_ind_r nat TMP_194 
TMP_195 TMP_199 TMP_201 TMP_205) in (let TMP_206 \def (minus i0 h) in (let 
TMP_207 \def (S TMP_206) in (let TMP_210 \def (\lambda (n: nat).(let TMP_208 
\def (Flat f) in (let TMP_209 \def (CHead x0 TMP_208 x1) in (drop n O TMP_209 
a)))) in (let TMP_211 \def (Flat f) in (let TMP_212 \def (minus i0 h) in (let 
TMP_213 \def (drop_drop TMP_211 TMP_212 x0 a H9 x1) in (let TMP_214 \def (S 
i0) in (let TMP_215 \def (minus TMP_214 h) in (let TMP_216 \def (plus d0 h) 
in (let TMP_217 \def (le_S_n TMP_216 i0 H5) in (let TMP_218 \def 
(le_trans_plus_r d0 h i0 TMP_217) in (let TMP_219 \def (minus_Sn_m i0 h 
TMP_218) in (let TMP_220 \def (eq_ind nat TMP_207 TMP_210 TMP_213 TMP_215 
TMP_219) in (eq_ind_r C TMP_189 TMP_192 TMP_220 e 
H6)))))))))))))))))))))))))))))))))))) in (let TMP_222 \def (Flat f) in (let 
TMP_223 \def (drop_gen_skip_l c0 e t h d0 TMP_222 H4) in (ex3_2_ind C T 
TMP_177 TMP_181 TMP_184 TMP_187 TMP_221 TMP_223)))))))))))))) in (nat_ind 
TMP_151 TMP_174 TMP_224 d H2 H3)))))))))))) in (K_ind TMP_78 TMP_148 TMP_225 
k))))))) in (C_ind TMP_26 TMP_75 TMP_226 c)))))))) in (nat_ind TMP_2 TMP_23 
TMP_227 i)))).

theorem drop_conf_rev:
 \forall (j: nat).(\forall (e1: C).(\forall (e2: C).((drop j O e1 e2) \to 
(\forall (c2: C).(\forall (i: nat).((drop i O c2 e2) \to (ex2 C (\lambda (c1: 
C).(drop j O c1 c2)) (\lambda (c1: C).(drop i j c1 e1)))))))))
\def
 \lambda (j: nat).(let TMP_3 \def (\lambda (n: nat).(\forall (e1: C).(\forall 
(e2: C).((drop n O e1 e2) \to (\forall (c2: C).(\forall (i: nat).((drop i O 
c2 e2) \to (let TMP_1 \def (\lambda (c1: C).(drop n O c1 c2)) in (let TMP_2 
\def (\lambda (c1: C).(drop i n c1 e1)) in (ex2 C TMP_1 TMP_2)))))))))) in 
(let TMP_9 \def (\lambda (e1: C).(\lambda (e2: C).(\lambda (H: (drop O O e1 
e2)).(\lambda (c2: C).(\lambda (i: nat).(\lambda (H0: (drop i O c2 e2)).(let 
TMP_4 \def (\lambda (c: C).(drop i O c2 c)) in (let TMP_5 \def (drop_gen_refl 
e1 e2 H) in (let H1 \def (eq_ind_r C e2 TMP_4 H0 e1 TMP_5) in (let TMP_6 \def 
(\lambda (c1: C).(drop O O c1 c2)) in (let TMP_7 \def (\lambda (c1: C).(drop 
i O c1 e1)) in (let TMP_8 \def (drop_refl c2) in (ex_intro2 C TMP_6 TMP_7 c2 
TMP_8 H1))))))))))))) in (let TMP_108 \def (\lambda (j0: nat).(\lambda (IHj: 
((\forall (e1: C).(\forall (e2: C).((drop j0 O e1 e2) \to (\forall (c2: 
C).(\forall (i: nat).((drop i O c2 e2) \to (ex2 C (\lambda (c1: C).(drop j0 O 
c1 c2)) (\lambda (c1: C).(drop i j0 c1 e1))))))))))).(\lambda (e1: C).(let 
TMP_14 \def (\lambda (c: C).(\forall (e2: C).((drop (S j0) O c e2) \to 
(\forall (c2: C).(\forall (i: nat).((drop i O c2 e2) \to (let TMP_11 \def 
(\lambda (c1: C).(let TMP_10 \def (S j0) in (drop TMP_10 O c1 c2))) in (let 
TMP_13 \def (\lambda (c1: C).(let TMP_12 \def (S j0) in (drop i TMP_12 c1 
c))) in (ex2 C TMP_11 TMP_13))))))))) in (let TMP_39 \def (\lambda (n: 
nat).(\lambda (e2: C).(\lambda (H: (drop (S j0) O (CSort n) e2)).(\lambda 
(c2: C).(\lambda (i: nat).(\lambda (H0: (drop i O c2 e2)).(let TMP_15 \def 
(CSort n) in (let TMP_16 \def (eq C e2 TMP_15) in (let TMP_17 \def (S j0) in 
(let TMP_18 \def (eq nat TMP_17 O) in (let TMP_19 \def (eq nat O O) in (let 
TMP_21 \def (\lambda (c1: C).(let TMP_20 \def (S j0) in (drop TMP_20 O c1 
c2))) in (let TMP_24 \def (\lambda (c1: C).(let TMP_22 \def (S j0) in (let 
TMP_23 \def (CSort n) in (drop i TMP_22 c1 TMP_23)))) in (let TMP_25 \def 
(ex2 C TMP_21 TMP_24) in (let TMP_36 \def (\lambda (H1: (eq C e2 (CSort 
n))).(\lambda (H2: (eq nat (S j0) O)).(\lambda (_: (eq nat O O)).(let TMP_26 
\def (\lambda (c: C).(drop i O c2 c)) in (let TMP_27 \def (CSort n) in (let 
H4 \def (eq_ind C e2 TMP_26 H0 TMP_27 H1) in (let TMP_28 \def (S j0) in (let 
TMP_29 \def (\lambda (ee: nat).(match ee with [O \Rightarrow False | (S _) 
\Rightarrow True])) in (let H5 \def (eq_ind nat TMP_28 TMP_29 I O H2) in (let 
TMP_31 \def (\lambda (c1: C).(let TMP_30 \def (S j0) in (drop TMP_30 O c1 
c2))) in (let TMP_34 \def (\lambda (c1: C).(let TMP_32 \def (S j0) in (let 
TMP_33 \def (CSort n) in (drop i TMP_32 c1 TMP_33)))) in (let TMP_35 \def 
(ex2 C TMP_31 TMP_34) in (False_ind TMP_35 H5))))))))))))) in (let TMP_37 
\def (S j0) in (let TMP_38 \def (drop_gen_sort n TMP_37 O e2 H) in (and3_ind 
TMP_16 TMP_18 TMP_19 TMP_25 TMP_36 TMP_38)))))))))))))))))) in (let TMP_107 
\def (\lambda (e2: C).(\lambda (IHe1: ((\forall (e3: C).((drop (S j0) O e2 
e3) \to (\forall (c2: C).(\forall (i: nat).((drop i O c2 e3) \to (ex2 C 
(\lambda (c1: C).(drop (S j0) O c1 c2)) (\lambda (c1: C).(drop i (S j0) c1 
e2)))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (e3: C).(\lambda (H: 
(drop (S j0) O (CHead e2 k t) e3)).(\lambda (c2: C).(\lambda (i: 
nat).(\lambda (H0: (drop i O c2 e3)).(let TMP_45 \def (\lambda (k0: K).((drop 
(r k0 j0) O e2 e3) \to (let TMP_41 \def (\lambda (c1: C).(let TMP_40 \def (S 
j0) in (drop TMP_40 O c1 c2))) in (let TMP_44 \def (\lambda (c1: C).(let 
TMP_42 \def (S j0) in (let TMP_43 \def (CHead e2 k0 t) in (drop i TMP_42 c1 
TMP_43)))) in (ex2 C TMP_41 TMP_44))))) in (let TMP_74 \def (\lambda (b: 
B).(\lambda (H1: (drop (r (Bind b) j0) O e2 e3)).(let H_x \def (IHj e2 e3 H1 
c2 i H0) in (let H2 \def H_x in (let TMP_46 \def (\lambda (c1: C).(drop j0 O 
c1 c2)) in (let TMP_47 \def (\lambda (c1: C).(drop i j0 c1 e2)) in (let 
TMP_49 \def (\lambda (c1: C).(let TMP_48 \def (S j0) in (drop TMP_48 O c1 
c2))) in (let TMP_53 \def (\lambda (c1: C).(let TMP_50 \def (S j0) in (let 
TMP_51 \def (Bind b) in (let TMP_52 \def (CHead e2 TMP_51 t) in (drop i 
TMP_50 c1 TMP_52))))) in (let TMP_54 \def (ex2 C TMP_49 TMP_53) in (let 
TMP_73 \def (\lambda (x: C).(\lambda (H3: (drop j0 O x c2)).(\lambda (H4: 
(drop i j0 x e2)).(let TMP_56 \def (\lambda (c1: C).(let TMP_55 \def (S j0) 
in (drop TMP_55 O c1 c2))) in (let TMP_60 \def (\lambda (c1: C).(let TMP_57 
\def (S j0) in (let TMP_58 \def (Bind b) in (let TMP_59 \def (CHead e2 TMP_58 
t) in (drop i TMP_57 c1 TMP_59))))) in (let TMP_61 \def (Bind b) in (let 
TMP_62 \def (Bind b) in (let TMP_63 \def (r TMP_62 j0) in (let TMP_64 \def 
(lift i TMP_63 t) in (let TMP_65 \def (CHead x TMP_61 TMP_64) in (let TMP_66 
\def (Bind b) in (let TMP_67 \def (Bind b) in (let TMP_68 \def (r TMP_67 j0) 
in (let TMP_69 \def (lift i TMP_68 t) in (let TMP_70 \def (drop_drop TMP_66 
j0 x c2 H3 TMP_69) in (let TMP_71 \def (Bind b) in (let TMP_72 \def 
(drop_skip TMP_71 i j0 x e2 H4 t) in (ex_intro2 C TMP_56 TMP_60 TMP_65 TMP_70 
TMP_72)))))))))))))))))) in (ex2_ind C TMP_46 TMP_47 TMP_54 TMP_73 
H2))))))))))) in (let TMP_105 \def (\lambda (f: F).(\lambda (H1: (drop (r 
(Flat f) j0) O e2 e3)).(let H_x \def (IHe1 e3 H1 c2 i H0) in (let H2 \def H_x 
in (let TMP_76 \def (\lambda (c1: C).(let TMP_75 \def (S j0) in (drop TMP_75 
O c1 c2))) in (let TMP_78 \def (\lambda (c1: C).(let TMP_77 \def (S j0) in 
(drop i TMP_77 c1 e2))) in (let TMP_80 \def (\lambda (c1: C).(let TMP_79 \def 
(S j0) in (drop TMP_79 O c1 c2))) in (let TMP_84 \def (\lambda (c1: C).(let 
TMP_81 \def (S j0) in (let TMP_82 \def (Flat f) in (let TMP_83 \def (CHead e2 
TMP_82 t) in (drop i TMP_81 c1 TMP_83))))) in (let TMP_85 \def (ex2 C TMP_80 
TMP_84) in (let TMP_104 \def (\lambda (x: C).(\lambda (H3: (drop (S j0) O x 
c2)).(\lambda (H4: (drop i (S j0) x e2)).(let TMP_87 \def (\lambda (c1: 
C).(let TMP_86 \def (S j0) in (drop TMP_86 O c1 c2))) in (let TMP_91 \def 
(\lambda (c1: C).(let TMP_88 \def (S j0) in (let TMP_89 \def (Flat f) in (let 
TMP_90 \def (CHead e2 TMP_89 t) in (drop i TMP_88 c1 TMP_90))))) in (let 
TMP_92 \def (Flat f) in (let TMP_93 \def (Flat f) in (let TMP_94 \def (r 
TMP_93 j0) in (let TMP_95 \def (lift i TMP_94 t) in (let TMP_96 \def (CHead x 
TMP_92 TMP_95) in (let TMP_97 \def (Flat f) in (let TMP_98 \def (Flat f) in 
(let TMP_99 \def (r TMP_98 j0) in (let TMP_100 \def (lift i TMP_99 t) in (let 
TMP_101 \def (drop_drop TMP_97 j0 x c2 H3 TMP_100) in (let TMP_102 \def (Flat 
f) in (let TMP_103 \def (drop_skip TMP_102 i j0 x e2 H4 t) in (ex_intro2 C 
TMP_87 TMP_91 TMP_96 TMP_101 TMP_103)))))))))))))))))) in (ex2_ind C TMP_76 
TMP_78 TMP_85 TMP_104 H2))))))))))) in (let TMP_106 \def (drop_gen_drop k e2 
e3 t j0 H) in (K_ind TMP_45 TMP_74 TMP_105 k TMP_106)))))))))))))) in (C_ind 
TMP_14 TMP_39 TMP_107 e1))))))) in (nat_ind TMP_3 TMP_9 TMP_108 j)))).

theorem drop_trans_le:
 \forall (i: nat).(\forall (d: nat).((le i d) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (h: nat).((drop h d c1 c2) \to (\forall (e2: C).((drop i O 
c2 e2) \to (ex2 C (\lambda (e1: C).(drop i O c1 e1)) (\lambda (e1: C).(drop h 
(minus d i) e1 e2)))))))))))
\def
 \lambda (i: nat).(let TMP_4 \def (\lambda (n: nat).(\forall (d: nat).((le n 
d) \to (\forall (c1: C).(\forall (c2: C).(\forall (h: nat).((drop h d c1 c2) 
\to (\forall (e2: C).((drop n O c2 e2) \to (let TMP_1 \def (\lambda (e1: 
C).(drop n O c1 e1)) in (let TMP_3 \def (\lambda (e1: C).(let TMP_2 \def 
(minus d n) in (drop h TMP_2 e1 e2))) in (ex2 C TMP_1 TMP_3)))))))))))) in 
(let TMP_16 \def (\lambda (d: nat).(\lambda (_: (le O d)).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (h: nat).(\lambda (H0: (drop h d c1 
c2)).(\lambda (e2: C).(\lambda (H1: (drop O O c2 e2)).(let TMP_5 \def 
(\lambda (c: C).(drop h d c1 c)) in (let TMP_6 \def (drop_gen_refl c2 e2 H1) 
in (let H2 \def (eq_ind C c2 TMP_5 H0 e2 TMP_6) in (let TMP_9 \def (\lambda 
(n: nat).(let TMP_7 \def (\lambda (e1: C).(drop O O c1 e1)) in (let TMP_8 
\def (\lambda (e1: C).(drop h n e1 e2)) in (ex2 C TMP_7 TMP_8)))) in (let 
TMP_10 \def (\lambda (e1: C).(drop O O c1 e1)) in (let TMP_11 \def (\lambda 
(e1: C).(drop h d e1 e2)) in (let TMP_12 \def (drop_refl c1) in (let TMP_13 
\def (ex_intro2 C TMP_10 TMP_11 c1 TMP_12 H2) in (let TMP_14 \def (minus d O) 
in (let TMP_15 \def (minus_n_O d) in (eq_ind nat d TMP_9 TMP_13 TMP_14 
TMP_15))))))))))))))))))) in (let TMP_271 \def (\lambda (i0: nat).(\lambda 
(IHi: ((\forall (d: nat).((le i0 d) \to (\forall (c1: C).(\forall (c2: 
C).(\forall (h: nat).((drop h d c1 c2) \to (\forall (e2: C).((drop i0 O c2 
e2) \to (ex2 C (\lambda (e1: C).(drop i0 O c1 e1)) (\lambda (e1: C).(drop h 
(minus d i0) e1 e2))))))))))))).(\lambda (d: nat).(let TMP_22 \def (\lambda 
(n: nat).((le (S i0) n) \to (\forall (c1: C).(\forall (c2: C).(\forall (h: 
nat).((drop h n c1 c2) \to (\forall (e2: C).((drop (S i0) O c2 e2) \to (let 
TMP_18 \def (\lambda (e1: C).(let TMP_17 \def (S i0) in (drop TMP_17 O c1 
e1))) in (let TMP_21 \def (\lambda (e1: C).(let TMP_19 \def (S i0) in (let 
TMP_20 \def (minus n TMP_19) in (drop h TMP_20 e1 e2)))) in (ex2 C TMP_18 
TMP_21))))))))))) in (let TMP_42 \def (\lambda (H: (le (S i0) O)).(\lambda 
(c1: C).(\lambda (c2: C).(\lambda (h: nat).(\lambda (_: (drop h O c1 
c2)).(\lambda (e2: C).(\lambda (_: (drop (S i0) O c2 e2)).(let TMP_24 \def 
(\lambda (n: nat).(let TMP_23 \def (S n) in (eq nat O TMP_23))) in (let 
TMP_25 \def (\lambda (n: nat).(le i0 n)) in (let TMP_27 \def (\lambda (e1: 
C).(let TMP_26 \def (S i0) in (drop TMP_26 O c1 e1))) in (let TMP_30 \def 
(\lambda (e1: C).(let TMP_28 \def (S i0) in (let TMP_29 \def (minus O TMP_28) 
in (drop h TMP_29 e1 e2)))) in (let TMP_31 \def (ex2 C TMP_27 TMP_30) in (let 
TMP_40 \def (\lambda (x: nat).(\lambda (H2: (eq nat O (S x))).(\lambda (_: 
(le i0 x)).(let TMP_32 \def (\lambda (ee: nat).(match ee with [O \Rightarrow 
True | (S _) \Rightarrow False])) in (let TMP_33 \def (S x) in (let H4 \def 
(eq_ind nat O TMP_32 I TMP_33 H2) in (let TMP_35 \def (\lambda (e1: C).(let 
TMP_34 \def (S i0) in (drop TMP_34 O c1 e1))) in (let TMP_38 \def (\lambda 
(e1: C).(let TMP_36 \def (S i0) in (let TMP_37 \def (minus O TMP_36) in (drop 
h TMP_37 e1 e2)))) in (let TMP_39 \def (ex2 C TMP_35 TMP_38) in (False_ind 
TMP_39 H4)))))))))) in (let TMP_41 \def (le_gen_S i0 O H) in (ex2_ind nat 
TMP_24 TMP_25 TMP_31 TMP_40 TMP_41))))))))))))))) in (let TMP_270 \def 
(\lambda (d0: nat).(\lambda (_: (((le (S i0) d0) \to (\forall (c1: 
C).(\forall (c2: C).(\forall (h: nat).((drop h d0 c1 c2) \to (\forall (e2: 
C).((drop (S i0) O c2 e2) \to (ex2 C (\lambda (e1: C).(drop (S i0) O c1 e1)) 
(\lambda (e1: C).(drop h (minus d0 (S i0)) e1 e2)))))))))))).(\lambda (H: (le 
(S i0) (S d0))).(\lambda (c1: C).(let TMP_49 \def (\lambda (c: C).(\forall 
(c2: C).(\forall (h: nat).((drop h (S d0) c c2) \to (\forall (e2: C).((drop 
(S i0) O c2 e2) \to (let TMP_44 \def (\lambda (e1: C).(let TMP_43 \def (S i0) 
in (drop TMP_43 O c e1))) in (let TMP_48 \def (\lambda (e1: C).(let TMP_45 
\def (S d0) in (let TMP_46 \def (S i0) in (let TMP_47 \def (minus TMP_45 
TMP_46) in (drop h TMP_47 e1 e2))))) in (ex2 C TMP_44 TMP_48))))))))) in (let 
TMP_106 \def (\lambda (n: nat).(\lambda (c2: C).(\lambda (h: nat).(\lambda 
(H0: (drop h (S d0) (CSort n) c2)).(\lambda (e2: C).(\lambda (H1: (drop (S 
i0) O c2 e2)).(let TMP_50 \def (CSort n) in (let TMP_51 \def (eq C c2 TMP_50) 
in (let TMP_52 \def (eq nat h O) in (let TMP_53 \def (S d0) in (let TMP_54 
\def (eq nat TMP_53 O) in (let TMP_57 \def (\lambda (e1: C).(let TMP_55 \def 
(S i0) in (let TMP_56 \def (CSort n) in (drop TMP_55 O TMP_56 e1)))) in (let 
TMP_61 \def (\lambda (e1: C).(let TMP_58 \def (S d0) in (let TMP_59 \def (S 
i0) in (let TMP_60 \def (minus TMP_58 TMP_59) in (drop h TMP_60 e1 e2))))) in 
(let TMP_62 \def (ex2 C TMP_57 TMP_61) in (let TMP_103 \def (\lambda (H2: (eq 
C c2 (CSort n))).(\lambda (_: (eq nat h O)).(\lambda (_: (eq nat (S d0) 
O)).(let TMP_64 \def (\lambda (c: C).(let TMP_63 \def (S i0) in (drop TMP_63 
O c e2))) in (let TMP_65 \def (CSort n) in (let H5 \def (eq_ind C c2 TMP_64 
H1 TMP_65 H2) in (let TMP_66 \def (CSort n) in (let TMP_67 \def (eq C e2 
TMP_66) in (let TMP_68 \def (S i0) in (let TMP_69 \def (eq nat TMP_68 O) in 
(let TMP_70 \def (eq nat O O) in (let TMP_73 \def (\lambda (e1: C).(let 
TMP_71 \def (S i0) in (let TMP_72 \def (CSort n) in (drop TMP_71 O TMP_72 
e1)))) in (let TMP_77 \def (\lambda (e1: C).(let TMP_74 \def (S d0) in (let 
TMP_75 \def (S i0) in (let TMP_76 \def (minus TMP_74 TMP_75) in (drop h 
TMP_76 e1 e2))))) in (let TMP_78 \def (ex2 C TMP_73 TMP_77) in (let TMP_100 
\def (\lambda (H6: (eq C e2 (CSort n))).(\lambda (H7: (eq nat (S i0) 
O)).(\lambda (_: (eq nat O O)).(let TMP_79 \def (CSort n) in (let TMP_87 \def 
(\lambda (c: C).(let TMP_82 \def (\lambda (e1: C).(let TMP_80 \def (S i0) in 
(let TMP_81 \def (CSort n) in (drop TMP_80 O TMP_81 e1)))) in (let TMP_86 
\def (\lambda (e1: C).(let TMP_83 \def (S d0) in (let TMP_84 \def (S i0) in 
(let TMP_85 \def (minus TMP_83 TMP_84) in (drop h TMP_85 e1 c))))) in (ex2 C 
TMP_82 TMP_86)))) in (let TMP_88 \def (S i0) in (let TMP_89 \def (\lambda 
(ee: nat).(match ee with [O \Rightarrow False | (S _) \Rightarrow True])) in 
(let H9 \def (eq_ind nat TMP_88 TMP_89 I O H7) in (let TMP_92 \def (\lambda 
(e1: C).(let TMP_90 \def (S i0) in (let TMP_91 \def (CSort n) in (drop TMP_90 
O TMP_91 e1)))) in (let TMP_97 \def (\lambda (e1: C).(let TMP_93 \def (S d0) 
in (let TMP_94 \def (S i0) in (let TMP_95 \def (minus TMP_93 TMP_94) in (let 
TMP_96 \def (CSort n) in (drop h TMP_95 e1 TMP_96)))))) in (let TMP_98 \def 
(ex2 C TMP_92 TMP_97) in (let TMP_99 \def (False_ind TMP_98 H9) in (eq_ind_r 
C TMP_79 TMP_87 TMP_99 e2 H6))))))))))))) in (let TMP_101 \def (S i0) in (let 
TMP_102 \def (drop_gen_sort n TMP_101 O e2 H5) in (and3_ind TMP_67 TMP_69 
TMP_70 TMP_78 TMP_100 TMP_102)))))))))))))))))) in (let TMP_104 \def (S d0) 
in (let TMP_105 \def (drop_gen_sort n h TMP_104 c2 H0) in (and3_ind TMP_51 
TMP_52 TMP_54 TMP_62 TMP_103 TMP_105)))))))))))))))))) in (let TMP_269 \def 
(\lambda (c2: C).(\lambda (IHc: ((\forall (c3: C).(\forall (h: nat).((drop h 
(S d0) c2 c3) \to (\forall (e2: C).((drop (S i0) O c3 e2) \to (ex2 C (\lambda 
(e1: C).(drop (S i0) O c2 e1)) (\lambda (e1: C).(drop h (minus (S d0) (S i0)) 
e1 e2)))))))))).(\lambda (k: K).(let TMP_114 \def (\lambda (k0: K).(\forall 
(t: T).(\forall (c3: C).(\forall (h: nat).((drop h (S d0) (CHead c2 k0 t) c3) 
\to (\forall (e2: C).((drop (S i0) O c3 e2) \to (let TMP_109 \def (\lambda 
(e1: C).(let TMP_107 \def (S i0) in (let TMP_108 \def (CHead c2 k0 t) in 
(drop TMP_107 O TMP_108 e1)))) in (let TMP_113 \def (\lambda (e1: C).(let 
TMP_110 \def (S d0) in (let TMP_111 \def (S i0) in (let TMP_112 \def (minus 
TMP_110 TMP_111) in (drop h TMP_112 e1 e2))))) in (ex2 C TMP_109 
TMP_113)))))))))) in (let TMP_190 \def (\lambda (b: B).(\lambda (t: 
T).(\lambda (c3: C).(\lambda (h: nat).(\lambda (H0: (drop h (S d0) (CHead c2 
(Bind b) t) c3)).(\lambda (e2: C).(\lambda (H1: (drop (S i0) O c3 e2)).(let 
TMP_117 \def (\lambda (e: C).(\lambda (v: T).(let TMP_115 \def (Bind b) in 
(let TMP_116 \def (CHead e TMP_115 v) in (eq C c3 TMP_116))))) in (let 
TMP_121 \def (\lambda (_: C).(\lambda (v: T).(let TMP_118 \def (Bind b) in 
(let TMP_119 \def (r TMP_118 d0) in (let TMP_120 \def (lift h TMP_119 v) in 
(eq T t TMP_120)))))) in (let TMP_124 \def (\lambda (e: C).(\lambda (_: 
T).(let TMP_122 \def (Bind b) in (let TMP_123 \def (r TMP_122 d0) in (drop h 
TMP_123 c2 e))))) in (let TMP_128 \def (\lambda (e1: C).(let TMP_125 \def (S 
i0) in (let TMP_126 \def (Bind b) in (let TMP_127 \def (CHead c2 TMP_126 t) 
in (drop TMP_125 O TMP_127 e1))))) in (let TMP_132 \def (\lambda (e1: C).(let 
TMP_129 \def (S d0) in (let TMP_130 \def (S i0) in (let TMP_131 \def (minus 
TMP_129 TMP_130) in (drop h TMP_131 e1 e2))))) in (let TMP_133 \def (ex2 C 
TMP_128 TMP_132) in (let TMP_187 \def (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H2: (eq C c3 (CHead x0 (Bind b) x1))).(\lambda (H3: (eq T t 
(lift h (r (Bind b) d0) x1))).(\lambda (H4: (drop h (r (Bind b) d0) c2 
x0)).(let TMP_135 \def (\lambda (c: C).(let TMP_134 \def (S i0) in (drop 
TMP_134 O c e2))) in (let TMP_136 \def (Bind b) in (let TMP_137 \def (CHead 
x0 TMP_136 x1) in (let H5 \def (eq_ind C c3 TMP_135 H1 TMP_137 H2) in (let 
TMP_138 \def (Bind b) in (let TMP_139 \def (r TMP_138 d0) in (let TMP_140 
\def (lift h TMP_139 x1) in (let TMP_149 \def (\lambda (t0: T).(let TMP_144 
\def (\lambda (e1: C).(let TMP_141 \def (S i0) in (let TMP_142 \def (Bind b) 
in (let TMP_143 \def (CHead c2 TMP_142 t0) in (drop TMP_141 O TMP_143 e1))))) 
in (let TMP_148 \def (\lambda (e1: C).(let TMP_145 \def (S d0) in (let 
TMP_146 \def (S i0) in (let TMP_147 \def (minus TMP_145 TMP_146) in (drop h 
TMP_147 e1 e2))))) in (ex2 C TMP_144 TMP_148)))) in (let TMP_150 \def 
(\lambda (e1: C).(drop i0 O c2 e1)) in (let TMP_152 \def (\lambda (e1: 
C).(let TMP_151 \def (minus d0 i0) in (drop h TMP_151 e1 e2))) in (let 
TMP_159 \def (\lambda (e1: C).(let TMP_153 \def (S i0) in (let TMP_154 \def 
(Bind b) in (let TMP_155 \def (Bind b) in (let TMP_156 \def (r TMP_155 d0) in 
(let TMP_157 \def (lift h TMP_156 x1) in (let TMP_158 \def (CHead c2 TMP_154 
TMP_157) in (drop TMP_153 O TMP_158 e1)))))))) in (let TMP_163 \def (\lambda 
(e1: C).(let TMP_160 \def (S d0) in (let TMP_161 \def (S i0) in (let TMP_162 
\def (minus TMP_160 TMP_161) in (drop h TMP_162 e1 e2))))) in (let TMP_164 
\def (ex2 C TMP_159 TMP_163) in (let TMP_181 \def (\lambda (x: C).(\lambda 
(H6: (drop i0 O c2 x)).(\lambda (H7: (drop h (minus d0 i0) x e2)).(let 
TMP_171 \def (\lambda (e1: C).(let TMP_165 \def (S i0) in (let TMP_166 \def 
(Bind b) in (let TMP_167 \def (Bind b) in (let TMP_168 \def (r TMP_167 d0) in 
(let TMP_169 \def (lift h TMP_168 x1) in (let TMP_170 \def (CHead c2 TMP_166 
TMP_169) in (drop TMP_165 O TMP_170 e1)))))))) in (let TMP_175 \def (\lambda 
(e1: C).(let TMP_172 \def (S d0) in (let TMP_173 \def (S i0) in (let TMP_174 
\def (minus TMP_172 TMP_173) in (drop h TMP_174 e1 e2))))) in (let TMP_176 
\def (Bind b) in (let TMP_177 \def (Bind b) in (let TMP_178 \def (r TMP_177 
d0) in (let TMP_179 \def (lift h TMP_178 x1) in (let TMP_180 \def (drop_drop 
TMP_176 i0 c2 x H6 TMP_179) in (ex_intro2 C TMP_171 TMP_175 x TMP_180 
H7))))))))))) in (let TMP_182 \def (le_S_n i0 d0 H) in (let TMP_183 \def 
(Bind b) in (let TMP_184 \def (drop_gen_drop TMP_183 x0 e2 x1 i0 H5) in (let 
TMP_185 \def (IHi d0 TMP_182 c2 x0 h H4 e2 TMP_184) in (let TMP_186 \def 
(ex2_ind C TMP_150 TMP_152 TMP_164 TMP_181 TMP_185) in (eq_ind_r T TMP_140 
TMP_149 TMP_186 t H3))))))))))))))))))))))))) in (let TMP_188 \def (Bind b) 
in (let TMP_189 \def (drop_gen_skip_l c2 c3 t h d0 TMP_188 H0) in (ex3_2_ind 
C T TMP_117 TMP_121 TMP_124 TMP_133 TMP_187 TMP_189))))))))))))))))) in (let 
TMP_268 \def (\lambda (f: F).(\lambda (t: T).(\lambda (c3: C).(\lambda (h: 
nat).(\lambda (H0: (drop h (S d0) (CHead c2 (Flat f) t) c3)).(\lambda (e2: 
C).(\lambda (H1: (drop (S i0) O c3 e2)).(let TMP_193 \def (\lambda (e: 
C).(\lambda (v: T).(let TMP_191 \def (Flat f) in (let TMP_192 \def (CHead e 
TMP_191 v) in (eq C c3 TMP_192))))) in (let TMP_197 \def (\lambda (_: 
C).(\lambda (v: T).(let TMP_194 \def (Flat f) in (let TMP_195 \def (r TMP_194 
d0) in (let TMP_196 \def (lift h TMP_195 v) in (eq T t TMP_196)))))) in (let 
TMP_200 \def (\lambda (e: C).(\lambda (_: T).(let TMP_198 \def (Flat f) in 
(let TMP_199 \def (r TMP_198 d0) in (drop h TMP_199 c2 e))))) in (let TMP_204 
\def (\lambda (e1: C).(let TMP_201 \def (S i0) in (let TMP_202 \def (Flat f) 
in (let TMP_203 \def (CHead c2 TMP_202 t) in (drop TMP_201 O TMP_203 e1))))) 
in (let TMP_208 \def (\lambda (e1: C).(let TMP_205 \def (S d0) in (let 
TMP_206 \def (S i0) in (let TMP_207 \def (minus TMP_205 TMP_206) in (drop h 
TMP_207 e1 e2))))) in (let TMP_209 \def (ex2 C TMP_204 TMP_208) in (let 
TMP_265 \def (\lambda (x0: C).(\lambda (x1: T).(\lambda (H2: (eq C c3 (CHead 
x0 (Flat f) x1))).(\lambda (H3: (eq T t (lift h (r (Flat f) d0) 
x1))).(\lambda (H4: (drop h (r (Flat f) d0) c2 x0)).(let TMP_211 \def 
(\lambda (c: C).(let TMP_210 \def (S i0) in (drop TMP_210 O c e2))) in (let 
TMP_212 \def (Flat f) in (let TMP_213 \def (CHead x0 TMP_212 x1) in (let H5 
\def (eq_ind C c3 TMP_211 H1 TMP_213 H2) in (let TMP_214 \def (Flat f) in 
(let TMP_215 \def (r TMP_214 d0) in (let TMP_216 \def (lift h TMP_215 x1) in 
(let TMP_225 \def (\lambda (t0: T).(let TMP_220 \def (\lambda (e1: C).(let 
TMP_217 \def (S i0) in (let TMP_218 \def (Flat f) in (let TMP_219 \def (CHead 
c2 TMP_218 t0) in (drop TMP_217 O TMP_219 e1))))) in (let TMP_224 \def 
(\lambda (e1: C).(let TMP_221 \def (S d0) in (let TMP_222 \def (S i0) in (let 
TMP_223 \def (minus TMP_221 TMP_222) in (drop h TMP_223 e1 e2))))) in (ex2 C 
TMP_220 TMP_224)))) in (let TMP_227 \def (\lambda (e1: C).(let TMP_226 \def 
(S i0) in (drop TMP_226 O c2 e1))) in (let TMP_231 \def (\lambda (e1: C).(let 
TMP_228 \def (S d0) in (let TMP_229 \def (S i0) in (let TMP_230 \def (minus 
TMP_228 TMP_229) in (drop h TMP_230 e1 e2))))) in (let TMP_238 \def (\lambda 
(e1: C).(let TMP_232 \def (S i0) in (let TMP_233 \def (Flat f) in (let 
TMP_234 \def (Flat f) in (let TMP_235 \def (r TMP_234 d0) in (let TMP_236 
\def (lift h TMP_235 x1) in (let TMP_237 \def (CHead c2 TMP_233 TMP_236) in 
(drop TMP_232 O TMP_237 e1)))))))) in (let TMP_242 \def (\lambda (e1: C).(let 
TMP_239 \def (S d0) in (let TMP_240 \def (S i0) in (let TMP_241 \def (minus 
TMP_239 TMP_240) in (drop h TMP_241 e1 e2))))) in (let TMP_243 \def (ex2 C 
TMP_238 TMP_242) in (let TMP_260 \def (\lambda (x: C).(\lambda (H6: (drop (S 
i0) O c2 x)).(\lambda (H7: (drop h (minus (S d0) (S i0)) x e2)).(let TMP_250 
\def (\lambda (e1: C).(let TMP_244 \def (S i0) in (let TMP_245 \def (Flat f) 
in (let TMP_246 \def (Flat f) in (let TMP_247 \def (r TMP_246 d0) in (let 
TMP_248 \def (lift h TMP_247 x1) in (let TMP_249 \def (CHead c2 TMP_245 
TMP_248) in (drop TMP_244 O TMP_249 e1)))))))) in (let TMP_254 \def (\lambda 
(e1: C).(let TMP_251 \def (S d0) in (let TMP_252 \def (S i0) in (let TMP_253 
\def (minus TMP_251 TMP_252) in (drop h TMP_253 e1 e2))))) in (let TMP_255 
\def (Flat f) in (let TMP_256 \def (Flat f) in (let TMP_257 \def (r TMP_256 
d0) in (let TMP_258 \def (lift h TMP_257 x1) in (let TMP_259 \def (drop_drop 
TMP_255 i0 c2 x H6 TMP_258) in (ex_intro2 C TMP_250 TMP_254 x TMP_259 
H7))))))))))) in (let TMP_261 \def (Flat f) in (let TMP_262 \def 
(drop_gen_drop TMP_261 x0 e2 x1 i0 H5) in (let TMP_263 \def (IHc x0 h H4 e2 
TMP_262) in (let TMP_264 \def (ex2_ind C TMP_227 TMP_231 TMP_243 TMP_260 
TMP_263) in (eq_ind_r T TMP_216 TMP_225 TMP_264 t H3)))))))))))))))))))))))) 
in (let TMP_266 \def (Flat f) in (let TMP_267 \def (drop_gen_skip_l c2 c3 t h 
d0 TMP_266 H0) in (ex3_2_ind C T TMP_193 TMP_197 TMP_200 TMP_209 TMP_265 
TMP_267))))))))))))))))) in (K_ind TMP_114 TMP_190 TMP_268 k))))))) in (C_ind 
TMP_49 TMP_106 TMP_269 c1)))))))) in (nat_ind TMP_22 TMP_42 TMP_270 d))))))) 
in (nat_ind TMP_4 TMP_16 TMP_271 i)))).

theorem drop_trans_ge:
 \forall (i: nat).(\forall (c1: C).(\forall (c2: C).(\forall (d: 
nat).(\forall (h: nat).((drop h d c1 c2) \to (\forall (e2: C).((drop i O c2 
e2) \to ((le d i) \to (drop (plus i h) O c1 e2)))))))))
\def
 \lambda (i: nat).(let TMP_2 \def (\lambda (n: nat).(\forall (c1: C).(\forall 
(c2: C).(\forall (d: nat).(\forall (h: nat).((drop h d c1 c2) \to (\forall 
(e2: C).((drop n O c2 e2) \to ((le d n) \to (let TMP_1 \def (plus n h) in 
(drop TMP_1 O c1 e2))))))))))) in (let TMP_7 \def (\lambda (c1: C).(\lambda 
(c2: C).(\lambda (d: nat).(\lambda (h: nat).(\lambda (H: (drop h d c1 
c2)).(\lambda (e2: C).(\lambda (H0: (drop O O c2 e2)).(\lambda (H1: (le d 
O)).(let TMP_4 \def (\lambda (c: C).(let TMP_3 \def (plus O h) in (drop TMP_3 
O c1 c))) in (let H_y \def (le_n_O_eq d H1) in (let TMP_5 \def (\lambda (n: 
nat).(drop h n c1 c2)) in (let H2 \def (eq_ind_r nat d TMP_5 H O H_y) in (let 
TMP_6 \def (drop_gen_refl c2 e2 H0) in (eq_ind C c2 TMP_4 H2 e2 
TMP_6)))))))))))))) in (let TMP_165 \def (\lambda (i0: nat).(\lambda (IHi: 
((\forall (c1: C).(\forall (c2: C).(\forall (d: nat).(\forall (h: nat).((drop 
h d c1 c2) \to (\forall (e2: C).((drop i0 O c2 e2) \to ((le d i0) \to (drop 
(plus i0 h) O c1 e2))))))))))).(\lambda (c1: C).(let TMP_10 \def (\lambda (c: 
C).(\forall (c2: C).(\forall (d: nat).(\forall (h: nat).((drop h d c c2) \to 
(\forall (e2: C).((drop (S i0) O c2 e2) \to ((le d (S i0)) \to (let TMP_8 
\def (S i0) in (let TMP_9 \def (plus TMP_8 h) in (drop TMP_9 O c 
e2))))))))))) in (let TMP_56 \def (\lambda (n: nat).(\lambda (c2: C).(\lambda 
(d: nat).(\lambda (h: nat).(\lambda (H: (drop h d (CSort n) c2)).(\lambda 
(e2: C).(\lambda (H0: (drop (S i0) O c2 e2)).(\lambda (H1: (le d (S 
i0))).(let TMP_11 \def (CSort n) in (let TMP_12 \def (eq C c2 TMP_11) in (let 
TMP_13 \def (eq nat h O) in (let TMP_14 \def (eq nat d O) in (let TMP_15 \def 
(plus i0 h) in (let TMP_16 \def (S TMP_15) in (let TMP_17 \def (CSort n) in 
(let TMP_18 \def (drop TMP_16 O TMP_17 e2) in (let TMP_54 \def (\lambda (H2: 
(eq C c2 (CSort n))).(\lambda (H3: (eq nat h O)).(\lambda (H4: (eq nat d 
O)).(let TMP_22 \def (\lambda (n0: nat).(let TMP_19 \def (plus i0 n0) in (let 
TMP_20 \def (S TMP_19) in (let TMP_21 \def (CSort n) in (drop TMP_20 O TMP_21 
e2))))) in (let TMP_24 \def (\lambda (n0: nat).(let TMP_23 \def (S i0) in (le 
n0 TMP_23))) in (let H5 \def (eq_ind nat d TMP_24 H1 O H4) in (let TMP_26 
\def (\lambda (c: C).(let TMP_25 \def (S i0) in (drop TMP_25 O c e2))) in 
(let TMP_27 \def (CSort n) in (let H6 \def (eq_ind C c2 TMP_26 H0 TMP_27 H2) 
in (let TMP_28 \def (CSort n) in (let TMP_29 \def (eq C e2 TMP_28) in (let 
TMP_30 \def (S i0) in (let TMP_31 \def (eq nat TMP_30 O) in (let TMP_32 \def 
(eq nat O O) in (let TMP_33 \def (plus i0 O) in (let TMP_34 \def (S TMP_33) 
in (let TMP_35 \def (CSort n) in (let TMP_36 \def (drop TMP_34 O TMP_35 e2) 
in (let TMP_50 \def (\lambda (H7: (eq C e2 (CSort n))).(\lambda (H8: (eq nat 
(S i0) O)).(\lambda (_: (eq nat O O)).(let TMP_37 \def (CSort n) in (let 
TMP_41 \def (\lambda (c: C).(let TMP_38 \def (plus i0 O) in (let TMP_39 \def 
(S TMP_38) in (let TMP_40 \def (CSort n) in (drop TMP_39 O TMP_40 c))))) in 
(let TMP_42 \def (S i0) in (let TMP_43 \def (\lambda (ee: nat).(match ee with 
[O \Rightarrow False | (S _) \Rightarrow True])) in (let H10 \def (eq_ind nat 
TMP_42 TMP_43 I O H8) in (let TMP_44 \def (plus i0 O) in (let TMP_45 \def (S 
TMP_44) in (let TMP_46 \def (CSort n) in (let TMP_47 \def (CSort n) in (let 
TMP_48 \def (drop TMP_45 O TMP_46 TMP_47) in (let TMP_49 \def (False_ind 
TMP_48 H10) in (eq_ind_r C TMP_37 TMP_41 TMP_49 e2 H7))))))))))))))) in (let 
TMP_51 \def (S i0) in (let TMP_52 \def (drop_gen_sort n TMP_51 O e2 H6) in 
(let TMP_53 \def (and3_ind TMP_29 TMP_31 TMP_32 TMP_36 TMP_50 TMP_52) in 
(eq_ind_r nat O TMP_22 TMP_53 h H3))))))))))))))))))))))) in (let TMP_55 \def 
(drop_gen_sort n h d c2 H) in (and3_ind TMP_12 TMP_13 TMP_14 TMP_18 TMP_54 
TMP_55))))))))))))))))))) in (let TMP_164 \def (\lambda (c2: C).(\lambda 
(IHc: ((\forall (c3: C).(\forall (d: nat).(\forall (h: nat).((drop h d c2 c3) 
\to (\forall (e2: C).((drop (S i0) O c3 e2) \to ((le d (S i0)) \to (drop (S 
(plus i0 h)) O c2 e2)))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c3: 
C).(\lambda (d: nat).(let TMP_60 \def (\lambda (n: nat).(\forall (h: 
nat).((drop h n (CHead c2 k t) c3) \to (\forall (e2: C).((drop (S i0) O c3 
e2) \to ((le n (S i0)) \to (let TMP_57 \def (plus i0 h) in (let TMP_58 \def 
(S TMP_57) in (let TMP_59 \def (CHead c2 k t) in (drop TMP_58 O TMP_59 
e2)))))))))) in (let TMP_111 \def (\lambda (h: nat).(let TMP_64 \def (\lambda 
(n: nat).((drop n O (CHead c2 k t) c3) \to (\forall (e2: C).((drop (S i0) O 
c3 e2) \to ((le O (S i0)) \to (let TMP_61 \def (plus i0 n) in (let TMP_62 
\def (S TMP_61) in (let TMP_63 \def (CHead c2 k t) in (drop TMP_62 O TMP_63 
e2))))))))) in (let TMP_77 \def (\lambda (H: (drop O O (CHead c2 k t) 
c3)).(\lambda (e2: C).(\lambda (H0: (drop (S i0) O c3 e2)).(\lambda (_: (le O 
(S i0))).(let TMP_66 \def (\lambda (c: C).(let TMP_65 \def (S i0) in (drop 
TMP_65 O c e2))) in (let TMP_67 \def (CHead c2 k t) in (let TMP_68 \def 
(CHead c2 k t) in (let TMP_69 \def (drop_gen_refl TMP_68 c3 H) in (let H2 
\def (eq_ind_r C c3 TMP_66 H0 TMP_67 TMP_69) in (let TMP_72 \def (\lambda (n: 
nat).(let TMP_70 \def (S n) in (let TMP_71 \def (CHead c2 k t) in (drop 
TMP_70 O TMP_71 e2)))) in (let TMP_73 \def (drop_gen_drop k c2 e2 t i0 H2) in 
(let TMP_74 \def (drop_drop k i0 c2 e2 TMP_73 t) in (let TMP_75 \def (plus i0 
O) in (let TMP_76 \def (plus_n_O i0) in (eq_ind nat i0 TMP_72 TMP_74 TMP_75 
TMP_76))))))))))))))) in (let TMP_110 \def (\lambda (n: nat).(\lambda (_: 
(((drop n O (CHead c2 k t) c3) \to (\forall (e2: C).((drop (S i0) O c3 e2) 
\to ((le O (S i0)) \to (drop (S (plus i0 n)) O (CHead c2 k t) 
e2))))))).(\lambda (H0: (drop (S n) O (CHead c2 k t) c3)).(\lambda (e2: 
C).(\lambda (H1: (drop (S i0) O c3 e2)).(\lambda (H2: (le O (S i0))).(let 
TMP_78 \def (plus i0 n) in (let TMP_79 \def (S TMP_78) in (let TMP_82 \def 
(\lambda (n0: nat).(let TMP_80 \def (S n0) in (let TMP_81 \def (CHead c2 k t) 
in (drop TMP_80 O TMP_81 e2)))) in (let TMP_83 \def (plus i0 n) in (let 
TMP_84 \def (S TMP_83) in (let TMP_85 \def (plus i0 n) in (let TMP_86 \def (r 
k TMP_85) in (let TMP_87 \def (S TMP_86) in (let TMP_88 \def (\lambda (n0: 
nat).(drop n0 O c2 e2)) in (let TMP_89 \def (r k n) in (let TMP_90 \def (plus 
i0 TMP_89) in (let TMP_92 \def (\lambda (n0: nat).(let TMP_91 \def (S n0) in 
(drop TMP_91 O c2 e2))) in (let TMP_93 \def (r k n) in (let TMP_94 \def 
(drop_gen_drop k c2 c3 t n H0) in (let TMP_95 \def (IHc c3 O TMP_93 TMP_94 e2 
H1 H2) in (let TMP_96 \def (plus i0 n) in (let TMP_97 \def (r k TMP_96) in 
(let TMP_98 \def (r_plus_sym k i0 n) in (let TMP_99 \def (eq_ind_r nat TMP_90 
TMP_92 TMP_95 TMP_97 TMP_98) in (let TMP_100 \def (plus i0 n) in (let TMP_101 
\def (S TMP_100) in (let TMP_102 \def (r k TMP_101) in (let TMP_103 \def 
(plus i0 n) in (let TMP_104 \def (r_S k TMP_103) in (let TMP_105 \def 
(eq_ind_r nat TMP_87 TMP_88 TMP_99 TMP_102 TMP_104) in (let TMP_106 \def 
(drop_drop k TMP_84 c2 e2 TMP_105 t) in (let TMP_107 \def (S n) in (let 
TMP_108 \def (plus i0 TMP_107) in (let TMP_109 \def (plus_n_Sm i0 n) in 
(eq_ind nat TMP_79 TMP_82 TMP_106 TMP_108 
TMP_109)))))))))))))))))))))))))))))))))))) in (nat_ind TMP_64 TMP_77 TMP_110 
h))))) in (let TMP_163 \def (\lambda (d0: nat).(\lambda (IHd: ((\forall (h: 
nat).((drop h d0 (CHead c2 k t) c3) \to (\forall (e2: C).((drop (S i0) O c3 
e2) \to ((le d0 (S i0)) \to (drop (S (plus i0 h)) O (CHead c2 k t) 
e2)))))))).(\lambda (h: nat).(\lambda (H: (drop h (S d0) (CHead c2 k t) 
c3)).(\lambda (e2: C).(\lambda (H0: (drop (S i0) O c3 e2)).(\lambda (H1: (le 
(S d0) (S i0))).(let TMP_113 \def (\lambda (e: C).(\lambda (v: T).(let 
TMP_112 \def (CHead e k v) in (eq C c3 TMP_112)))) in (let TMP_116 \def 
(\lambda (_: C).(\lambda (v: T).(let TMP_114 \def (r k d0) in (let TMP_115 
\def (lift h TMP_114 v) in (eq T t TMP_115))))) in (let TMP_118 \def (\lambda 
(e: C).(\lambda (_: T).(let TMP_117 \def (r k d0) in (drop h TMP_117 c2 e)))) 
in (let TMP_119 \def (plus i0 h) in (let TMP_120 \def (S TMP_119) in (let 
TMP_121 \def (CHead c2 k t) in (let TMP_122 \def (drop TMP_120 O TMP_121 e2) 
in (let TMP_161 \def (\lambda (x0: C).(\lambda (x1: T).(\lambda (H2: (eq C c3 
(CHead x0 k x1))).(\lambda (H3: (eq T t (lift h (r k d0) x1))).(\lambda (H4: 
(drop h (r k d0) c2 x0)).(let TMP_126 \def (\lambda (c: C).(\forall (h0: 
nat).((drop h0 d0 (CHead c2 k t) c) \to (\forall (e3: C).((drop (S i0) O c 
e3) \to ((le d0 (S i0)) \to (let TMP_123 \def (plus i0 h0) in (let TMP_124 
\def (S TMP_123) in (let TMP_125 \def (CHead c2 k t) in (drop TMP_124 O 
TMP_125 e3)))))))))) in (let TMP_127 \def (CHead x0 k x1) in (let H5 \def 
(eq_ind C c3 TMP_126 IHd TMP_127 H2) in (let TMP_129 \def (\lambda (c: 
C).(let TMP_128 \def (S i0) in (drop TMP_128 O c e2))) in (let TMP_130 \def 
(CHead x0 k x1) in (let H6 \def (eq_ind C c3 TMP_129 H0 TMP_130 H2) in (let 
TMP_134 \def (\lambda (t0: T).(\forall (h0: nat).((drop h0 d0 (CHead c2 k t0) 
(CHead x0 k x1)) \to (\forall (e3: C).((drop (S i0) O (CHead x0 k x1) e3) \to 
((le d0 (S i0)) \to (let TMP_131 \def (plus i0 h0) in (let TMP_132 \def (S 
TMP_131) in (let TMP_133 \def (CHead c2 k t0) in (drop TMP_132 O TMP_133 
e3)))))))))) in (let TMP_135 \def (r k d0) in (let TMP_136 \def (lift h 
TMP_135 x1) in (let H7 \def (eq_ind T t TMP_134 H5 TMP_136 H3) in (let 
TMP_137 \def (r k d0) in (let TMP_138 \def (lift h TMP_137 x1) in (let 
TMP_142 \def (\lambda (t0: T).(let TMP_139 \def (plus i0 h) in (let TMP_140 
\def (S TMP_139) in (let TMP_141 \def (CHead c2 k t0) in (drop TMP_140 O 
TMP_141 e2))))) in (let TMP_143 \def (plus i0 h) in (let TMP_146 \def 
(\lambda (k0: K).((drop h (r k0 d0) c2 x0) \to ((drop (r k0 i0) O x0 e2) \to 
(let TMP_144 \def (plus i0 h) in (let TMP_145 \def (r k0 TMP_144) in (drop 
TMP_145 O c2 e2)))))) in (let TMP_152 \def (\lambda (b: B).(\lambda (H8: 
(drop h (r (Bind b) d0) c2 x0)).(\lambda (H9: (drop (r (Bind b) i0) O x0 
e2)).(let TMP_147 \def (Bind b) in (let TMP_148 \def (r TMP_147 d0) in (let 
TMP_149 \def (Bind b) in (let TMP_150 \def (r TMP_149 d0) in (let TMP_151 
\def (le_S_n TMP_150 i0 H1) in (IHi c2 x0 TMP_148 h H8 e2 H9 TMP_151))))))))) 
in (let TMP_155 \def (\lambda (f: F).(\lambda (H8: (drop h (r (Flat f) d0) c2 
x0)).(\lambda (H9: (drop (r (Flat f) i0) O x0 e2)).(let TMP_153 \def (Flat f) 
in (let TMP_154 \def (r TMP_153 d0) in (IHc x0 TMP_154 h H8 e2 H9 H1)))))) in 
(let TMP_156 \def (drop_gen_drop k x0 e2 x1 i0 H6) in (let TMP_157 \def 
(K_ind TMP_146 TMP_152 TMP_155 k H4 TMP_156) in (let TMP_158 \def (r k d0) in 
(let TMP_159 \def (lift h TMP_158 x1) in (let TMP_160 \def (drop_drop k 
TMP_143 c2 e2 TMP_157 TMP_159) in (eq_ind_r T TMP_138 TMP_142 TMP_160 t 
H3)))))))))))))))))))))))))))) in (let TMP_162 \def (drop_gen_skip_l c2 c3 t 
h d0 k H) in (ex3_2_ind C T TMP_113 TMP_116 TMP_118 TMP_122 TMP_161 
TMP_162))))))))))))))))) in (nat_ind TMP_60 TMP_111 TMP_163 d)))))))))) in 
(C_ind TMP_10 TMP_56 TMP_164 c1))))))) in (nat_ind TMP_2 TMP_7 TMP_165 i)))).

