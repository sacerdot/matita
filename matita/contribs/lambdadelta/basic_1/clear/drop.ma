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

include "basic_1/clear/fwd.ma".

include "basic_1/drop/fwd.ma".

theorem drop_clear:
 \forall (c1: C).(\forall (c2: C).(\forall (i: nat).((drop (S i) O c1 c2) \to 
(ex2_3 B C T (\lambda (b: B).(\lambda (e: C).(\lambda (v: T).(clear c1 (CHead 
e (Bind b) v))))) (\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop i O e 
c2))))))))
\def
 \lambda (c1: C).(let TMP_5 \def (\lambda (c: C).(\forall (c2: C).(\forall 
(i: nat).((drop (S i) O c c2) \to (let TMP_3 \def (\lambda (b: B).(\lambda 
(e: C).(\lambda (v: T).(let TMP_1 \def (Bind b) in (let TMP_2 \def (CHead e 
TMP_1 v) in (clear c TMP_2)))))) in (let TMP_4 \def (\lambda (_: B).(\lambda 
(e: C).(\lambda (_: T).(drop i O e c2)))) in (ex2_3 B C T TMP_3 TMP_4))))))) 
in (let TMP_28 \def (\lambda (n: nat).(\lambda (c2: C).(\lambda (i: 
nat).(\lambda (H: (drop (S i) O (CSort n) c2)).(let TMP_6 \def (CSort n) in 
(let TMP_7 \def (eq C c2 TMP_6) in (let TMP_8 \def (S i) in (let TMP_9 \def 
(eq nat TMP_8 O) in (let TMP_10 \def (eq nat O O) in (let TMP_14 \def 
(\lambda (b: B).(\lambda (e: C).(\lambda (v: T).(let TMP_11 \def (CSort n) in 
(let TMP_12 \def (Bind b) in (let TMP_13 \def (CHead e TMP_12 v) in (clear 
TMP_11 TMP_13))))))) in (let TMP_15 \def (\lambda (_: B).(\lambda (e: 
C).(\lambda (_: T).(drop i O e c2)))) in (let TMP_16 \def (ex2_3 B C T TMP_14 
TMP_15) in (let TMP_25 \def (\lambda (_: (eq C c2 (CSort n))).(\lambda (H1: 
(eq nat (S i) O)).(\lambda (_: (eq nat O O)).(let TMP_17 \def (S i) in (let 
TMP_18 \def (\lambda (ee: nat).(match ee with [O \Rightarrow False | (S _) 
\Rightarrow True])) in (let H3 \def (eq_ind nat TMP_17 TMP_18 I O H1) in (let 
TMP_22 \def (\lambda (b: B).(\lambda (e: C).(\lambda (v: T).(let TMP_19 \def 
(CSort n) in (let TMP_20 \def (Bind b) in (let TMP_21 \def (CHead e TMP_20 v) 
in (clear TMP_19 TMP_21))))))) in (let TMP_23 \def (\lambda (_: B).(\lambda 
(e: C).(\lambda (_: T).(drop i O e c2)))) in (let TMP_24 \def (ex2_3 B C T 
TMP_22 TMP_23) in (False_ind TMP_24 H3)))))))))) in (let TMP_26 \def (S i) in 
(let TMP_27 \def (drop_gen_sort n TMP_26 O c2 H) in (and3_ind TMP_7 TMP_9 
TMP_10 TMP_16 TMP_25 TMP_27)))))))))))))))) in (let TMP_66 \def (\lambda (c: 
C).(\lambda (H: ((\forall (c2: C).(\forall (i: nat).((drop (S i) O c c2) \to 
(ex2_3 B C T (\lambda (b: B).(\lambda (e: C).(\lambda (v: T).(clear c (CHead 
e (Bind b) v))))) (\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop i O e 
c2)))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c2: C).(\lambda (i: 
nat).(\lambda (H0: (drop (S i) O (CHead c k t) c2)).(let TMP_34 \def (\lambda 
(k0: K).((drop (r k0 i) O c c2) \to (let TMP_32 \def (\lambda (b: B).(\lambda 
(e: C).(\lambda (v: T).(let TMP_29 \def (CHead c k0 t) in (let TMP_30 \def 
(Bind b) in (let TMP_31 \def (CHead e TMP_30 v) in (clear TMP_29 
TMP_31))))))) in (let TMP_33 \def (\lambda (_: B).(\lambda (e: C).(\lambda 
(_: T).(drop i O e c2)))) in (ex2_3 B C T TMP_32 TMP_33))))) in (let TMP_42 
\def (\lambda (b: B).(\lambda (H1: (drop (r (Bind b) i) O c c2)).(let TMP_39 
\def (\lambda (b0: B).(\lambda (e: C).(\lambda (v: T).(let TMP_35 \def (Bind 
b) in (let TMP_36 \def (CHead c TMP_35 t) in (let TMP_37 \def (Bind b0) in 
(let TMP_38 \def (CHead e TMP_37 v) in (clear TMP_36 TMP_38)))))))) in (let 
TMP_40 \def (\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop i O e 
c2)))) in (let TMP_41 \def (clear_bind b c t) in (ex2_3_intro B C T TMP_39 
TMP_40 b c t TMP_41 H1)))))) in (let TMP_64 \def (\lambda (f: F).(\lambda 
(H1: (drop (r (Flat f) i) O c c2)).(let H2 \def (H c2 i H1) in (let TMP_45 
\def (\lambda (b: B).(\lambda (e: C).(\lambda (v: T).(let TMP_43 \def (Bind 
b) in (let TMP_44 \def (CHead e TMP_43 v) in (clear c TMP_44)))))) in (let 
TMP_46 \def (\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop i O e 
c2)))) in (let TMP_51 \def (\lambda (b: B).(\lambda (e: C).(\lambda (v: 
T).(let TMP_47 \def (Flat f) in (let TMP_48 \def (CHead c TMP_47 t) in (let 
TMP_49 \def (Bind b) in (let TMP_50 \def (CHead e TMP_49 v) in (clear TMP_48 
TMP_50)))))))) in (let TMP_52 \def (\lambda (_: B).(\lambda (e: C).(\lambda 
(_: T).(drop i O e c2)))) in (let TMP_53 \def (ex2_3 B C T TMP_51 TMP_52) in 
(let TMP_63 \def (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: T).(\lambda 
(H3: (clear c (CHead x1 (Bind x0) x2))).(\lambda (H4: (drop i O x1 c2)).(let 
TMP_58 \def (\lambda (b: B).(\lambda (e: C).(\lambda (v: T).(let TMP_54 \def 
(Flat f) in (let TMP_55 \def (CHead c TMP_54 t) in (let TMP_56 \def (Bind b) 
in (let TMP_57 \def (CHead e TMP_56 v) in (clear TMP_55 TMP_57)))))))) in 
(let TMP_59 \def (\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop i O e 
c2)))) in (let TMP_60 \def (Bind x0) in (let TMP_61 \def (CHead x1 TMP_60 x2) 
in (let TMP_62 \def (clear_flat c TMP_61 H3 f t) in (ex2_3_intro B C T TMP_58 
TMP_59 x0 x1 x2 TMP_62 H4))))))))))) in (ex2_3_ind B C T TMP_45 TMP_46 TMP_53 
TMP_63 H2)))))))))) in (let TMP_65 \def (drop_gen_drop k c c2 t i H0) in 
(K_ind TMP_34 TMP_42 TMP_64 k TMP_65)))))))))))) in (C_ind TMP_5 TMP_28 
TMP_66 c1)))).

theorem drop_clear_O:
 \forall (b: B).(\forall (c: C).(\forall (e1: C).(\forall (u: T).((clear c 
(CHead e1 (Bind b) u)) \to (\forall (e2: C).(\forall (i: nat).((drop i O e1 
e2) \to (drop (S i) O c e2))))))))
\def
 \lambda (b: B).(\lambda (c: C).(let TMP_2 \def (\lambda (c0: C).(\forall 
(e1: C).(\forall (u: T).((clear c0 (CHead e1 (Bind b) u)) \to (\forall (e2: 
C).(\forall (i: nat).((drop i O e1 e2) \to (let TMP_1 \def (S i) in (drop 
TMP_1 O c0 e2))))))))) in (let TMP_8 \def (\lambda (n: nat).(\lambda (e1: 
C).(\lambda (u: T).(\lambda (H: (clear (CSort n) (CHead e1 (Bind b) 
u))).(\lambda (e2: C).(\lambda (i: nat).(\lambda (_: (drop i O e1 e2)).(let 
TMP_3 \def (Bind b) in (let TMP_4 \def (CHead e1 TMP_3 u) in (let TMP_5 \def 
(S i) in (let TMP_6 \def (CSort n) in (let TMP_7 \def (drop TMP_5 O TMP_6 e2) 
in (clear_gen_sort TMP_4 n H TMP_7))))))))))))) in (let TMP_52 \def (\lambda 
(c0: C).(\lambda (H: ((\forall (e1: C).(\forall (u: T).((clear c0 (CHead e1 
(Bind b) u)) \to (\forall (e2: C).(\forall (i: nat).((drop i O e1 e2) \to 
(drop (S i) O c0 e2))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (e1: 
C).(\lambda (u: T).(\lambda (H0: (clear (CHead c0 k t) (CHead e1 (Bind b) 
u))).(\lambda (e2: C).(\lambda (i: nat).(\lambda (H1: (drop i O e1 e2)).(let 
TMP_11 \def (\lambda (k0: K).((clear (CHead c0 k0 t) (CHead e1 (Bind b) u)) 
\to (let TMP_9 \def (S i) in (let TMP_10 \def (CHead c0 k0 t) in (drop TMP_9 
O TMP_10 e2))))) in (let TMP_45 \def (\lambda (b0: B).(\lambda (H2: (clear 
(CHead c0 (Bind b0) t) (CHead e1 (Bind b) u))).(let TMP_12 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow e1 | (CHead c1 _ _) \Rightarrow c1])) 
in (let TMP_13 \def (Bind b) in (let TMP_14 \def (CHead e1 TMP_13 u) in (let 
TMP_15 \def (Bind b0) in (let TMP_16 \def (CHead c0 TMP_15 t) in (let TMP_17 
\def (Bind b) in (let TMP_18 \def (CHead e1 TMP_17 u) in (let TMP_19 \def 
(clear_gen_bind b0 c0 TMP_18 t H2) in (let H3 \def (f_equal C C TMP_12 TMP_14 
TMP_16 TMP_19) in (let TMP_20 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow b | (CHead _ k0 _) \Rightarrow (match k0 with [(Bind b1) 
\Rightarrow b1 | (Flat _) \Rightarrow b])])) in (let TMP_21 \def (Bind b) in 
(let TMP_22 \def (CHead e1 TMP_21 u) in (let TMP_23 \def (Bind b0) in (let 
TMP_24 \def (CHead c0 TMP_23 t) in (let TMP_25 \def (Bind b) in (let TMP_26 
\def (CHead e1 TMP_25 u) in (let TMP_27 \def (clear_gen_bind b0 c0 TMP_26 t 
H2) in (let H4 \def (f_equal C B TMP_20 TMP_22 TMP_24 TMP_27) in (let TMP_28 
\def (\lambda (e: C).(match e with [(CSort _) \Rightarrow u | (CHead _ _ t0) 
\Rightarrow t0])) in (let TMP_29 \def (Bind b) in (let TMP_30 \def (CHead e1 
TMP_29 u) in (let TMP_31 \def (Bind b0) in (let TMP_32 \def (CHead c0 TMP_31 
t) in (let TMP_33 \def (Bind b) in (let TMP_34 \def (CHead e1 TMP_33 u) in 
(let TMP_35 \def (clear_gen_bind b0 c0 TMP_34 t H2) in (let H5 \def (f_equal 
C T TMP_28 TMP_30 TMP_32 TMP_35) in (let TMP_43 \def (\lambda (H6: (eq B b 
b0)).(\lambda (H7: (eq C e1 c0)).(let TMP_36 \def (\lambda (c1: C).(drop i O 
c1 e2)) in (let H8 \def (eq_ind C e1 TMP_36 H1 c0 H7) in (let TMP_40 \def 
(\lambda (b1: B).(let TMP_37 \def (S i) in (let TMP_38 \def (Bind b1) in (let 
TMP_39 \def (CHead c0 TMP_38 t) in (drop TMP_37 O TMP_39 e2))))) in (let 
TMP_41 \def (Bind b) in (let TMP_42 \def (drop_drop TMP_41 i c0 e2 H8 t) in 
(eq_ind B b TMP_40 TMP_42 b0 H6)))))))) in (let TMP_44 \def (TMP_43 H4) in 
(TMP_44 H3)))))))))))))))))))))))))))))))) in (let TMP_51 \def (\lambda (f: 
F).(\lambda (H2: (clear (CHead c0 (Flat f) t) (CHead e1 (Bind b) u))).(let 
TMP_46 \def (Flat f) in (let TMP_47 \def (Bind b) in (let TMP_48 \def (CHead 
e1 TMP_47 u) in (let TMP_49 \def (clear_gen_flat f c0 TMP_48 t H2) in (let 
TMP_50 \def (H e1 u TMP_49 e2 i H1) in (drop_drop TMP_46 i c0 e2 TMP_50 
t)))))))) in (K_ind TMP_11 TMP_45 TMP_51 k H0)))))))))))))) in (C_ind TMP_2 
TMP_8 TMP_52 c))))).

theorem drop_clear_S:
 \forall (x2: C).(\forall (x1: C).(\forall (h: nat).(\forall (d: nat).((drop 
h (S d) x1 x2) \to (\forall (b: B).(\forall (c2: C).(\forall (u: T).((clear 
x2 (CHead c2 (Bind b) u)) \to (ex2 C (\lambda (c1: C).(clear x1 (CHead c1 
(Bind b) (lift h d u)))) (\lambda (c1: C).(drop h d c1 c2)))))))))))
\def
 \lambda (x2: C).(let TMP_6 \def (\lambda (c: C).(\forall (x1: C).(\forall 
(h: nat).(\forall (d: nat).((drop h (S d) x1 c) \to (\forall (b: B).(\forall 
(c2: C).(\forall (u: T).((clear c (CHead c2 (Bind b) u)) \to (let TMP_4 \def 
(\lambda (c1: C).(let TMP_1 \def (Bind b) in (let TMP_2 \def (lift h d u) in 
(let TMP_3 \def (CHead c1 TMP_1 TMP_2) in (clear x1 TMP_3))))) in (let TMP_5 
\def (\lambda (c1: C).(drop h d c1 c2)) in (ex2 C TMP_4 TMP_5)))))))))))) in 
(let TMP_15 \def (\lambda (n: nat).(\lambda (x1: C).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (_: (drop h (S d) x1 (CSort n))).(\lambda (b: 
B).(\lambda (c2: C).(\lambda (u: T).(\lambda (H0: (clear (CSort n) (CHead c2 
(Bind b) u))).(let TMP_7 \def (Bind b) in (let TMP_8 \def (CHead c2 TMP_7 u) 
in (let TMP_12 \def (\lambda (c1: C).(let TMP_9 \def (Bind b) in (let TMP_10 
\def (lift h d u) in (let TMP_11 \def (CHead c1 TMP_9 TMP_10) in (clear x1 
TMP_11))))) in (let TMP_13 \def (\lambda (c1: C).(drop h d c1 c2)) in (let 
TMP_14 \def (ex2 C TMP_12 TMP_13) in (clear_gen_sort TMP_8 n H0 
TMP_14))))))))))))))) in (let TMP_162 \def (\lambda (c: C).(\lambda (H: 
((\forall (x1: C).(\forall (h: nat).(\forall (d: nat).((drop h (S d) x1 c) 
\to (\forall (b: B).(\forall (c2: C).(\forall (u: T).((clear c (CHead c2 
(Bind b) u)) \to (ex2 C (\lambda (c1: C).(clear x1 (CHead c1 (Bind b) (lift h 
d u)))) (\lambda (c1: C).(drop h d c1 c2))))))))))))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (x1: C).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H0: (drop h (S d) x1 (CHead c k t))).(\lambda (b: B).(\lambda 
(c2: C).(\lambda (u: T).(\lambda (H1: (clear (CHead c k t) (CHead c2 (Bind b) 
u))).(let TMP_19 \def (\lambda (e: C).(let TMP_16 \def (r k d) in (let TMP_17 
\def (lift h TMP_16 t) in (let TMP_18 \def (CHead e k TMP_17) in (eq C x1 
TMP_18))))) in (let TMP_21 \def (\lambda (e: C).(let TMP_20 \def (r k d) in 
(drop h TMP_20 e c))) in (let TMP_25 \def (\lambda (c1: C).(let TMP_22 \def 
(Bind b) in (let TMP_23 \def (lift h d u) in (let TMP_24 \def (CHead c1 
TMP_22 TMP_23) in (clear x1 TMP_24))))) in (let TMP_26 \def (\lambda (c1: 
C).(drop h d c1 c2)) in (let TMP_27 \def (ex2 C TMP_25 TMP_26) in (let 
TMP_160 \def (\lambda (x: C).(\lambda (H2: (eq C x1 (CHead x k (lift h (r k 
d) t)))).(\lambda (H3: (drop h (r k d) x c)).(let TMP_28 \def (r k d) in (let 
TMP_29 \def (lift h TMP_28 t) in (let TMP_30 \def (CHead x k TMP_29) in (let 
TMP_36 \def (\lambda (c0: C).(let TMP_34 \def (\lambda (c1: C).(let TMP_31 
\def (Bind b) in (let TMP_32 \def (lift h d u) in (let TMP_33 \def (CHead c1 
TMP_31 TMP_32) in (clear c0 TMP_33))))) in (let TMP_35 \def (\lambda (c1: 
C).(drop h d c1 c2)) in (ex2 C TMP_34 TMP_35)))) in (let TMP_45 \def (\lambda 
(k0: K).((clear (CHead c k0 t) (CHead c2 (Bind b) u)) \to ((drop h (r k0 d) x 
c) \to (let TMP_43 \def (\lambda (c1: C).(let TMP_37 \def (r k0 d) in (let 
TMP_38 \def (lift h TMP_37 t) in (let TMP_39 \def (CHead x k0 TMP_38) in (let 
TMP_40 \def (Bind b) in (let TMP_41 \def (lift h d u) in (let TMP_42 \def 
(CHead c1 TMP_40 TMP_41) in (clear TMP_39 TMP_42)))))))) in (let TMP_44 \def 
(\lambda (c1: C).(drop h d c1 c2)) in (ex2 C TMP_43 TMP_44)))))) in (let 
TMP_120 \def (\lambda (b0: B).(\lambda (H4: (clear (CHead c (Bind b0) t) 
(CHead c2 (Bind b) u))).(\lambda (H5: (drop h (r (Bind b0) d) x c)).(let 
TMP_46 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow c2 | (CHead 
c0 _ _) \Rightarrow c0])) in (let TMP_47 \def (Bind b) in (let TMP_48 \def 
(CHead c2 TMP_47 u) in (let TMP_49 \def (Bind b0) in (let TMP_50 \def (CHead 
c TMP_49 t) in (let TMP_51 \def (Bind b) in (let TMP_52 \def (CHead c2 TMP_51 
u) in (let TMP_53 \def (clear_gen_bind b0 c TMP_52 t H4) in (let H6 \def 
(f_equal C C TMP_46 TMP_48 TMP_50 TMP_53) in (let TMP_54 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow b | (CHead _ k0 _) \Rightarrow (match 
k0 with [(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow b])])) in (let 
TMP_55 \def (Bind b) in (let TMP_56 \def (CHead c2 TMP_55 u) in (let TMP_57 
\def (Bind b0) in (let TMP_58 \def (CHead c TMP_57 t) in (let TMP_59 \def 
(Bind b) in (let TMP_60 \def (CHead c2 TMP_59 u) in (let TMP_61 \def 
(clear_gen_bind b0 c TMP_60 t H4) in (let H7 \def (f_equal C B TMP_54 TMP_56 
TMP_58 TMP_61) in (let TMP_62 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) in (let TMP_63 \def (Bind b) 
in (let TMP_64 \def (CHead c2 TMP_63 u) in (let TMP_65 \def (Bind b0) in (let 
TMP_66 \def (CHead c TMP_65 t) in (let TMP_67 \def (Bind b) in (let TMP_68 
\def (CHead c2 TMP_67 u) in (let TMP_69 \def (clear_gen_bind b0 c TMP_68 t 
H4) in (let H8 \def (f_equal C T TMP_62 TMP_64 TMP_66 TMP_69) in (let TMP_118 
\def (\lambda (H9: (eq B b b0)).(\lambda (H10: (eq C c2 c)).(let TMP_80 \def 
(\lambda (t0: T).(let TMP_78 \def (\lambda (c1: C).(let TMP_70 \def (Bind b0) 
in (let TMP_71 \def (Bind b0) in (let TMP_72 \def (r TMP_71 d) in (let TMP_73 
\def (lift h TMP_72 t) in (let TMP_74 \def (CHead x TMP_70 TMP_73) in (let 
TMP_75 \def (Bind b) in (let TMP_76 \def (lift h d t0) in (let TMP_77 \def 
(CHead c1 TMP_75 TMP_76) in (clear TMP_74 TMP_77)))))))))) in (let TMP_79 
\def (\lambda (c1: C).(drop h d c1 c2)) in (ex2 C TMP_78 TMP_79)))) in (let 
TMP_91 \def (\lambda (c0: C).(let TMP_89 \def (\lambda (c1: C).(let TMP_81 
\def (Bind b0) in (let TMP_82 \def (Bind b0) in (let TMP_83 \def (r TMP_82 d) 
in (let TMP_84 \def (lift h TMP_83 t) in (let TMP_85 \def (CHead x TMP_81 
TMP_84) in (let TMP_86 \def (Bind b) in (let TMP_87 \def (lift h d t) in (let 
TMP_88 \def (CHead c1 TMP_86 TMP_87) in (clear TMP_85 TMP_88)))))))))) in 
(let TMP_90 \def (\lambda (c1: C).(drop h d c1 c0)) in (ex2 C TMP_89 
TMP_90)))) in (let TMP_102 \def (\lambda (b1: B).(let TMP_100 \def (\lambda 
(c1: C).(let TMP_92 \def (Bind b0) in (let TMP_93 \def (Bind b0) in (let 
TMP_94 \def (r TMP_93 d) in (let TMP_95 \def (lift h TMP_94 t) in (let TMP_96 
\def (CHead x TMP_92 TMP_95) in (let TMP_97 \def (Bind b1) in (let TMP_98 
\def (lift h d t) in (let TMP_99 \def (CHead c1 TMP_97 TMP_98) in (clear 
TMP_96 TMP_99)))))))))) in (let TMP_101 \def (\lambda (c1: C).(drop h d c1 
c)) in (ex2 C TMP_100 TMP_101)))) in (let TMP_111 \def (\lambda (c1: C).(let 
TMP_103 \def (Bind b0) in (let TMP_104 \def (Bind b0) in (let TMP_105 \def (r 
TMP_104 d) in (let TMP_106 \def (lift h TMP_105 t) in (let TMP_107 \def 
(CHead x TMP_103 TMP_106) in (let TMP_108 \def (Bind b0) in (let TMP_109 \def 
(lift h d t) in (let TMP_110 \def (CHead c1 TMP_108 TMP_109) in (clear 
TMP_107 TMP_110)))))))))) in (let TMP_112 \def (\lambda (c1: C).(drop h d c1 
c)) in (let TMP_113 \def (lift h d t) in (let TMP_114 \def (clear_bind b0 x 
TMP_113) in (let TMP_115 \def (ex_intro2 C TMP_111 TMP_112 x TMP_114 H5) in 
(let TMP_116 \def (eq_ind_r B b0 TMP_102 TMP_115 b H9) in (let TMP_117 \def 
(eq_ind_r C c TMP_91 TMP_116 c2 H10) in (eq_ind_r T t TMP_80 TMP_117 u 
H8))))))))))))) in (let TMP_119 \def (TMP_118 H7) in (TMP_119 
H6))))))))))))))))))))))))))))))))) in (let TMP_158 \def (\lambda (f: 
F).(\lambda (H4: (clear (CHead c (Flat f) t) (CHead c2 (Bind b) u))).(\lambda 
(H5: (drop h (r (Flat f) d) x c)).(let TMP_121 \def (Bind b) in (let TMP_122 
\def (CHead c2 TMP_121 u) in (let TMP_123 \def (clear_gen_flat f c TMP_122 t 
H4) in (let H6 \def (H x h d H5 b c2 u TMP_123) in (let TMP_127 \def (\lambda 
(c1: C).(let TMP_124 \def (Bind b) in (let TMP_125 \def (lift h d u) in (let 
TMP_126 \def (CHead c1 TMP_124 TMP_125) in (clear x TMP_126))))) in (let 
TMP_128 \def (\lambda (c1: C).(drop h d c1 c2)) in (let TMP_137 \def (\lambda 
(c1: C).(let TMP_129 \def (Flat f) in (let TMP_130 \def (Flat f) in (let 
TMP_131 \def (r TMP_130 d) in (let TMP_132 \def (lift h TMP_131 t) in (let 
TMP_133 \def (CHead x TMP_129 TMP_132) in (let TMP_134 \def (Bind b) in (let 
TMP_135 \def (lift h d u) in (let TMP_136 \def (CHead c1 TMP_134 TMP_135) in 
(clear TMP_133 TMP_136)))))))))) in (let TMP_138 \def (\lambda (c1: C).(drop 
h d c1 c2)) in (let TMP_139 \def (ex2 C TMP_137 TMP_138) in (let TMP_157 \def 
(\lambda (x0: C).(\lambda (H7: (clear x (CHead x0 (Bind b) (lift h d 
u)))).(\lambda (H8: (drop h d x0 c2)).(let TMP_148 \def (\lambda (c1: C).(let 
TMP_140 \def (Flat f) in (let TMP_141 \def (Flat f) in (let TMP_142 \def (r 
TMP_141 d) in (let TMP_143 \def (lift h TMP_142 t) in (let TMP_144 \def 
(CHead x TMP_140 TMP_143) in (let TMP_145 \def (Bind b) in (let TMP_146 \def 
(lift h d u) in (let TMP_147 \def (CHead c1 TMP_145 TMP_146) in (clear 
TMP_144 TMP_147)))))))))) in (let TMP_149 \def (\lambda (c1: C).(drop h d c1 
c2)) in (let TMP_150 \def (Bind b) in (let TMP_151 \def (lift h d u) in (let 
TMP_152 \def (CHead x0 TMP_150 TMP_151) in (let TMP_153 \def (Flat f) in (let 
TMP_154 \def (r TMP_153 d) in (let TMP_155 \def (lift h TMP_154 t) in (let 
TMP_156 \def (clear_flat x TMP_152 H7 f TMP_155) in (ex_intro2 C TMP_148 
TMP_149 x0 TMP_156 H8))))))))))))) in (ex2_ind C TMP_127 TMP_128 TMP_139 
TMP_157 H6)))))))))))))) in (let TMP_159 \def (K_ind TMP_45 TMP_120 TMP_158 k 
H1 H3) in (eq_ind_r C TMP_30 TMP_36 TMP_159 x1 H2)))))))))))) in (let TMP_161 
\def (drop_gen_skip_r c x1 t h d k H0) in (ex2_ind C TMP_19 TMP_21 TMP_27 
TMP_160 TMP_161)))))))))))))))))))) in (C_ind TMP_6 TMP_15 TMP_162 x2)))).

