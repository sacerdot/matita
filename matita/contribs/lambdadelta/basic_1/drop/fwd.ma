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

include "basic_1/drop/defs.ma".

include "basic_1/lift/fwd.ma".

include "basic_1/r/props.ma".

include "basic_1/C/fwd.ma".

let rec drop_ind (P: (nat \to (nat \to (C \to (C \to Prop))))) (f: (\forall 
(c: C).(P O O c c))) (f0: (\forall (k: K).(\forall (h: nat).(\forall (c: 
C).(\forall (e: C).((drop (r k h) O c e) \to ((P (r k h) O c e) \to (\forall 
(u: T).(P (S h) O (CHead c k u) e))))))))) (f1: (\forall (k: K).(\forall (h: 
nat).(\forall (d: nat).(\forall (c: C).(\forall (e: C).((drop h (r k d) c e) 
\to ((P h (r k d) c e) \to (\forall (u: T).(P h (S d) (CHead c k (lift h (r k 
d) u)) (CHead e k u))))))))))) (n: nat) (n0: nat) (c: C) (c0: C) (d: drop n 
n0 c c0) on d: P n n0 c c0 \def match d with [(drop_refl c1) \Rightarrow (f 
c1) | (drop_drop k h c1 e d0 u) \Rightarrow (let TMP_3 \def (r k h) in (let 
TMP_4 \def ((drop_ind P f f0 f1) TMP_3 O c1 e d0) in (f0 k h c1 e d0 TMP_4 
u))) | (drop_skip k h d0 c1 e d1 u) \Rightarrow (let TMP_1 \def (r k d0) in 
(let TMP_2 \def ((drop_ind P f f0 f1) h TMP_1 c1 e d1) in (f1 k h d0 c1 e d1 
TMP_2 u)))].

theorem drop_gen_sort:
 \forall (n: nat).(\forall (h: nat).(\forall (d: nat).(\forall (x: C).((drop 
h d (CSort n) x) \to (and3 (eq C x (CSort n)) (eq nat h O) (eq nat d O))))))
\def
 \lambda (n: nat).(\lambda (h: nat).(\lambda (d: nat).(\lambda (x: 
C).(\lambda (H: (drop h d (CSort n) x)).(let TMP_1 \def (CSort n) in (let 
TMP_2 \def (\lambda (c: C).(drop h d c x)) in (let TMP_6 \def (\lambda (c: 
C).(let TMP_3 \def (eq C x c) in (let TMP_4 \def (eq nat h O) in (let TMP_5 
\def (eq nat d O) in (and3 TMP_3 TMP_4 TMP_5))))) in (let TMP_54 \def 
(\lambda (y: C).(\lambda (H0: (drop h d y x)).(let TMP_10 \def (\lambda (n0: 
nat).(\lambda (n1: nat).(\lambda (c: C).(\lambda (c0: C).((eq C c (CSort n)) 
\to (let TMP_7 \def (eq C c0 c) in (let TMP_8 \def (eq nat n0 O) in (let 
TMP_9 \def (eq nat n1 O) in (and3 TMP_7 TMP_8 TMP_9))))))))) in (let TMP_28 
\def (\lambda (c: C).(\lambda (H1: (eq C c (CSort n))).(let TMP_11 \def 
(\lambda (e: C).e) in (let TMP_12 \def (CSort n) in (let H2 \def (f_equal C C 
TMP_11 c TMP_12 H1) in (let TMP_13 \def (CSort n) in (let TMP_17 \def 
(\lambda (c0: C).(let TMP_14 \def (eq C c0 c0) in (let TMP_15 \def (eq nat O 
O) in (let TMP_16 \def (eq nat O O) in (and3 TMP_14 TMP_15 TMP_16))))) in 
(let TMP_18 \def (CSort n) in (let TMP_19 \def (CSort n) in (let TMP_20 \def 
(eq C TMP_18 TMP_19) in (let TMP_21 \def (eq nat O O) in (let TMP_22 \def (eq 
nat O O) in (let TMP_23 \def (CSort n) in (let TMP_24 \def (refl_equal C 
TMP_23) in (let TMP_25 \def (refl_equal nat O) in (let TMP_26 \def 
(refl_equal nat O) in (let TMP_27 \def (and3_intro TMP_20 TMP_21 TMP_22 
TMP_24 TMP_25 TMP_26) in (eq_ind_r C TMP_13 TMP_17 TMP_27 c 
H2)))))))))))))))))) in (let TMP_38 \def (\lambda (k: K).(\lambda (h0: 
nat).(\lambda (c: C).(\lambda (e: C).(\lambda (_: (drop (r k h0) O c 
e)).(\lambda (_: (((eq C c (CSort n)) \to (and3 (eq C e c) (eq nat (r k h0) 
O) (eq nat O O))))).(\lambda (u: T).(\lambda (H3: (eq C (CHead c k u) (CSort 
n))).(let TMP_29 \def (CHead c k u) in (let TMP_30 \def (\lambda (ee: 
C).(match ee with [(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow 
True])) in (let TMP_31 \def (CSort n) in (let H4 \def (eq_ind C TMP_29 TMP_30 
I TMP_31 H3) in (let TMP_32 \def (CHead c k u) in (let TMP_33 \def (eq C e 
TMP_32) in (let TMP_34 \def (S h0) in (let TMP_35 \def (eq nat TMP_34 O) in 
(let TMP_36 \def (eq nat O O) in (let TMP_37 \def (and3 TMP_33 TMP_35 TMP_36) 
in (False_ind TMP_37 H4))))))))))))))))))) in (let TMP_53 \def (\lambda (k: 
K).(\lambda (h0: nat).(\lambda (d0: nat).(\lambda (c: C).(\lambda (e: 
C).(\lambda (_: (drop h0 (r k d0) c e)).(\lambda (_: (((eq C c (CSort n)) \to 
(and3 (eq C e c) (eq nat h0 O) (eq nat (r k d0) O))))).(\lambda (u: 
T).(\lambda (H3: (eq C (CHead c k (lift h0 (r k d0) u)) (CSort n))).(let 
TMP_39 \def (r k d0) in (let TMP_40 \def (lift h0 TMP_39 u) in (let TMP_41 
\def (CHead c k TMP_40) in (let TMP_42 \def (\lambda (ee: C).(match ee with 
[(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow True])) in (let 
TMP_43 \def (CSort n) in (let H4 \def (eq_ind C TMP_41 TMP_42 I TMP_43 H3) in 
(let TMP_44 \def (CHead e k u) in (let TMP_45 \def (r k d0) in (let TMP_46 
\def (lift h0 TMP_45 u) in (let TMP_47 \def (CHead c k TMP_46) in (let TMP_48 
\def (eq C TMP_44 TMP_47) in (let TMP_49 \def (eq nat h0 O) in (let TMP_50 
\def (S d0) in (let TMP_51 \def (eq nat TMP_50 O) in (let TMP_52 \def (and3 
TMP_48 TMP_49 TMP_51) in (False_ind TMP_52 H4))))))))))))))))))))))))) in 
(drop_ind TMP_10 TMP_28 TMP_38 TMP_53 h d y x H0))))))) in (insert_eq C TMP_1 
TMP_2 TMP_6 TMP_54 H))))))))).

theorem drop_gen_refl:
 \forall (x: C).(\forall (e: C).((drop O O x e) \to (eq C x e)))
\def
 \lambda (x: C).(\lambda (e: C).(\lambda (H: (drop O O x e)).(let TMP_1 \def 
(\lambda (n: nat).(drop n O x e)) in (let TMP_2 \def (\lambda (_: nat).(eq C 
x e)) in (let TMP_36 \def (\lambda (y: nat).(\lambda (H0: (drop y O x 
e)).(let TMP_3 \def (\lambda (n: nat).(drop y n x e)) in (let TMP_4 \def 
(\lambda (n: nat).((eq nat y n) \to (eq C x e))) in (let TMP_35 \def (\lambda 
(y0: nat).(\lambda (H1: (drop y y0 x e)).(let TMP_5 \def (\lambda (n: 
nat).(\lambda (n0: nat).(\lambda (c: C).(\lambda (c0: C).((eq nat n0 O) \to 
((eq nat n n0) \to (eq C c c0))))))) in (let TMP_6 \def (\lambda (c: 
C).(\lambda (_: (eq nat O O)).(\lambda (_: (eq nat O O)).(refl_equal C c)))) 
in (let TMP_11 \def (\lambda (k: K).(\lambda (h: nat).(\lambda (c: 
C).(\lambda (e0: C).(\lambda (_: (drop (r k h) O c e0)).(\lambda (_: (((eq 
nat O O) \to ((eq nat (r k h) O) \to (eq C c e0))))).(\lambda (u: T).(\lambda 
(_: (eq nat O O)).(\lambda (H5: (eq nat (S h) O)).(let TMP_7 \def (S h) in 
(let TMP_8 \def (\lambda (ee: nat).(match ee with [O \Rightarrow False | (S 
_) \Rightarrow True])) in (let H6 \def (eq_ind nat TMP_7 TMP_8 I O H5) in 
(let TMP_9 \def (CHead c k u) in (let TMP_10 \def (eq C TMP_9 e0) in 
(False_ind TMP_10 H6))))))))))))))) in (let TMP_34 \def (\lambda (k: 
K).(\lambda (h: nat).(\lambda (d: nat).(\lambda (c: C).(\lambda (e0: 
C).(\lambda (H2: (drop h (r k d) c e0)).(\lambda (H3: (((eq nat (r k d) O) 
\to ((eq nat h (r k d)) \to (eq C c e0))))).(\lambda (u: T).(\lambda (H4: (eq 
nat (S d) O)).(\lambda (H5: (eq nat h (S d))).(let TMP_12 \def (\lambda (e1: 
nat).e1) in (let TMP_13 \def (S d) in (let H6 \def (f_equal nat nat TMP_12 h 
TMP_13 H5) in (let TMP_14 \def (\lambda (n: nat).((eq nat (r k d) O) \to ((eq 
nat n (r k d)) \to (eq C c e0)))) in (let TMP_15 \def (S d) in (let H7 \def 
(eq_ind nat h TMP_14 H3 TMP_15 H6) in (let TMP_17 \def (\lambda (n: nat).(let 
TMP_16 \def (r k d) in (drop n TMP_16 c e0))) in (let TMP_18 \def (S d) in 
(let H8 \def (eq_ind nat h TMP_17 H2 TMP_18 H6) in (let TMP_19 \def (S d) in 
(let TMP_24 \def (\lambda (n: nat).(let TMP_20 \def (r k d) in (let TMP_21 
\def (lift n TMP_20 u) in (let TMP_22 \def (CHead c k TMP_21) in (let TMP_23 
\def (CHead e0 k u) in (eq C TMP_22 TMP_23)))))) in (let TMP_25 \def (S d) in 
(let TMP_26 \def (\lambda (ee: nat).(match ee with [O \Rightarrow False | (S 
_) \Rightarrow True])) in (let H9 \def (eq_ind nat TMP_25 TMP_26 I O H4) in 
(let TMP_27 \def (S d) in (let TMP_28 \def (r k d) in (let TMP_29 \def (lift 
TMP_27 TMP_28 u) in (let TMP_30 \def (CHead c k TMP_29) in (let TMP_31 \def 
(CHead e0 k u) in (let TMP_32 \def (eq C TMP_30 TMP_31) in (let TMP_33 \def 
(False_ind TMP_32 H9) in (eq_ind_r nat TMP_19 TMP_24 TMP_33 h 
H6)))))))))))))))))))))))))))))))) in (drop_ind TMP_5 TMP_6 TMP_11 TMP_34 y 
y0 x e H1))))))) in (insert_eq nat O TMP_3 TMP_4 TMP_35 H0)))))) in 
(insert_eq nat O TMP_1 TMP_2 TMP_36 H)))))).

theorem drop_gen_drop:
 \forall (k: K).(\forall (c: C).(\forall (x: C).(\forall (u: T).(\forall (h: 
nat).((drop (S h) O (CHead c k u) x) \to (drop (r k h) O c x))))))
\def
 \lambda (k: K).(\lambda (c: C).(\lambda (x: C).(\lambda (u: T).(\lambda (h: 
nat).(\lambda (H: (drop (S h) O (CHead c k u) x)).(let TMP_1 \def (CHead c k 
u) in (let TMP_3 \def (\lambda (c0: C).(let TMP_2 \def (S h) in (drop TMP_2 O 
c0 x))) in (let TMP_5 \def (\lambda (_: C).(let TMP_4 \def (r k h) in (drop 
TMP_4 O c x))) in (let TMP_130 \def (\lambda (y: C).(\lambda (H0: (drop (S h) 
O y x)).(let TMP_7 \def (\lambda (n: nat).(let TMP_6 \def (S h) in (drop 
TMP_6 n y x))) in (let TMP_9 \def (\lambda (n: nat).((eq C y (CHead c k u)) 
\to (let TMP_8 \def (r k h) in (drop TMP_8 n c x)))) in (let TMP_129 \def 
(\lambda (y0: nat).(\lambda (H1: (drop (S h) y0 y x)).(let TMP_10 \def (S h) 
in (let TMP_11 \def (\lambda (n: nat).(drop n y0 y x)) in (let TMP_13 \def 
(\lambda (_: nat).((eq nat y0 O) \to ((eq C y (CHead c k u)) \to (let TMP_12 
\def (r k h) in (drop TMP_12 y0 c x))))) in (let TMP_128 \def (\lambda (y1: 
nat).(\lambda (H2: (drop y1 y0 y x)).(let TMP_15 \def (\lambda (n: 
nat).(\lambda (n0: nat).(\lambda (c0: C).(\lambda (c1: C).((eq nat n (S h)) 
\to ((eq nat n0 O) \to ((eq C c0 (CHead c k u)) \to (let TMP_14 \def (r k h) 
in (drop TMP_14 n0 c c1))))))))) in (let TMP_25 \def (\lambda (c0: 
C).(\lambda (H3: (eq nat O (S h))).(\lambda (_: (eq nat O O)).(\lambda (H5: 
(eq C c0 (CHead c k u))).(let TMP_16 \def (CHead c k u) in (let TMP_18 \def 
(\lambda (c1: C).(let TMP_17 \def (r k h) in (drop TMP_17 O c c1))) in (let 
TMP_19 \def (\lambda (ee: nat).(match ee with [O \Rightarrow True | (S _) 
\Rightarrow False])) in (let TMP_20 \def (S h) in (let H6 \def (eq_ind nat O 
TMP_19 I TMP_20 H3) in (let TMP_21 \def (r k h) in (let TMP_22 \def (CHead c 
k u) in (let TMP_23 \def (drop TMP_21 O c TMP_22) in (let TMP_24 \def 
(False_ind TMP_23 H6) in (eq_ind_r C TMP_16 TMP_18 TMP_24 c0 H5)))))))))))))) 
in (let TMP_52 \def (\lambda (k0: K).(\lambda (h0: nat).(\lambda (c0: 
C).(\lambda (e: C).(\lambda (H3: (drop (r k0 h0) O c0 e)).(\lambda (H4: (((eq 
nat (r k0 h0) (S h)) \to ((eq nat O O) \to ((eq C c0 (CHead c k u)) \to (drop 
(r k h) O c e)))))).(\lambda (u0: T).(\lambda (H5: (eq nat (S h0) (S 
h))).(\lambda (_: (eq nat O O)).(\lambda (H7: (eq C (CHead c0 k0 u0) (CHead c 
k u))).(let TMP_26 \def (\lambda (e0: C).(match e0 with [(CSort _) 
\Rightarrow c0 | (CHead c1 _ _) \Rightarrow c1])) in (let TMP_27 \def (CHead 
c0 k0 u0) in (let TMP_28 \def (CHead c k u) in (let H8 \def (f_equal C C 
TMP_26 TMP_27 TMP_28 H7) in (let TMP_29 \def (\lambda (e0: C).(match e0 with 
[(CSort _) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow k1])) in (let TMP_30 
\def (CHead c0 k0 u0) in (let TMP_31 \def (CHead c k u) in (let H9 \def 
(f_equal C K TMP_29 TMP_30 TMP_31 H7) in (let TMP_32 \def (\lambda (e0: 
C).(match e0 with [(CSort _) \Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) 
in (let TMP_33 \def (CHead c0 k0 u0) in (let TMP_34 \def (CHead c k u) in 
(let H10 \def (f_equal C T TMP_32 TMP_33 TMP_34 H7) in (let TMP_50 \def 
(\lambda (H11: (eq K k0 k)).(\lambda (H12: (eq C c0 c)).(let TMP_36 \def 
(\lambda (c1: C).((eq nat (r k0 h0) (S h)) \to ((eq nat O O) \to ((eq C c1 
(CHead c k u)) \to (let TMP_35 \def (r k h) in (drop TMP_35 O c e)))))) in 
(let H13 \def (eq_ind C c0 TMP_36 H4 c H12) in (let TMP_38 \def (\lambda (c1: 
C).(let TMP_37 \def (r k0 h0) in (drop TMP_37 O c1 e))) in (let H14 \def 
(eq_ind C c0 TMP_38 H3 c H12) in (let TMP_40 \def (\lambda (k1: K).((eq nat 
(r k1 h0) (S h)) \to ((eq nat O O) \to ((eq C c (CHead c k u)) \to (let 
TMP_39 \def (r k h) in (drop TMP_39 O c e)))))) in (let H15 \def (eq_ind K k0 
TMP_40 H13 k H11) in (let TMP_42 \def (\lambda (k1: K).(let TMP_41 \def (r k1 
h0) in (drop TMP_41 O c e))) in (let H16 \def (eq_ind K k0 TMP_42 H14 k H11) 
in (let TMP_43 \def (\lambda (e0: nat).(match e0 with [O \Rightarrow h0 | (S 
n) \Rightarrow n])) in (let TMP_44 \def (S h0) in (let TMP_45 \def (S h) in 
(let H17 \def (f_equal nat nat TMP_43 TMP_44 TMP_45 H5) in (let TMP_47 \def 
(\lambda (n: nat).((eq nat (r k n) (S h)) \to ((eq nat O O) \to ((eq C c 
(CHead c k u)) \to (let TMP_46 \def (r k h) in (drop TMP_46 O c e)))))) in 
(let H18 \def (eq_ind nat h0 TMP_47 H15 h H17) in (let TMP_49 \def (\lambda 
(n: nat).(let TMP_48 \def (r k n) in (drop TMP_48 O c e))) in (let H19 \def 
(eq_ind nat h0 TMP_49 H16 h H17) in H19)))))))))))))))))) in (let TMP_51 \def 
(TMP_50 H9) in (TMP_51 H8))))))))))))))))))))))))) in (let TMP_127 \def 
(\lambda (k0: K).(\lambda (h0: nat).(\lambda (d: nat).(\lambda (c0: 
C).(\lambda (e: C).(\lambda (H3: (drop h0 (r k0 d) c0 e)).(\lambda (H4: (((eq 
nat h0 (S h)) \to ((eq nat (r k0 d) O) \to ((eq C c0 (CHead c k u)) \to (drop 
(r k h) (r k0 d) c e)))))).(\lambda (u0: T).(\lambda (H5: (eq nat h0 (S 
h))).(\lambda (H6: (eq nat (S d) O)).(\lambda (H7: (eq C (CHead c0 k0 (lift 
h0 (r k0 d) u0)) (CHead c k u))).(let TMP_57 \def (\lambda (n: nat).(let 
TMP_53 \def (r k0 d) in (let TMP_54 \def (lift n TMP_53 u0) in (let TMP_55 
\def (CHead c0 k0 TMP_54) in (let TMP_56 \def (CHead c k u) in (eq C TMP_55 
TMP_56)))))) in (let TMP_58 \def (S h) in (let H8 \def (eq_ind nat h0 TMP_57 
H7 TMP_58 H5) in (let TMP_61 \def (\lambda (n: nat).((eq nat n (S h)) \to 
((eq nat (r k0 d) O) \to ((eq C c0 (CHead c k u)) \to (let TMP_59 \def (r k 
h) in (let TMP_60 \def (r k0 d) in (drop TMP_59 TMP_60 c e))))))) in (let 
TMP_62 \def (S h) in (let H9 \def (eq_ind nat h0 TMP_61 H4 TMP_62 H5) in (let 
TMP_64 \def (\lambda (n: nat).(let TMP_63 \def (r k0 d) in (drop n TMP_63 c0 
e))) in (let TMP_65 \def (S h) in (let H10 \def (eq_ind nat h0 TMP_64 H3 
TMP_65 H5) in (let TMP_66 \def (\lambda (e0: C).(match e0 with [(CSort _) 
\Rightarrow c0 | (CHead c1 _ _) \Rightarrow c1])) in (let TMP_67 \def (S h) 
in (let TMP_68 \def (r k0 d) in (let TMP_69 \def (lift TMP_67 TMP_68 u0) in 
(let TMP_70 \def (CHead c0 k0 TMP_69) in (let TMP_71 \def (CHead c k u) in 
(let H11 \def (f_equal C C TMP_66 TMP_70 TMP_71 H8) in (let TMP_72 \def 
(\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow k0 | (CHead _ k1 _) 
\Rightarrow k1])) in (let TMP_73 \def (S h) in (let TMP_74 \def (r k0 d) in 
(let TMP_75 \def (lift TMP_73 TMP_74 u0) in (let TMP_76 \def (CHead c0 k0 
TMP_75) in (let TMP_77 \def (CHead c k u) in (let H12 \def (f_equal C K 
TMP_72 TMP_76 TMP_77 H8) in (let TMP_86 \def (\lambda (e0: C).(match e0 with 
[(CSort _) \Rightarrow (let TMP_84 \def (\lambda (x0: nat).(let TMP_83 \def 
(S h) in (plus x0 TMP_83))) in (let TMP_85 \def (r k0 d) in (lref_map TMP_84 
TMP_85 u0))) | (CHead _ _ t) \Rightarrow t])) in (let TMP_87 \def (S h) in 
(let TMP_88 \def (r k0 d) in (let TMP_89 \def (lift TMP_87 TMP_88 u0) in (let 
TMP_90 \def (CHead c0 k0 TMP_89) in (let TMP_91 \def (CHead c k u) in (let 
H13 \def (f_equal C T TMP_86 TMP_90 TMP_91 H8) in (let TMP_125 \def (\lambda 
(H14: (eq K k0 k)).(\lambda (H15: (eq C c0 c)).(let TMP_94 \def (\lambda (c1: 
C).((eq nat (S h) (S h)) \to ((eq nat (r k0 d) O) \to ((eq C c1 (CHead c k 
u)) \to (let TMP_92 \def (r k h) in (let TMP_93 \def (r k0 d) in (drop TMP_92 
TMP_93 c e))))))) in (let H16 \def (eq_ind C c0 TMP_94 H9 c H15) in (let 
TMP_97 \def (\lambda (c1: C).(let TMP_95 \def (S h) in (let TMP_96 \def (r k0 
d) in (drop TMP_95 TMP_96 c1 e)))) in (let H17 \def (eq_ind C c0 TMP_97 H10 c 
H15) in (let TMP_101 \def (\lambda (k1: K).(let TMP_98 \def (S h) in (let 
TMP_99 \def (r k1 d) in (let TMP_100 \def (lift TMP_98 TMP_99 u0) in (eq T 
TMP_100 u))))) in (let H18 \def (eq_ind K k0 TMP_101 H13 k H14) in (let 
TMP_104 \def (\lambda (k1: K).((eq nat (S h) (S h)) \to ((eq nat (r k1 d) O) 
\to ((eq C c (CHead c k u)) \to (let TMP_102 \def (r k h) in (let TMP_103 
\def (r k1 d) in (drop TMP_102 TMP_103 c e))))))) in (let H19 \def (eq_ind K 
k0 TMP_104 H16 k H14) in (let TMP_107 \def (\lambda (k1: K).(let TMP_105 \def 
(S h) in (let TMP_106 \def (r k1 d) in (drop TMP_105 TMP_106 c e)))) in (let 
H20 \def (eq_ind K k0 TMP_107 H17 k H14) in (let TMP_111 \def (\lambda (k1: 
K).(let TMP_108 \def (r k h) in (let TMP_109 \def (S d) in (let TMP_110 \def 
(CHead e k1 u0) in (drop TMP_108 TMP_109 c TMP_110))))) in (let TMP_114 \def 
(\lambda (t: T).((eq nat (S h) (S h)) \to ((eq nat (r k d) O) \to ((eq C c 
(CHead c k t)) \to (let TMP_112 \def (r k h) in (let TMP_113 \def (r k d) in 
(drop TMP_112 TMP_113 c e))))))) in (let TMP_115 \def (S h) in (let TMP_116 
\def (r k d) in (let TMP_117 \def (lift TMP_115 TMP_116 u0) in (let H21 \def 
(eq_ind_r T u TMP_114 H19 TMP_117 H18) in (let TMP_118 \def (S d) in (let 
TMP_119 \def (\lambda (ee: nat).(match ee with [O \Rightarrow False | (S _) 
\Rightarrow True])) in (let H22 \def (eq_ind nat TMP_118 TMP_119 I O H6) in 
(let TMP_120 \def (r k h) in (let TMP_121 \def (S d) in (let TMP_122 \def 
(CHead e k u0) in (let TMP_123 \def (drop TMP_120 TMP_121 c TMP_122) in (let 
TMP_124 \def (False_ind TMP_123 H22) in (eq_ind_r K k TMP_111 TMP_124 k0 
H14))))))))))))))))))))))))))) in (let TMP_126 \def (TMP_125 H12) in (TMP_126 
H11)))))))))))))))))))))))))))))))))))))))))))) in (drop_ind TMP_15 TMP_25 
TMP_52 TMP_127 y1 y0 y x H2))))))) in (insert_eq nat TMP_10 TMP_11 TMP_13 
TMP_128 H1))))))) in (insert_eq nat O TMP_7 TMP_9 TMP_129 H0)))))) in 
(insert_eq C TMP_1 TMP_3 TMP_5 TMP_130 H)))))))))).

theorem drop_gen_skip_r:
 \forall (c: C).(\forall (x: C).(\forall (u: T).(\forall (h: nat).(\forall 
(d: nat).(\forall (k: K).((drop h (S d) x (CHead c k u)) \to (ex2 C (\lambda 
(e: C).(eq C x (CHead e k (lift h (r k d) u)))) (\lambda (e: C).(drop h (r k 
d) e c)))))))))
\def
 \lambda (c: C).(\lambda (x: C).(\lambda (u: T).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (k: K).(\lambda (H: (drop h (S d) x (CHead c k u))).(let 
TMP_1 \def (CHead c k u) in (let TMP_3 \def (\lambda (c0: C).(let TMP_2 \def 
(S d) in (drop h TMP_2 x c0))) in (let TMP_10 \def (\lambda (_: C).(let TMP_7 
\def (\lambda (e: C).(let TMP_4 \def (r k d) in (let TMP_5 \def (lift h TMP_4 
u) in (let TMP_6 \def (CHead e k TMP_5) in (eq C x TMP_6))))) in (let TMP_9 
\def (\lambda (e: C).(let TMP_8 \def (r k d) in (drop h TMP_8 e c))) in (ex2 
C TMP_7 TMP_9)))) in (let TMP_162 \def (\lambda (y: C).(\lambda (H0: (drop h 
(S d) x y)).(let TMP_11 \def (S d) in (let TMP_12 \def (\lambda (n: 
nat).(drop h n x y)) in (let TMP_19 \def (\lambda (_: nat).((eq C y (CHead c 
k u)) \to (let TMP_16 \def (\lambda (e: C).(let TMP_13 \def (r k d) in (let 
TMP_14 \def (lift h TMP_13 u) in (let TMP_15 \def (CHead e k TMP_14) in (eq C 
x TMP_15))))) in (let TMP_18 \def (\lambda (e: C).(let TMP_17 \def (r k d) in 
(drop h TMP_17 e c))) in (ex2 C TMP_16 TMP_18))))) in (let TMP_161 \def 
(\lambda (y0: nat).(\lambda (H1: (drop h y0 x y)).(let TMP_26 \def (\lambda 
(n: nat).(\lambda (n0: nat).(\lambda (c0: C).(\lambda (c1: C).((eq nat n0 (S 
d)) \to ((eq C c1 (CHead c k u)) \to (let TMP_23 \def (\lambda (e: C).(let 
TMP_20 \def (r k d) in (let TMP_21 \def (lift n TMP_20 u) in (let TMP_22 \def 
(CHead e k TMP_21) in (eq C c0 TMP_22))))) in (let TMP_25 \def (\lambda (e: 
C).(let TMP_24 \def (r k d) in (drop n TMP_24 e c))) in (ex2 C TMP_23 
TMP_25))))))))) in (let TMP_46 \def (\lambda (c0: C).(\lambda (H2: (eq nat O 
(S d))).(\lambda (H3: (eq C c0 (CHead c k u))).(let TMP_27 \def (CHead c k u) 
in (let TMP_34 \def (\lambda (c1: C).(let TMP_31 \def (\lambda (e: C).(let 
TMP_28 \def (r k d) in (let TMP_29 \def (lift O TMP_28 u) in (let TMP_30 \def 
(CHead e k TMP_29) in (eq C c1 TMP_30))))) in (let TMP_33 \def (\lambda (e: 
C).(let TMP_32 \def (r k d) in (drop O TMP_32 e c))) in (ex2 C TMP_31 
TMP_33)))) in (let TMP_35 \def (\lambda (ee: nat).(match ee with [O 
\Rightarrow True | (S _) \Rightarrow False])) in (let TMP_36 \def (S d) in 
(let H4 \def (eq_ind nat O TMP_35 I TMP_36 H2) in (let TMP_41 \def (\lambda 
(e: C).(let TMP_37 \def (CHead c k u) in (let TMP_38 \def (r k d) in (let 
TMP_39 \def (lift O TMP_38 u) in (let TMP_40 \def (CHead e k TMP_39) in (eq C 
TMP_37 TMP_40)))))) in (let TMP_43 \def (\lambda (e: C).(let TMP_42 \def (r k 
d) in (drop O TMP_42 e c))) in (let TMP_44 \def (ex2 C TMP_41 TMP_43) in (let 
TMP_45 \def (False_ind TMP_44 H4) in (eq_ind_r C TMP_27 TMP_34 TMP_45 c0 
H3))))))))))))) in (let TMP_72 \def (\lambda (k0: K).(\lambda (h0: 
nat).(\lambda (c0: C).(\lambda (e: C).(\lambda (H2: (drop (r k0 h0) O c0 
e)).(\lambda (H3: (((eq nat O (S d)) \to ((eq C e (CHead c k u)) \to (ex2 C 
(\lambda (e0: C).(eq C c0 (CHead e0 k (lift (r k0 h0) (r k d) u)))) (\lambda 
(e0: C).(drop (r k0 h0) (r k d) e0 c))))))).(\lambda (u0: T).(\lambda (H4: 
(eq nat O (S d))).(\lambda (H5: (eq C e (CHead c k u))).(let TMP_55 \def 
(\lambda (c1: C).((eq nat O (S d)) \to ((eq C c1 (CHead c k u)) \to (let 
TMP_51 \def (\lambda (e0: C).(let TMP_47 \def (r k0 h0) in (let TMP_48 \def 
(r k d) in (let TMP_49 \def (lift TMP_47 TMP_48 u) in (let TMP_50 \def (CHead 
e0 k TMP_49) in (eq C c0 TMP_50)))))) in (let TMP_54 \def (\lambda (e0: 
C).(let TMP_52 \def (r k0 h0) in (let TMP_53 \def (r k d) in (drop TMP_52 
TMP_53 e0 c)))) in (ex2 C TMP_51 TMP_54)))))) in (let TMP_56 \def (CHead c k 
u) in (let H6 \def (eq_ind C e TMP_55 H3 TMP_56 H5) in (let TMP_58 \def 
(\lambda (c1: C).(let TMP_57 \def (r k0 h0) in (drop TMP_57 O c0 c1))) in 
(let TMP_59 \def (CHead c k u) in (let H7 \def (eq_ind C e TMP_58 H2 TMP_59 
H5) in (let TMP_60 \def (\lambda (ee: nat).(match ee with [O \Rightarrow True 
| (S _) \Rightarrow False])) in (let TMP_61 \def (S d) in (let H8 \def 
(eq_ind nat O TMP_60 I TMP_61 H4) in (let TMP_67 \def (\lambda (e0: C).(let 
TMP_62 \def (CHead c0 k0 u0) in (let TMP_63 \def (S h0) in (let TMP_64 \def 
(r k d) in (let TMP_65 \def (lift TMP_63 TMP_64 u) in (let TMP_66 \def (CHead 
e0 k TMP_65) in (eq C TMP_62 TMP_66))))))) in (let TMP_70 \def (\lambda (e0: 
C).(let TMP_68 \def (S h0) in (let TMP_69 \def (r k d) in (drop TMP_68 TMP_69 
e0 c)))) in (let TMP_71 \def (ex2 C TMP_67 TMP_70) in (False_ind TMP_71 
H8)))))))))))))))))))))) in (let TMP_160 \def (\lambda (k0: K).(\lambda (h0: 
nat).(\lambda (d0: nat).(\lambda (c0: C).(\lambda (e: C).(\lambda (H2: (drop 
h0 (r k0 d0) c0 e)).(\lambda (H3: (((eq nat (r k0 d0) (S d)) \to ((eq C e 
(CHead c k u)) \to (ex2 C (\lambda (e0: C).(eq C c0 (CHead e0 k (lift h0 (r k 
d) u)))) (\lambda (e0: C).(drop h0 (r k d) e0 c))))))).(\lambda (u0: 
T).(\lambda (H4: (eq nat (S d0) (S d))).(\lambda (H5: (eq C (CHead e k0 u0) 
(CHead c k u))).(let TMP_73 \def (\lambda (e0: C).(match e0 with [(CSort _) 
\Rightarrow e | (CHead c1 _ _) \Rightarrow c1])) in (let TMP_74 \def (CHead e 
k0 u0) in (let TMP_75 \def (CHead c k u) in (let H6 \def (f_equal C C TMP_73 
TMP_74 TMP_75 H5) in (let TMP_76 \def (\lambda (e0: C).(match e0 with [(CSort 
_) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow k1])) in (let TMP_77 \def 
(CHead e k0 u0) in (let TMP_78 \def (CHead c k u) in (let H7 \def (f_equal C 
K TMP_76 TMP_77 TMP_78 H5) in (let TMP_79 \def (\lambda (e0: C).(match e0 
with [(CSort _) \Rightarrow u0 | (CHead _ _ t) \Rightarrow t])) in (let 
TMP_80 \def (CHead e k0 u0) in (let TMP_81 \def (CHead c k u) in (let H8 \def 
(f_equal C T TMP_79 TMP_80 TMP_81 H5) in (let TMP_158 \def (\lambda (H9: (eq 
K k0 k)).(\lambda (H10: (eq C e c)).(let TMP_91 \def (\lambda (t: T).(let 
TMP_88 \def (\lambda (e0: C).(let TMP_82 \def (r k0 d0) in (let TMP_83 \def 
(lift h0 TMP_82 t) in (let TMP_84 \def (CHead c0 k0 TMP_83) in (let TMP_85 
\def (r k d) in (let TMP_86 \def (lift h0 TMP_85 u) in (let TMP_87 \def 
(CHead e0 k TMP_86) in (eq C TMP_84 TMP_87)))))))) in (let TMP_90 \def 
(\lambda (e0: C).(let TMP_89 \def (r k d) in (drop h0 TMP_89 e0 c))) in (ex2 
C TMP_88 TMP_90)))) in (let TMP_98 \def (\lambda (c1: C).((eq nat (r k0 d0) 
(S d)) \to ((eq C c1 (CHead c k u)) \to (let TMP_95 \def (\lambda (e0: 
C).(let TMP_92 \def (r k d) in (let TMP_93 \def (lift h0 TMP_92 u) in (let 
TMP_94 \def (CHead e0 k TMP_93) in (eq C c0 TMP_94))))) in (let TMP_97 \def 
(\lambda (e0: C).(let TMP_96 \def (r k d) in (drop h0 TMP_96 e0 c))) in (ex2 
C TMP_95 TMP_97)))))) in (let H11 \def (eq_ind C e TMP_98 H3 c H10) in (let 
TMP_100 \def (\lambda (c1: C).(let TMP_99 \def (r k0 d0) in (drop h0 TMP_99 
c0 c1))) in (let H12 \def (eq_ind C e TMP_100 H2 c H10) in (let TMP_107 \def 
(\lambda (k1: K).((eq nat (r k1 d0) (S d)) \to ((eq C c (CHead c k u)) \to 
(let TMP_104 \def (\lambda (e0: C).(let TMP_101 \def (r k d) in (let TMP_102 
\def (lift h0 TMP_101 u) in (let TMP_103 \def (CHead e0 k TMP_102) in (eq C 
c0 TMP_103))))) in (let TMP_106 \def (\lambda (e0: C).(let TMP_105 \def (r k 
d) in (drop h0 TMP_105 e0 c))) in (ex2 C TMP_104 TMP_106)))))) in (let H13 
\def (eq_ind K k0 TMP_107 H11 k H9) in (let TMP_109 \def (\lambda (k1: 
K).(let TMP_108 \def (r k1 d0) in (drop h0 TMP_108 c0 c))) in (let H14 \def 
(eq_ind K k0 TMP_109 H12 k H9) in (let TMP_119 \def (\lambda (k1: K).(let 
TMP_116 \def (\lambda (e0: C).(let TMP_110 \def (r k1 d0) in (let TMP_111 
\def (lift h0 TMP_110 u) in (let TMP_112 \def (CHead c0 k1 TMP_111) in (let 
TMP_113 \def (r k d) in (let TMP_114 \def (lift h0 TMP_113 u) in (let TMP_115 
\def (CHead e0 k TMP_114) in (eq C TMP_112 TMP_115)))))))) in (let TMP_118 
\def (\lambda (e0: C).(let TMP_117 \def (r k d) in (drop h0 TMP_117 e0 c))) 
in (ex2 C TMP_116 TMP_118)))) in (let TMP_120 \def (\lambda (e0: nat).(match 
e0 with [O \Rightarrow d0 | (S n) \Rightarrow n])) in (let TMP_121 \def (S 
d0) in (let TMP_122 \def (S d) in (let H15 \def (f_equal nat nat TMP_120 
TMP_121 TMP_122 H4) in (let TMP_129 \def (\lambda (n: nat).((eq nat (r k n) 
(S d)) \to ((eq C c (CHead c k u)) \to (let TMP_126 \def (\lambda (e0: 
C).(let TMP_123 \def (r k d) in (let TMP_124 \def (lift h0 TMP_123 u) in (let 
TMP_125 \def (CHead e0 k TMP_124) in (eq C c0 TMP_125))))) in (let TMP_128 
\def (\lambda (e0: C).(let TMP_127 \def (r k d) in (drop h0 TMP_127 e0 c))) 
in (ex2 C TMP_126 TMP_128)))))) in (let H16 \def (eq_ind nat d0 TMP_129 H13 d 
H15) in (let TMP_131 \def (\lambda (n: nat).(let TMP_130 \def (r k n) in 
(drop h0 TMP_130 c0 c))) in (let H17 \def (eq_ind nat d0 TMP_131 H14 d H15) 
in (let TMP_141 \def (\lambda (n: nat).(let TMP_138 \def (\lambda (e0: 
C).(let TMP_132 \def (r k n) in (let TMP_133 \def (lift h0 TMP_132 u) in (let 
TMP_134 \def (CHead c0 k TMP_133) in (let TMP_135 \def (r k d) in (let 
TMP_136 \def (lift h0 TMP_135 u) in (let TMP_137 \def (CHead e0 k TMP_136) in 
(eq C TMP_134 TMP_137)))))))) in (let TMP_140 \def (\lambda (e0: C).(let 
TMP_139 \def (r k d) in (drop h0 TMP_139 e0 c))) in (ex2 C TMP_138 
TMP_140)))) in (let TMP_148 \def (\lambda (e0: C).(let TMP_142 \def (r k d) 
in (let TMP_143 \def (lift h0 TMP_142 u) in (let TMP_144 \def (CHead c0 k 
TMP_143) in (let TMP_145 \def (r k d) in (let TMP_146 \def (lift h0 TMP_145 
u) in (let TMP_147 \def (CHead e0 k TMP_146) in (eq C TMP_144 TMP_147)))))))) 
in (let TMP_150 \def (\lambda (e0: C).(let TMP_149 \def (r k d) in (drop h0 
TMP_149 e0 c))) in (let TMP_151 \def (r k d) in (let TMP_152 \def (lift h0 
TMP_151 u) in (let TMP_153 \def (CHead c0 k TMP_152) in (let TMP_154 \def 
(refl_equal C TMP_153) in (let TMP_155 \def (ex_intro2 C TMP_148 TMP_150 c0 
TMP_154 H17) in (let TMP_156 \def (eq_ind_r nat d TMP_141 TMP_155 d0 H15) in 
(let TMP_157 \def (eq_ind_r K k TMP_119 TMP_156 k0 H9) in (eq_ind_r T u 
TMP_91 TMP_157 u0 H8))))))))))))))))))))))))))))))) in (let TMP_159 \def 
(TMP_158 H7) in (TMP_159 H6))))))))))))))))))))))))) in (drop_ind TMP_26 
TMP_46 TMP_72 TMP_160 h y0 x y H1))))))) in (insert_eq nat TMP_11 TMP_12 
TMP_19 TMP_161 H0))))))) in (insert_eq C TMP_1 TMP_3 TMP_10 TMP_162 
H))))))))))).

theorem drop_gen_skip_l:
 \forall (c: C).(\forall (x: C).(\forall (u: T).(\forall (h: nat).(\forall 
(d: nat).(\forall (k: K).((drop h (S d) (CHead c k u) x) \to (ex3_2 C T 
(\lambda (e: C).(\lambda (v: T).(eq C x (CHead e k v)))) (\lambda (_: 
C).(\lambda (v: T).(eq T u (lift h (r k d) v)))) (\lambda (e: C).(\lambda (_: 
T).(drop h (r k d) c e))))))))))
\def
 \lambda (c: C).(\lambda (x: C).(\lambda (u: T).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (k: K).(\lambda (H: (drop h (S d) (CHead c k u) x)).(let 
TMP_1 \def (CHead c k u) in (let TMP_3 \def (\lambda (c0: C).(let TMP_2 \def 
(S d) in (drop h TMP_2 c0 x))) in (let TMP_11 \def (\lambda (_: C).(let TMP_5 
\def (\lambda (e: C).(\lambda (v: T).(let TMP_4 \def (CHead e k v) in (eq C x 
TMP_4)))) in (let TMP_8 \def (\lambda (_: C).(\lambda (v: T).(let TMP_6 \def 
(r k d) in (let TMP_7 \def (lift h TMP_6 v) in (eq T u TMP_7))))) in (let 
TMP_10 \def (\lambda (e: C).(\lambda (_: T).(let TMP_9 \def (r k d) in (drop 
h TMP_9 c e)))) in (ex3_2 C T TMP_5 TMP_8 TMP_10))))) in (let TMP_223 \def 
(\lambda (y: C).(\lambda (H0: (drop h (S d) y x)).(let TMP_12 \def (S d) in 
(let TMP_13 \def (\lambda (n: nat).(drop h n y x)) in (let TMP_21 \def 
(\lambda (_: nat).((eq C y (CHead c k u)) \to (let TMP_15 \def (\lambda (e: 
C).(\lambda (v: T).(let TMP_14 \def (CHead e k v) in (eq C x TMP_14)))) in 
(let TMP_18 \def (\lambda (_: C).(\lambda (v: T).(let TMP_16 \def (r k d) in 
(let TMP_17 \def (lift h TMP_16 v) in (eq T u TMP_17))))) in (let TMP_20 \def 
(\lambda (e: C).(\lambda (_: T).(let TMP_19 \def (r k d) in (drop h TMP_19 c 
e)))) in (ex3_2 C T TMP_15 TMP_18 TMP_20)))))) in (let TMP_222 \def (\lambda 
(y0: nat).(\lambda (H1: (drop h y0 y x)).(let TMP_29 \def (\lambda (n: 
nat).(\lambda (n0: nat).(\lambda (c0: C).(\lambda (c1: C).((eq nat n0 (S d)) 
\to ((eq C c0 (CHead c k u)) \to (let TMP_23 \def (\lambda (e: C).(\lambda 
(v: T).(let TMP_22 \def (CHead e k v) in (eq C c1 TMP_22)))) in (let TMP_26 
\def (\lambda (_: C).(\lambda (v: T).(let TMP_24 \def (r k d) in (let TMP_25 
\def (lift n TMP_24 v) in (eq T u TMP_25))))) in (let TMP_28 \def (\lambda 
(e: C).(\lambda (_: T).(let TMP_27 \def (r k d) in (drop n TMP_27 c e)))) in 
(ex3_2 C T TMP_23 TMP_26 TMP_28)))))))))) in (let TMP_51 \def (\lambda (c0: 
C).(\lambda (H2: (eq nat O (S d))).(\lambda (H3: (eq C c0 (CHead c k 
u))).(let TMP_30 \def (CHead c k u) in (let TMP_38 \def (\lambda (c1: C).(let 
TMP_32 \def (\lambda (e: C).(\lambda (v: T).(let TMP_31 \def (CHead e k v) in 
(eq C c1 TMP_31)))) in (let TMP_35 \def (\lambda (_: C).(\lambda (v: T).(let 
TMP_33 \def (r k d) in (let TMP_34 \def (lift O TMP_33 v) in (eq T u 
TMP_34))))) in (let TMP_37 \def (\lambda (e: C).(\lambda (_: T).(let TMP_36 
\def (r k d) in (drop O TMP_36 c e)))) in (ex3_2 C T TMP_32 TMP_35 
TMP_37))))) in (let TMP_39 \def (\lambda (ee: nat).(match ee with [O 
\Rightarrow True | (S _) \Rightarrow False])) in (let TMP_40 \def (S d) in 
(let H4 \def (eq_ind nat O TMP_39 I TMP_40 H2) in (let TMP_43 \def (\lambda 
(e: C).(\lambda (v: T).(let TMP_41 \def (CHead c k u) in (let TMP_42 \def 
(CHead e k v) in (eq C TMP_41 TMP_42))))) in (let TMP_46 \def (\lambda (_: 
C).(\lambda (v: T).(let TMP_44 \def (r k d) in (let TMP_45 \def (lift O 
TMP_44 v) in (eq T u TMP_45))))) in (let TMP_48 \def (\lambda (e: C).(\lambda 
(_: T).(let TMP_47 \def (r k d) in (drop O TMP_47 c e)))) in (let TMP_49 \def 
(ex3_2 C T TMP_43 TMP_46 TMP_48) in (let TMP_50 \def (False_ind TMP_49 H4) in 
(eq_ind_r C TMP_30 TMP_38 TMP_50 c0 H3)))))))))))))) in (let TMP_99 \def 
(\lambda (k0: K).(\lambda (h0: nat).(\lambda (c0: C).(\lambda (e: C).(\lambda 
(H2: (drop (r k0 h0) O c0 e)).(\lambda (H3: (((eq nat O (S d)) \to ((eq C c0 
(CHead c k u)) \to (ex3_2 C T (\lambda (e0: C).(\lambda (v: T).(eq C e (CHead 
e0 k v)))) (\lambda (_: C).(\lambda (v: T).(eq T u (lift (r k0 h0) (r k d) 
v)))) (\lambda (e0: C).(\lambda (_: T).(drop (r k0 h0) (r k d) c 
e0)))))))).(\lambda (u0: T).(\lambda (H4: (eq nat O (S d))).(\lambda (H5: (eq 
C (CHead c0 k0 u0) (CHead c k u))).(let TMP_52 \def (\lambda (e0: C).(match 
e0 with [(CSort _) \Rightarrow c0 | (CHead c1 _ _) \Rightarrow c1])) in (let 
TMP_53 \def (CHead c0 k0 u0) in (let TMP_54 \def (CHead c k u) in (let H6 
\def (f_equal C C TMP_52 TMP_53 TMP_54 H5) in (let TMP_55 \def (\lambda (e0: 
C).(match e0 with [(CSort _) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow 
k1])) in (let TMP_56 \def (CHead c0 k0 u0) in (let TMP_57 \def (CHead c k u) 
in (let H7 \def (f_equal C K TMP_55 TMP_56 TMP_57 H5) in (let TMP_58 \def 
(\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow u0 | (CHead _ _ t) 
\Rightarrow t])) in (let TMP_59 \def (CHead c0 k0 u0) in (let TMP_60 \def 
(CHead c k u) in (let H8 \def (f_equal C T TMP_58 TMP_59 TMP_60 H5) in (let 
TMP_97 \def (\lambda (H9: (eq K k0 k)).(\lambda (H10: (eq C c0 c)).(let 
TMP_70 \def (\lambda (c1: C).((eq nat O (S d)) \to ((eq C c1 (CHead c k u)) 
\to (let TMP_62 \def (\lambda (e0: C).(\lambda (v: T).(let TMP_61 \def (CHead 
e0 k v) in (eq C e TMP_61)))) in (let TMP_66 \def (\lambda (_: C).(\lambda 
(v: T).(let TMP_63 \def (r k0 h0) in (let TMP_64 \def (r k d) in (let TMP_65 
\def (lift TMP_63 TMP_64 v) in (eq T u TMP_65)))))) in (let TMP_69 \def 
(\lambda (e0: C).(\lambda (_: T).(let TMP_67 \def (r k0 h0) in (let TMP_68 
\def (r k d) in (drop TMP_67 TMP_68 c e0))))) in (ex3_2 C T TMP_62 TMP_66 
TMP_69))))))) in (let H11 \def (eq_ind C c0 TMP_70 H3 c H10) in (let TMP_72 
\def (\lambda (c1: C).(let TMP_71 \def (r k0 h0) in (drop TMP_71 O c1 e))) in 
(let H12 \def (eq_ind C c0 TMP_72 H2 c H10) in (let TMP_82 \def (\lambda (k1: 
K).((eq nat O (S d)) \to ((eq C c (CHead c k u)) \to (let TMP_74 \def 
(\lambda (e0: C).(\lambda (v: T).(let TMP_73 \def (CHead e0 k v) in (eq C e 
TMP_73)))) in (let TMP_78 \def (\lambda (_: C).(\lambda (v: T).(let TMP_75 
\def (r k1 h0) in (let TMP_76 \def (r k d) in (let TMP_77 \def (lift TMP_75 
TMP_76 v) in (eq T u TMP_77)))))) in (let TMP_81 \def (\lambda (e0: 
C).(\lambda (_: T).(let TMP_79 \def (r k1 h0) in (let TMP_80 \def (r k d) in 
(drop TMP_79 TMP_80 c e0))))) in (ex3_2 C T TMP_74 TMP_78 TMP_81))))))) in 
(let H13 \def (eq_ind K k0 TMP_82 H11 k H9) in (let TMP_84 \def (\lambda (k1: 
K).(let TMP_83 \def (r k1 h0) in (drop TMP_83 O c e))) in (let H14 \def 
(eq_ind K k0 TMP_84 H12 k H9) in (let TMP_85 \def (\lambda (ee: nat).(match 
ee with [O \Rightarrow True | (S _) \Rightarrow False])) in (let TMP_86 \def 
(S d) in (let H15 \def (eq_ind nat O TMP_85 I TMP_86 H4) in (let TMP_88 \def 
(\lambda (e0: C).(\lambda (v: T).(let TMP_87 \def (CHead e0 k v) in (eq C e 
TMP_87)))) in (let TMP_92 \def (\lambda (_: C).(\lambda (v: T).(let TMP_89 
\def (S h0) in (let TMP_90 \def (r k d) in (let TMP_91 \def (lift TMP_89 
TMP_90 v) in (eq T u TMP_91)))))) in (let TMP_95 \def (\lambda (e0: 
C).(\lambda (_: T).(let TMP_93 \def (S h0) in (let TMP_94 \def (r k d) in 
(drop TMP_93 TMP_94 c e0))))) in (let TMP_96 \def (ex3_2 C T TMP_88 TMP_92 
TMP_95) in (False_ind TMP_96 H15)))))))))))))))))) in (let TMP_98 \def 
(TMP_97 H7) in (TMP_98 H6)))))))))))))))))))))))) in (let TMP_221 \def 
(\lambda (k0: K).(\lambda (h0: nat).(\lambda (d0: nat).(\lambda (c0: 
C).(\lambda (e: C).(\lambda (H2: (drop h0 (r k0 d0) c0 e)).(\lambda (H3: 
(((eq nat (r k0 d0) (S d)) \to ((eq C c0 (CHead c k u)) \to (ex3_2 C T 
(\lambda (e0: C).(\lambda (v: T).(eq C e (CHead e0 k v)))) (\lambda (_: 
C).(\lambda (v: T).(eq T u (lift h0 (r k d) v)))) (\lambda (e0: C).(\lambda 
(_: T).(drop h0 (r k d) c e0)))))))).(\lambda (u0: T).(\lambda (H4: (eq nat 
(S d0) (S d))).(\lambda (H5: (eq C (CHead c0 k0 (lift h0 (r k0 d0) u0)) 
(CHead c k u))).(let TMP_100 \def (\lambda (e0: C).(match e0 with [(CSort _) 
\Rightarrow c0 | (CHead c1 _ _) \Rightarrow c1])) in (let TMP_101 \def (r k0 
d0) in (let TMP_102 \def (lift h0 TMP_101 u0) in (let TMP_103 \def (CHead c0 
k0 TMP_102) in (let TMP_104 \def (CHead c k u) in (let H6 \def (f_equal C C 
TMP_100 TMP_103 TMP_104 H5) in (let TMP_105 \def (\lambda (e0: C).(match e0 
with [(CSort _) \Rightarrow k0 | (CHead _ k1 _) \Rightarrow k1])) in (let 
TMP_106 \def (r k0 d0) in (let TMP_107 \def (lift h0 TMP_106 u0) in (let 
TMP_108 \def (CHead c0 k0 TMP_107) in (let TMP_109 \def (CHead c k u) in (let 
H7 \def (f_equal C K TMP_105 TMP_108 TMP_109 H5) in (let TMP_117 \def 
(\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow (let TMP_115 \def 
(\lambda (x0: nat).(plus x0 h0)) in (let TMP_116 \def (r k0 d0) in (lref_map 
TMP_115 TMP_116 u0))) | (CHead _ _ t) \Rightarrow t])) in (let TMP_118 \def 
(r k0 d0) in (let TMP_119 \def (lift h0 TMP_118 u0) in (let TMP_120 \def 
(CHead c0 k0 TMP_119) in (let TMP_121 \def (CHead c k u) in (let H8 \def 
(f_equal C T TMP_117 TMP_120 TMP_121 H5) in (let TMP_219 \def (\lambda (H9: 
(eq K k0 k)).(\lambda (H10: (eq C c0 c)).(let TMP_129 \def (\lambda (c1: 
C).((eq nat (r k0 d0) (S d)) \to ((eq C c1 (CHead c k u)) \to (let TMP_123 
\def (\lambda (e0: C).(\lambda (v: T).(let TMP_122 \def (CHead e0 k v) in (eq 
C e TMP_122)))) in (let TMP_126 \def (\lambda (_: C).(\lambda (v: T).(let 
TMP_124 \def (r k d) in (let TMP_125 \def (lift h0 TMP_124 v) in (eq T u 
TMP_125))))) in (let TMP_128 \def (\lambda (e0: C).(\lambda (_: T).(let 
TMP_127 \def (r k d) in (drop h0 TMP_127 c e0)))) in (ex3_2 C T TMP_123 
TMP_126 TMP_128))))))) in (let H11 \def (eq_ind C c0 TMP_129 H3 c H10) in 
(let TMP_131 \def (\lambda (c1: C).(let TMP_130 \def (r k0 d0) in (drop h0 
TMP_130 c1 e))) in (let H12 \def (eq_ind C c0 TMP_131 H2 c H10) in (let 
TMP_134 \def (\lambda (k1: K).(let TMP_132 \def (r k1 d0) in (let TMP_133 
\def (lift h0 TMP_132 u0) in (eq T TMP_133 u)))) in (let H13 \def (eq_ind K 
k0 TMP_134 H8 k H9) in (let TMP_142 \def (\lambda (k1: K).((eq nat (r k1 d0) 
(S d)) \to ((eq C c (CHead c k u)) \to (let TMP_136 \def (\lambda (e0: 
C).(\lambda (v: T).(let TMP_135 \def (CHead e0 k v) in (eq C e TMP_135)))) in 
(let TMP_139 \def (\lambda (_: C).(\lambda (v: T).(let TMP_137 \def (r k d) 
in (let TMP_138 \def (lift h0 TMP_137 v) in (eq T u TMP_138))))) in (let 
TMP_141 \def (\lambda (e0: C).(\lambda (_: T).(let TMP_140 \def (r k d) in 
(drop h0 TMP_140 c e0)))) in (ex3_2 C T TMP_136 TMP_139 TMP_141))))))) in 
(let H14 \def (eq_ind K k0 TMP_142 H11 k H9) in (let TMP_144 \def (\lambda 
(k1: K).(let TMP_143 \def (r k1 d0) in (drop h0 TMP_143 c e))) in (let H15 
\def (eq_ind K k0 TMP_144 H12 k H9) in (let TMP_153 \def (\lambda (k1: 
K).(let TMP_147 \def (\lambda (e0: C).(\lambda (v: T).(let TMP_145 \def 
(CHead e k1 u0) in (let TMP_146 \def (CHead e0 k v) in (eq C TMP_145 
TMP_146))))) in (let TMP_150 \def (\lambda (_: C).(\lambda (v: T).(let 
TMP_148 \def (r k d) in (let TMP_149 \def (lift h0 TMP_148 v) in (eq T u 
TMP_149))))) in (let TMP_152 \def (\lambda (e0: C).(\lambda (_: T).(let 
TMP_151 \def (r k d) in (drop h0 TMP_151 c e0)))) in (ex3_2 C T TMP_147 
TMP_150 TMP_152))))) in (let TMP_161 \def (\lambda (t: T).((eq nat (r k d0) 
(S d)) \to ((eq C c (CHead c k t)) \to (let TMP_155 \def (\lambda (e0: 
C).(\lambda (v: T).(let TMP_154 \def (CHead e0 k v) in (eq C e TMP_154)))) in 
(let TMP_158 \def (\lambda (_: C).(\lambda (v: T).(let TMP_156 \def (r k d) 
in (let TMP_157 \def (lift h0 TMP_156 v) in (eq T t TMP_157))))) in (let 
TMP_160 \def (\lambda (e0: C).(\lambda (_: T).(let TMP_159 \def (r k d) in 
(drop h0 TMP_159 c e0)))) in (ex3_2 C T TMP_155 TMP_158 TMP_160))))))) in 
(let TMP_162 \def (r k d0) in (let TMP_163 \def (lift h0 TMP_162 u0) in (let 
H16 \def (eq_ind_r T u TMP_161 H14 TMP_163 H13) in (let TMP_164 \def (r k d0) 
in (let TMP_165 \def (lift h0 TMP_164 u0) in (let TMP_174 \def (\lambda (t: 
T).(let TMP_168 \def (\lambda (e0: C).(\lambda (v: T).(let TMP_166 \def 
(CHead e k u0) in (let TMP_167 \def (CHead e0 k v) in (eq C TMP_166 
TMP_167))))) in (let TMP_171 \def (\lambda (_: C).(\lambda (v: T).(let 
TMP_169 \def (r k d) in (let TMP_170 \def (lift h0 TMP_169 v) in (eq T t 
TMP_170))))) in (let TMP_173 \def (\lambda (e0: C).(\lambda (_: T).(let 
TMP_172 \def (r k d) in (drop h0 TMP_172 c e0)))) in (ex3_2 C T TMP_168 
TMP_171 TMP_173))))) in (let TMP_175 \def (\lambda (e0: nat).(match e0 with 
[O \Rightarrow d0 | (S n) \Rightarrow n])) in (let TMP_176 \def (S d0) in 
(let TMP_177 \def (S d) in (let H17 \def (f_equal nat nat TMP_175 TMP_176 
TMP_177 H4) in (let TMP_187 \def (\lambda (n: nat).((eq nat (r k n) (S d)) 
\to ((eq C c (CHead c k (lift h0 (r k n) u0))) \to (let TMP_179 \def (\lambda 
(e0: C).(\lambda (v: T).(let TMP_178 \def (CHead e0 k v) in (eq C e 
TMP_178)))) in (let TMP_184 \def (\lambda (_: C).(\lambda (v: T).(let TMP_180 
\def (r k n) in (let TMP_181 \def (lift h0 TMP_180 u0) in (let TMP_182 \def 
(r k d) in (let TMP_183 \def (lift h0 TMP_182 v) in (eq T TMP_181 
TMP_183))))))) in (let TMP_186 \def (\lambda (e0: C).(\lambda (_: T).(let 
TMP_185 \def (r k d) in (drop h0 TMP_185 c e0)))) in (ex3_2 C T TMP_179 
TMP_184 TMP_186))))))) in (let H18 \def (eq_ind nat d0 TMP_187 H16 d H17) in 
(let TMP_189 \def (\lambda (n: nat).(let TMP_188 \def (r k n) in (drop h0 
TMP_188 c e))) in (let H19 \def (eq_ind nat d0 TMP_189 H15 d H17) in (let 
TMP_200 \def (\lambda (n: nat).(let TMP_192 \def (\lambda (e0: C).(\lambda 
(v: T).(let TMP_190 \def (CHead e k u0) in (let TMP_191 \def (CHead e0 k v) 
in (eq C TMP_190 TMP_191))))) in (let TMP_197 \def (\lambda (_: C).(\lambda 
(v: T).(let TMP_193 \def (r k n) in (let TMP_194 \def (lift h0 TMP_193 u0) in 
(let TMP_195 \def (r k d) in (let TMP_196 \def (lift h0 TMP_195 v) in (eq T 
TMP_194 TMP_196))))))) in (let TMP_199 \def (\lambda (e0: C).(\lambda (_: 
T).(let TMP_198 \def (r k d) in (drop h0 TMP_198 c e0)))) in (ex3_2 C T 
TMP_192 TMP_197 TMP_199))))) in (let TMP_203 \def (\lambda (e0: C).(\lambda 
(v: T).(let TMP_201 \def (CHead e k u0) in (let TMP_202 \def (CHead e0 k v) 
in (eq C TMP_201 TMP_202))))) in (let TMP_208 \def (\lambda (_: C).(\lambda 
(v: T).(let TMP_204 \def (r k d) in (let TMP_205 \def (lift h0 TMP_204 u0) in 
(let TMP_206 \def (r k d) in (let TMP_207 \def (lift h0 TMP_206 v) in (eq T 
TMP_205 TMP_207))))))) in (let TMP_210 \def (\lambda (e0: C).(\lambda (_: 
T).(let TMP_209 \def (r k d) in (drop h0 TMP_209 c e0)))) in (let TMP_211 
\def (CHead e k u0) in (let TMP_212 \def (refl_equal C TMP_211) in (let 
TMP_213 \def (r k d) in (let TMP_214 \def (lift h0 TMP_213 u0) in (let 
TMP_215 \def (refl_equal T TMP_214) in (let TMP_216 \def (ex3_2_intro C T 
TMP_203 TMP_208 TMP_210 e u0 TMP_212 TMP_215 H19) in (let TMP_217 \def 
(eq_ind_r nat d TMP_200 TMP_216 d0 H17) in (let TMP_218 \def (eq_ind T 
TMP_165 TMP_174 TMP_217 u H13) in (eq_ind_r K k TMP_153 TMP_218 k0 
H9))))))))))))))))))))))))))))))))))))))))) in (let TMP_220 \def (TMP_219 H7) 
in (TMP_220 H6))))))))))))))))))))))))))))))) in (drop_ind TMP_29 TMP_51 
TMP_99 TMP_221 h y0 y x H1))))))) in (insert_eq nat TMP_12 TMP_13 TMP_21 
TMP_222 H0))))))) in (insert_eq C TMP_1 TMP_3 TMP_11 TMP_223 H))))))))))).

theorem drop_S:
 \forall (b: B).(\forall (c: C).(\forall (e: C).(\forall (u: T).(\forall (h: 
nat).((drop h O c (CHead e (Bind b) u)) \to (drop (S h) O c e))))))
\def
 \lambda (b: B).(\lambda (c: C).(let TMP_2 \def (\lambda (c0: C).(\forall (e: 
C).(\forall (u: T).(\forall (h: nat).((drop h O c0 (CHead e (Bind b) u)) \to 
(let TMP_1 \def (S h) in (drop TMP_1 O c0 e))))))) in (let TMP_27 \def 
(\lambda (n: nat).(\lambda (e: C).(\lambda (u: T).(\lambda (h: nat).(\lambda 
(H: (drop h O (CSort n) (CHead e (Bind b) u))).(let TMP_3 \def (Bind b) in 
(let TMP_4 \def (CHead e TMP_3 u) in (let TMP_5 \def (CSort n) in (let TMP_6 
\def (eq C TMP_4 TMP_5) in (let TMP_7 \def (eq nat h O) in (let TMP_8 \def 
(eq nat O O) in (let TMP_9 \def (S h) in (let TMP_10 \def (CSort n) in (let 
TMP_11 \def (drop TMP_9 O TMP_10 e) in (let TMP_23 \def (\lambda (H0: (eq C 
(CHead e (Bind b) u) (CSort n))).(\lambda (H1: (eq nat h O)).(\lambda (_: (eq 
nat O O)).(let TMP_14 \def (\lambda (n0: nat).(let TMP_12 \def (S n0) in (let 
TMP_13 \def (CSort n) in (drop TMP_12 O TMP_13 e)))) in (let TMP_15 \def 
(Bind b) in (let TMP_16 \def (CHead e TMP_15 u) in (let TMP_17 \def (\lambda 
(ee: C).(match ee with [(CSort _) \Rightarrow False | (CHead _ _ _) 
\Rightarrow True])) in (let TMP_18 \def (CSort n) in (let H3 \def (eq_ind C 
TMP_16 TMP_17 I TMP_18 H0) in (let TMP_19 \def (S O) in (let TMP_20 \def 
(CSort n) in (let TMP_21 \def (drop TMP_19 O TMP_20 e) in (let TMP_22 \def 
(False_ind TMP_21 H3) in (eq_ind_r nat O TMP_14 TMP_22 h H1)))))))))))))) in 
(let TMP_24 \def (Bind b) in (let TMP_25 \def (CHead e TMP_24 u) in (let 
TMP_26 \def (drop_gen_sort n h O TMP_25 H) in (and3_ind TMP_6 TMP_7 TMP_8 
TMP_11 TMP_23 TMP_26))))))))))))))))))) in (let TMP_83 \def (\lambda (c0: 
C).(\lambda (H: ((\forall (e: C).(\forall (u: T).(\forall (h: nat).((drop h O 
c0 (CHead e (Bind b) u)) \to (drop (S h) O c0 e))))))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (e: C).(\lambda (u: T).(\lambda (h: nat).(let 
TMP_30 \def (\lambda (n: nat).((drop n O (CHead c0 k t) (CHead e (Bind b) u)) 
\to (let TMP_28 \def (S n) in (let TMP_29 \def (CHead c0 k t) in (drop TMP_28 
O TMP_29 e))))) in (let TMP_68 \def (\lambda (H0: (drop O O (CHead c0 k t) 
(CHead e (Bind b) u))).(let TMP_31 \def (\lambda (e0: C).(match e0 with 
[(CSort _) \Rightarrow c0 | (CHead c1 _ _) \Rightarrow c1])) in (let TMP_32 
\def (CHead c0 k t) in (let TMP_33 \def (Bind b) in (let TMP_34 \def (CHead e 
TMP_33 u) in (let TMP_35 \def (CHead c0 k t) in (let TMP_36 \def (Bind b) in 
(let TMP_37 \def (CHead e TMP_36 u) in (let TMP_38 \def (drop_gen_refl TMP_35 
TMP_37 H0) in (let H1 \def (f_equal C C TMP_31 TMP_32 TMP_34 TMP_38) in (let 
TMP_39 \def (\lambda (e0: C).(match e0 with [(CSort _) \Rightarrow k | (CHead 
_ k0 _) \Rightarrow k0])) in (let TMP_40 \def (CHead c0 k t) in (let TMP_41 
\def (Bind b) in (let TMP_42 \def (CHead e TMP_41 u) in (let TMP_43 \def 
(CHead c0 k t) in (let TMP_44 \def (Bind b) in (let TMP_45 \def (CHead e 
TMP_44 u) in (let TMP_46 \def (drop_gen_refl TMP_43 TMP_45 H0) in (let H2 
\def (f_equal C K TMP_39 TMP_40 TMP_42 TMP_46) in (let TMP_47 \def (\lambda 
(e0: C).(match e0 with [(CSort _) \Rightarrow t | (CHead _ _ t0) \Rightarrow 
t0])) in (let TMP_48 \def (CHead c0 k t) in (let TMP_49 \def (Bind b) in (let 
TMP_50 \def (CHead e TMP_49 u) in (let TMP_51 \def (CHead c0 k t) in (let 
TMP_52 \def (Bind b) in (let TMP_53 \def (CHead e TMP_52 u) in (let TMP_54 
\def (drop_gen_refl TMP_51 TMP_53 H0) in (let H3 \def (f_equal C T TMP_47 
TMP_48 TMP_50 TMP_54) in (let TMP_66 \def (\lambda (H4: (eq K k (Bind 
b))).(\lambda (H5: (eq C c0 e)).(let TMP_57 \def (\lambda (c1: C).(let TMP_55 
\def (S O) in (let TMP_56 \def (CHead c0 k t) in (drop TMP_55 O TMP_56 c1)))) 
in (let TMP_58 \def (Bind b) in (let TMP_61 \def (\lambda (k0: K).(let TMP_59 
\def (S O) in (let TMP_60 \def (CHead c0 k0 t) in (drop TMP_59 O TMP_60 
c0)))) in (let TMP_62 \def (Bind b) in (let TMP_63 \def (drop_refl c0) in 
(let TMP_64 \def (drop_drop TMP_62 O c0 c0 TMP_63 t) in (let TMP_65 \def 
(eq_ind_r K TMP_58 TMP_61 TMP_64 k H4) in (eq_ind C c0 TMP_57 TMP_65 e 
H5)))))))))) in (let TMP_67 \def (TMP_66 H2) in (TMP_67 
H1))))))))))))))))))))))))))))))) in (let TMP_82 \def (\lambda (n: 
nat).(\lambda (_: (((drop n O (CHead c0 k t) (CHead e (Bind b) u)) \to (drop 
(S n) O (CHead c0 k t) e)))).(\lambda (H1: (drop (S n) O (CHead c0 k t) 
(CHead e (Bind b) u))).(let TMP_69 \def (S n) in (let TMP_70 \def (r k n) in 
(let TMP_71 \def (S TMP_70) in (let TMP_72 \def (\lambda (n0: nat).(drop n0 O 
c0 e)) in (let TMP_73 \def (r k n) in (let TMP_74 \def (Bind b) in (let 
TMP_75 \def (CHead e TMP_74 u) in (let TMP_76 \def (drop_gen_drop k c0 TMP_75 
t n H1) in (let TMP_77 \def (H e u TMP_73 TMP_76) in (let TMP_78 \def (S n) 
in (let TMP_79 \def (r k TMP_78) in (let TMP_80 \def (r_S k n) in (let TMP_81 
\def (eq_ind_r nat TMP_71 TMP_72 TMP_77 TMP_79 TMP_80) in (drop_drop k TMP_69 
c0 e TMP_81 t))))))))))))))))) in (nat_ind TMP_30 TMP_68 TMP_82 h))))))))))) 
in (C_ind TMP_2 TMP_27 TMP_83 c))))).

theorem drop_mono:
 \forall (c: C).(\forall (x1: C).(\forall (d: nat).(\forall (h: nat).((drop h 
d c x1) \to (\forall (x2: C).((drop h d c x2) \to (eq C x1 x2)))))))
\def
 \lambda (c: C).(let TMP_1 \def (\lambda (c0: C).(\forall (x1: C).(\forall 
(d: nat).(\forall (h: nat).((drop h d c0 x1) \to (\forall (x2: C).((drop h d 
c0 x2) \to (eq C x1 x2)))))))) in (let TMP_26 \def (\lambda (n: nat).(\lambda 
(x1: C).(\lambda (d: nat).(\lambda (h: nat).(\lambda (H: (drop h d (CSort n) 
x1)).(\lambda (x2: C).(\lambda (H0: (drop h d (CSort n) x2)).(let TMP_2 \def 
(CSort n) in (let TMP_3 \def (eq C x2 TMP_2) in (let TMP_4 \def (eq nat h O) 
in (let TMP_5 \def (eq nat d O) in (let TMP_6 \def (eq C x1 x2) in (let 
TMP_24 \def (\lambda (H1: (eq C x2 (CSort n))).(\lambda (H2: (eq nat h 
O)).(\lambda (H3: (eq nat d O)).(let TMP_7 \def (CSort n) in (let TMP_8 \def 
(eq C x1 TMP_7) in (let TMP_9 \def (eq nat h O) in (let TMP_10 \def (eq nat d 
O) in (let TMP_11 \def (eq C x1 x2) in (let TMP_22 \def (\lambda (H4: (eq C 
x1 (CSort n))).(\lambda (H5: (eq nat h O)).(\lambda (H6: (eq nat d O)).(let 
TMP_12 \def (CSort n) in (let TMP_13 \def (\lambda (c0: C).(eq C x1 c0)) in 
(let TMP_14 \def (\lambda (n0: nat).(eq nat n0 O)) in (let H7 \def (eq_ind 
nat h TMP_14 H2 O H5) in (let TMP_15 \def (\lambda (n0: nat).(eq nat n0 O)) 
in (let H8 \def (eq_ind nat d TMP_15 H3 O H6) in (let TMP_16 \def (CSort n) 
in (let TMP_18 \def (\lambda (c0: C).(let TMP_17 \def (CSort n) in (eq C c0 
TMP_17))) in (let TMP_19 \def (CSort n) in (let TMP_20 \def (refl_equal C 
TMP_19) in (let TMP_21 \def (eq_ind_r C TMP_16 TMP_18 TMP_20 x1 H4) in 
(eq_ind_r C TMP_12 TMP_13 TMP_21 x2 H1))))))))))))))) in (let TMP_23 \def 
(drop_gen_sort n h d x1 H) in (and3_ind TMP_8 TMP_9 TMP_10 TMP_11 TMP_22 
TMP_23))))))))))) in (let TMP_25 \def (drop_gen_sort n h d x2 H0) in 
(and3_ind TMP_3 TMP_4 TMP_5 TMP_6 TMP_24 TMP_25))))))))))))))) in (let 
TMP_109 \def (\lambda (c0: C).(\lambda (H: ((\forall (x1: C).(\forall (d: 
nat).(\forall (h: nat).((drop h d c0 x1) \to (\forall (x2: C).((drop h d c0 
x2) \to (eq C x1 x2))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (x1: 
C).(\lambda (d: nat).(let TMP_27 \def (\lambda (n: nat).(\forall (h: 
nat).((drop h n (CHead c0 k t) x1) \to (\forall (x2: C).((drop h n (CHead c0 
k t) x2) \to (eq C x1 x2)))))) in (let TMP_46 \def (\lambda (h: nat).(let 
TMP_28 \def (\lambda (n: nat).((drop n O (CHead c0 k t) x1) \to (\forall (x2: 
C).((drop n O (CHead c0 k t) x2) \to (eq C x1 x2))))) in (let TMP_41 \def 
(\lambda (H0: (drop O O (CHead c0 k t) x1)).(\lambda (x2: C).(\lambda (H1: 
(drop O O (CHead c0 k t) x2)).(let TMP_29 \def (CHead c0 k t) in (let TMP_30 
\def (\lambda (c1: C).(eq C x1 c1)) in (let TMP_31 \def (CHead c0 k t) in 
(let TMP_33 \def (\lambda (c1: C).(let TMP_32 \def (CHead c0 k t) in (eq C c1 
TMP_32))) in (let TMP_34 \def (CHead c0 k t) in (let TMP_35 \def (refl_equal 
C TMP_34) in (let TMP_36 \def (CHead c0 k t) in (let TMP_37 \def 
(drop_gen_refl TMP_36 x1 H0) in (let TMP_38 \def (eq_ind C TMP_31 TMP_33 
TMP_35 x1 TMP_37) in (let TMP_39 \def (CHead c0 k t) in (let TMP_40 \def 
(drop_gen_refl TMP_39 x2 H1) in (eq_ind C TMP_29 TMP_30 TMP_38 x2 
TMP_40))))))))))))))) in (let TMP_45 \def (\lambda (n: nat).(\lambda (_: 
(((drop n O (CHead c0 k t) x1) \to (\forall (x2: C).((drop n O (CHead c0 k t) 
x2) \to (eq C x1 x2)))))).(\lambda (H1: (drop (S n) O (CHead c0 k t) 
x1)).(\lambda (x2: C).(\lambda (H2: (drop (S n) O (CHead c0 k t) x2)).(let 
TMP_42 \def (r k n) in (let TMP_43 \def (drop_gen_drop k c0 x1 t n H1) in 
(let TMP_44 \def (drop_gen_drop k c0 x2 t n H2) in (H x1 O TMP_42 TMP_43 x2 
TMP_44))))))))) in (nat_ind TMP_28 TMP_41 TMP_45 h))))) in (let TMP_108 \def 
(\lambda (n: nat).(\lambda (H0: ((\forall (h: nat).((drop h n (CHead c0 k t) 
x1) \to (\forall (x2: C).((drop h n (CHead c0 k t) x2) \to (eq C x1 
x2))))))).(\lambda (h: nat).(\lambda (H1: (drop h (S n) (CHead c0 k t) 
x1)).(\lambda (x2: C).(\lambda (H2: (drop h (S n) (CHead c0 k t) x2)).(let 
TMP_48 \def (\lambda (e: C).(\lambda (v: T).(let TMP_47 \def (CHead e k v) in 
(eq C x2 TMP_47)))) in (let TMP_51 \def (\lambda (_: C).(\lambda (v: T).(let 
TMP_49 \def (r k n) in (let TMP_50 \def (lift h TMP_49 v) in (eq T t 
TMP_50))))) in (let TMP_53 \def (\lambda (e: C).(\lambda (_: T).(let TMP_52 
\def (r k n) in (drop h TMP_52 c0 e)))) in (let TMP_54 \def (eq C x1 x2) in 
(let TMP_106 \def (\lambda (x0: C).(\lambda (x3: T).(\lambda (H3: (eq C x2 
(CHead x0 k x3))).(\lambda (H4: (eq T t (lift h (r k n) x3))).(\lambda (H5: 
(drop h (r k n) c0 x0)).(let TMP_56 \def (\lambda (e: C).(\lambda (v: T).(let 
TMP_55 \def (CHead e k v) in (eq C x1 TMP_55)))) in (let TMP_59 \def (\lambda 
(_: C).(\lambda (v: T).(let TMP_57 \def (r k n) in (let TMP_58 \def (lift h 
TMP_57 v) in (eq T t TMP_58))))) in (let TMP_61 \def (\lambda (e: C).(\lambda 
(_: T).(let TMP_60 \def (r k n) in (drop h TMP_60 c0 e)))) in (let TMP_62 
\def (eq C x1 x2) in (let TMP_104 \def (\lambda (x4: C).(\lambda (x5: 
T).(\lambda (H6: (eq C x1 (CHead x4 k x5))).(\lambda (H7: (eq T t (lift h (r 
k n) x5))).(\lambda (H8: (drop h (r k n) c0 x4)).(let TMP_63 \def (CHead x0 k 
x3) in (let TMP_64 \def (\lambda (c1: C).(eq C x1 c1)) in (let TMP_65 \def 
(\lambda (c1: C).(\forall (h0: nat).((drop h0 n (CHead c0 k t) c1) \to 
(\forall (x6: C).((drop h0 n (CHead c0 k t) x6) \to (eq C c1 x6)))))) in (let 
TMP_66 \def (CHead x4 k x5) in (let H9 \def (eq_ind C x1 TMP_65 H0 TMP_66 H6) 
in (let TMP_67 \def (CHead x4 k x5) in (let TMP_69 \def (\lambda (c1: C).(let 
TMP_68 \def (CHead x0 k x3) in (eq C c1 TMP_68))) in (let TMP_71 \def 
(\lambda (t0: T).(\forall (h0: nat).((drop h0 n (CHead c0 k t0) (CHead x4 k 
x5)) \to (\forall (x6: C).((drop h0 n (CHead c0 k t0) x6) \to (let TMP_70 
\def (CHead x4 k x5) in (eq C TMP_70 x6))))))) in (let TMP_72 \def (r k n) in 
(let TMP_73 \def (lift h TMP_72 x5) in (let H10 \def (eq_ind T t TMP_71 H9 
TMP_73 H7) in (let TMP_76 \def (\lambda (t0: T).(let TMP_74 \def (r k n) in 
(let TMP_75 \def (lift h TMP_74 x3) in (eq T t0 TMP_75)))) in (let TMP_77 
\def (r k n) in (let TMP_78 \def (lift h TMP_77 x5) in (let H11 \def (eq_ind 
T t TMP_76 H4 TMP_78 H7) in (let TMP_80 \def (\lambda (t0: T).(\forall (h0: 
nat).((drop h0 n (CHead c0 k (lift h (r k n) t0)) (CHead x4 k t0)) \to 
(\forall (x6: C).((drop h0 n (CHead c0 k (lift h (r k n) t0)) x6) \to (let 
TMP_79 \def (CHead x4 k t0) in (eq C TMP_79 x6))))))) in (let TMP_81 \def (r 
k n) in (let TMP_82 \def (lift_inj x5 x3 h TMP_81 H11) in (let H12 \def 
(eq_ind T x5 TMP_80 H10 x3 TMP_82) in (let TMP_85 \def (\lambda (t0: T).(let 
TMP_83 \def (CHead x4 k t0) in (let TMP_84 \def (CHead x0 k x3) in (eq C 
TMP_83 TMP_84)))) in (let TMP_86 \def (CHead x0 k x3) in (let TMP_87 \def 
(CHead x4 k x3) in (let TMP_88 \def (CHead x4 k x3) in (let TMP_89 \def 
(CHead x0 k x3) in (let TMP_90 \def (CHead x0 k x3) in (let TMP_91 \def 
(CHead x4 k x3) in (let TMP_92 \def (r k n) in (let TMP_93 \def (H x0 TMP_92 
h H5 x4 H8) in (let TMP_94 \def (refl_equal K k) in (let TMP_95 \def 
(refl_equal T x3) in (let TMP_96 \def (f_equal3 C K T C CHead x0 x4 k k x3 x3 
TMP_93 TMP_94 TMP_95) in (let TMP_97 \def (sym_eq C TMP_90 TMP_91 TMP_96) in 
(let TMP_98 \def (sym_eq C TMP_88 TMP_89 TMP_97) in (let TMP_99 \def (sym_eq 
C TMP_86 TMP_87 TMP_98) in (let TMP_100 \def (r k n) in (let TMP_101 \def 
(lift_inj x5 x3 h TMP_100 H11) in (let TMP_102 \def (eq_ind_r T x3 TMP_85 
TMP_99 x5 TMP_101) in (let TMP_103 \def (eq_ind_r C TMP_67 TMP_69 TMP_102 x1 
H6) in (eq_ind_r C TMP_63 TMP_64 TMP_103 x2 
H3)))))))))))))))))))))))))))))))))))))))))))) in (let TMP_105 \def 
(drop_gen_skip_l c0 x1 t h n k H1) in (ex3_2_ind C T TMP_56 TMP_59 TMP_61 
TMP_62 TMP_104 TMP_105)))))))))))) in (let TMP_107 \def (drop_gen_skip_l c0 
x2 t h n k H2) in (ex3_2_ind C T TMP_48 TMP_51 TMP_53 TMP_54 TMP_106 
TMP_107))))))))))))) in (nat_ind TMP_27 TMP_46 TMP_108 d)))))))))) in (C_ind 
TMP_1 TMP_26 TMP_109 c)))).

