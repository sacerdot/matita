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

include "basic_1/cimp/defs.ma".

include "basic_1/getl/getl.ma".

theorem cimp_flat_sx:
 \forall (f: F).(\forall (c: C).(\forall (v: T).(cimp (CHead c (Flat f) v) 
c)))
\def
 \lambda (f: F).(\lambda (c: C).(\lambda (v: T).(\lambda (b: B).(\lambda (d1: 
C).(\lambda (w: T).(\lambda (h: nat).(\lambda (H: (getl h (CHead c (Flat f) 
v) (CHead d1 (Bind b) w))).(let TMP_4 \def (\lambda (n: nat).((getl n (CHead 
c (Flat f) v) (CHead d1 (Bind b) w)) \to (let TMP_3 \def (\lambda (d2: 
C).(let TMP_1 \def (Bind b) in (let TMP_2 \def (CHead d2 TMP_1 w) in (getl n 
c TMP_2)))) in (ex C TMP_3)))) in (let TMP_20 \def (\lambda (H0: (getl O 
(CHead c (Flat f) v) (CHead d1 (Bind b) w))).(let TMP_7 \def (\lambda (d2: 
C).(let TMP_5 \def (Bind b) in (let TMP_6 \def (CHead d2 TMP_5 w) in (getl O 
c TMP_6)))) in (let TMP_8 \def (Bind b) in (let TMP_9 \def (CHead d1 TMP_8 w) 
in (let TMP_10 \def (drop_refl c) in (let TMP_11 \def (Bind b) in (let TMP_12 
\def (CHead d1 TMP_11 w) in (let TMP_13 \def (Flat f) in (let TMP_14 \def 
(CHead c TMP_13 v) in (let TMP_15 \def (Bind b) in (let TMP_16 \def (CHead d1 
TMP_15 w) in (let TMP_17 \def (getl_gen_O TMP_14 TMP_16 H0) in (let TMP_18 
\def (clear_gen_flat f c TMP_12 v TMP_17) in (let TMP_19 \def (getl_intro O c 
TMP_9 c TMP_10 TMP_18) in (ex_intro C TMP_7 d1 TMP_19))))))))))))))) in (let 
TMP_29 \def (\lambda (h0: nat).(\lambda (_: (((getl h0 (CHead c (Flat f) v) 
(CHead d1 (Bind b) w)) \to (ex C (\lambda (d2: C).(getl h0 c (CHead d2 (Bind 
b) w))))))).(\lambda (H0: (getl (S h0) (CHead c (Flat f) v) (CHead d1 (Bind 
b) w))).(let TMP_24 \def (\lambda (d2: C).(let TMP_21 \def (S h0) in (let 
TMP_22 \def (Bind b) in (let TMP_23 \def (CHead d2 TMP_22 w) in (getl TMP_21 
c TMP_23))))) in (let TMP_25 \def (Flat f) in (let TMP_26 \def (Bind b) in 
(let TMP_27 \def (CHead d1 TMP_26 w) in (let TMP_28 \def (getl_gen_S TMP_25 c 
TMP_27 v h0 H0) in (ex_intro C TMP_24 d1 TMP_28))))))))) in (nat_ind TMP_4 
TMP_20 TMP_29 h H))))))))))).

theorem cimp_flat_dx:
 \forall (f: F).(\forall (c: C).(\forall (v: T).(cimp c (CHead c (Flat f) 
v))))
\def
 \lambda (f: F).(\lambda (c: C).(\lambda (v: T).(\lambda (b: B).(\lambda (d1: 
C).(\lambda (w: T).(\lambda (h: nat).(\lambda (H: (getl h c (CHead d1 (Bind 
b) w))).(let TMP_5 \def (\lambda (d2: C).(let TMP_1 \def (Flat f) in (let 
TMP_2 \def (CHead c TMP_1 v) in (let TMP_3 \def (Bind b) in (let TMP_4 \def 
(CHead d2 TMP_3 w) in (getl h TMP_2 TMP_4)))))) in (let TMP_6 \def (Bind b) 
in (let TMP_7 \def (CHead d1 TMP_6 w) in (let TMP_8 \def (getl_flat c TMP_7 h 
H f v) in (ex_intro C TMP_5 d1 TMP_8)))))))))))).

theorem cimp_bind:
 \forall (c1: C).(\forall (c2: C).((cimp c1 c2) \to (\forall (b: B).(\forall 
(v: T).(cimp (CHead c1 (Bind b) v) (CHead c2 (Bind b) v))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: ((\forall (b: B).(\forall (d1: 
C).(\forall (w: T).(\forall (h: nat).((getl h c1 (CHead d1 (Bind b) w)) \to 
(ex C (\lambda (d2: C).(getl h c2 (CHead d2 (Bind b) w))))))))))).(\lambda 
(b: B).(\lambda (v: T).(\lambda (b0: B).(\lambda (d1: C).(\lambda (w: 
T).(\lambda (h: nat).(\lambda (H0: (getl h (CHead c1 (Bind b) v) (CHead d1 
(Bind b0) w))).(let TMP_6 \def (\lambda (n: nat).((getl n (CHead c1 (Bind b) 
v) (CHead d1 (Bind b0) w)) \to (let TMP_5 \def (\lambda (d2: C).(let TMP_1 
\def (Bind b) in (let TMP_2 \def (CHead c2 TMP_1 v) in (let TMP_3 \def (Bind 
b0) in (let TMP_4 \def (CHead d2 TMP_3 w) in (getl n TMP_2 TMP_4)))))) in (ex 
C TMP_5)))) in (let TMP_68 \def (\lambda (H1: (getl O (CHead c1 (Bind b) v) 
(CHead d1 (Bind b0) w))).(let TMP_7 \def (\lambda (e: C).(match e with 
[(CSort _) \Rightarrow d1 | (CHead c _ _) \Rightarrow c])) in (let TMP_8 \def 
(Bind b0) in (let TMP_9 \def (CHead d1 TMP_8 w) in (let TMP_10 \def (Bind b) 
in (let TMP_11 \def (CHead c1 TMP_10 v) in (let TMP_12 \def (Bind b0) in (let 
TMP_13 \def (CHead d1 TMP_12 w) in (let TMP_14 \def (Bind b) in (let TMP_15 
\def (CHead c1 TMP_14 v) in (let TMP_16 \def (Bind b0) in (let TMP_17 \def 
(CHead d1 TMP_16 w) in (let TMP_18 \def (getl_gen_O TMP_15 TMP_17 H1) in (let 
TMP_19 \def (clear_gen_bind b c1 TMP_13 v TMP_18) in (let H2 \def (f_equal C 
C TMP_7 TMP_9 TMP_11 TMP_19) in (let TMP_20 \def (\lambda (e: C).(match e 
with [(CSort _) \Rightarrow b0 | (CHead _ k _) \Rightarrow (match k with 
[(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow b0])])) in (let TMP_21 \def 
(Bind b0) in (let TMP_22 \def (CHead d1 TMP_21 w) in (let TMP_23 \def (Bind 
b) in (let TMP_24 \def (CHead c1 TMP_23 v) in (let TMP_25 \def (Bind b0) in 
(let TMP_26 \def (CHead d1 TMP_25 w) in (let TMP_27 \def (Bind b) in (let 
TMP_28 \def (CHead c1 TMP_27 v) in (let TMP_29 \def (Bind b0) in (let TMP_30 
\def (CHead d1 TMP_29 w) in (let TMP_31 \def (getl_gen_O TMP_28 TMP_30 H1) in 
(let TMP_32 \def (clear_gen_bind b c1 TMP_26 v TMP_31) in (let H3 \def 
(f_equal C B TMP_20 TMP_22 TMP_24 TMP_32) in (let TMP_33 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow w | (CHead _ _ t) \Rightarrow t])) in 
(let TMP_34 \def (Bind b0) in (let TMP_35 \def (CHead d1 TMP_34 w) in (let 
TMP_36 \def (Bind b) in (let TMP_37 \def (CHead c1 TMP_36 v) in (let TMP_38 
\def (Bind b0) in (let TMP_39 \def (CHead d1 TMP_38 w) in (let TMP_40 \def 
(Bind b) in (let TMP_41 \def (CHead c1 TMP_40 v) in (let TMP_42 \def (Bind 
b0) in (let TMP_43 \def (CHead d1 TMP_42 w) in (let TMP_44 \def (getl_gen_O 
TMP_41 TMP_43 H1) in (let TMP_45 \def (clear_gen_bind b c1 TMP_39 v TMP_44) 
in (let H4 \def (f_equal C T TMP_33 TMP_35 TMP_37 TMP_45) in (let TMP_66 \def 
(\lambda (H5: (eq B b0 b)).(\lambda (_: (eq C d1 c1)).(let TMP_51 \def 
(\lambda (t: T).(let TMP_50 \def (\lambda (d2: C).(let TMP_46 \def (Bind b) 
in (let TMP_47 \def (CHead c2 TMP_46 v) in (let TMP_48 \def (Bind b0) in (let 
TMP_49 \def (CHead d2 TMP_48 t) in (getl O TMP_47 TMP_49)))))) in (ex C 
TMP_50))) in (let TMP_57 \def (\lambda (b1: B).(let TMP_56 \def (\lambda (d2: 
C).(let TMP_52 \def (Bind b) in (let TMP_53 \def (CHead c2 TMP_52 v) in (let 
TMP_54 \def (Bind b1) in (let TMP_55 \def (CHead d2 TMP_54 v) in (getl O 
TMP_53 TMP_55)))))) in (ex C TMP_56))) in (let TMP_62 \def (\lambda (d2: 
C).(let TMP_58 \def (Bind b) in (let TMP_59 \def (CHead c2 TMP_58 v) in (let 
TMP_60 \def (Bind b) in (let TMP_61 \def (CHead d2 TMP_60 v) in (getl O 
TMP_59 TMP_61)))))) in (let TMP_63 \def (getl_refl b c2 v) in (let TMP_64 
\def (ex_intro C TMP_62 c2 TMP_63) in (let TMP_65 \def (eq_ind_r B b TMP_57 
TMP_64 b0 H5) in (eq_ind_r T v TMP_51 TMP_65 w H4))))))))) in (let TMP_67 
\def (TMP_66 H3) in (TMP_67 H2)))))))))))))))))))))))))))))))))))))))))))))) 
in (let TMP_96 \def (\lambda (h0: nat).(\lambda (_: (((getl h0 (CHead c1 
(Bind b) v) (CHead d1 (Bind b0) w)) \to (ex C (\lambda (d2: C).(getl h0 
(CHead c2 (Bind b) v) (CHead d2 (Bind b0) w))))))).(\lambda (H1: (getl (S h0) 
(CHead c1 (Bind b) v) (CHead d1 (Bind b0) w))).(let TMP_69 \def (Bind b) in 
(let TMP_70 \def (r TMP_69 h0) in (let TMP_71 \def (Bind b) in (let TMP_72 
\def (Bind b0) in (let TMP_73 \def (CHead d1 TMP_72 w) in (let TMP_74 \def 
(getl_gen_S TMP_71 c1 TMP_73 v h0 H1) in (let H_x \def (H b0 d1 w TMP_70 
TMP_74) in (let H2 \def H_x in (let TMP_77 \def (\lambda (d2: C).(let TMP_75 
\def (Bind b0) in (let TMP_76 \def (CHead d2 TMP_75 w) in (getl h0 c2 
TMP_76)))) in (let TMP_83 \def (\lambda (d2: C).(let TMP_78 \def (S h0) in 
(let TMP_79 \def (Bind b) in (let TMP_80 \def (CHead c2 TMP_79 v) in (let 
TMP_81 \def (Bind b0) in (let TMP_82 \def (CHead d2 TMP_81 w) in (getl TMP_78 
TMP_80 TMP_82))))))) in (let TMP_84 \def (ex C TMP_83) in (let TMP_95 \def 
(\lambda (x: C).(\lambda (H3: (getl h0 c2 (CHead x (Bind b0) w))).(let TMP_90 
\def (\lambda (d2: C).(let TMP_85 \def (S h0) in (let TMP_86 \def (Bind b) in 
(let TMP_87 \def (CHead c2 TMP_86 v) in (let TMP_88 \def (Bind b0) in (let 
TMP_89 \def (CHead d2 TMP_88 w) in (getl TMP_85 TMP_87 TMP_89))))))) in (let 
TMP_91 \def (Bind b) in (let TMP_92 \def (Bind b0) in (let TMP_93 \def (CHead 
x TMP_92 w) in (let TMP_94 \def (getl_head TMP_91 h0 c2 TMP_93 H3 v) in 
(ex_intro C TMP_90 x TMP_94)))))))) in (ex_ind C TMP_77 TMP_84 TMP_95 
H2)))))))))))))))) in (nat_ind TMP_6 TMP_68 TMP_96 h H0))))))))))))).

theorem cimp_getl_conf:
 \forall (c1: C).(\forall (c2: C).((cimp c1 c2) \to (\forall (b: B).(\forall 
(d1: C).(\forall (w: T).(\forall (i: nat).((getl i c1 (CHead d1 (Bind b) w)) 
\to (ex2 C (\lambda (d2: C).(cimp d1 d2)) (\lambda (d2: C).(getl i c2 (CHead 
d2 (Bind b) w)))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: ((\forall (b: B).(\forall (d1: 
C).(\forall (w: T).(\forall (h: nat).((getl h c1 (CHead d1 (Bind b) w)) \to 
(ex C (\lambda (d2: C).(getl h c2 (CHead d2 (Bind b) w))))))))))).(\lambda 
(b: B).(\lambda (d1: C).(\lambda (w: T).(\lambda (i: nat).(\lambda (H0: (getl 
i c1 (CHead d1 (Bind b) w))).(let H_x \def (H b d1 w i H0) in (let H1 \def 
H_x in (let TMP_3 \def (\lambda (d2: C).(let TMP_1 \def (Bind b) in (let 
TMP_2 \def (CHead d2 TMP_1 w) in (getl i c2 TMP_2)))) in (let TMP_7 \def 
(\lambda (d2: C).(\forall (b0: B).(\forall (d3: C).(\forall (w0: T).(\forall 
(h: nat).((getl h d1 (CHead d3 (Bind b0) w0)) \to (let TMP_6 \def (\lambda 
(d4: C).(let TMP_4 \def (Bind b0) in (let TMP_5 \def (CHead d4 TMP_4 w0) in 
(getl h d2 TMP_5)))) in (ex C TMP_6)))))))) in (let TMP_10 \def (\lambda (d2: 
C).(let TMP_8 \def (Bind b) in (let TMP_9 \def (CHead d2 TMP_8 w) in (getl i 
c2 TMP_9)))) in (let TMP_11 \def (ex2 C TMP_7 TMP_10) in (let TMP_82 \def 
(\lambda (x: C).(\lambda (H2: (getl i c2 (CHead x (Bind b) w))).(let TMP_15 
\def (\lambda (d2: C).(\forall (b0: B).(\forall (d3: C).(\forall (w0: 
T).(\forall (h: nat).((getl h d1 (CHead d3 (Bind b0) w0)) \to (let TMP_14 
\def (\lambda (d4: C).(let TMP_12 \def (Bind b0) in (let TMP_13 \def (CHead 
d4 TMP_12 w0) in (getl h d2 TMP_13)))) in (ex C TMP_14)))))))) in (let TMP_18 
\def (\lambda (d2: C).(let TMP_16 \def (Bind b) in (let TMP_17 \def (CHead d2 
TMP_16 w) in (getl i c2 TMP_17)))) in (let TMP_81 \def (\lambda (b0: 
B).(\lambda (d0: C).(\lambda (w0: T).(\lambda (h: nat).(\lambda (H3: (getl h 
d1 (CHead d0 (Bind b0) w0))).(let TMP_19 \def (S h) in (let TMP_20 \def (Bind 
b) in (let TMP_21 \def (CHead d1 TMP_20 w) in (let H_y \def (getl_trans 
TMP_19 c1 TMP_21 i H0) in (let TMP_22 \def (S h) in (let TMP_23 \def (plus 
TMP_22 i) in (let TMP_24 \def (Bind b0) in (let TMP_25 \def (CHead d0 TMP_24 
w0) in (let TMP_26 \def (Bind b) in (let TMP_27 \def (Bind b0) in (let TMP_28 
\def (CHead d0 TMP_27 w0) in (let TMP_29 \def (getl_head TMP_26 h d1 TMP_28 
H3 w) in (let TMP_30 \def (H_y TMP_25 TMP_29) in (let H_x0 \def (H b0 d0 w0 
TMP_23 TMP_30) in (let H4 \def H_x0 in (let TMP_35 \def (\lambda (d2: C).(let 
TMP_31 \def (plus h i) in (let TMP_32 \def (S TMP_31) in (let TMP_33 \def 
(Bind b0) in (let TMP_34 \def (CHead d2 TMP_33 w0) in (getl TMP_32 c2 
TMP_34)))))) in (let TMP_38 \def (\lambda (d2: C).(let TMP_36 \def (Bind b0) 
in (let TMP_37 \def (CHead d2 TMP_36 w0) in (getl h x TMP_37)))) in (let 
TMP_39 \def (ex C TMP_38) in (let TMP_80 \def (\lambda (x0: C).(\lambda (H5: 
(getl (S (plus h i)) c2 (CHead x0 (Bind b0) w0))).(let TMP_40 \def (plus h i) 
in (let TMP_41 \def (S TMP_40) in (let TMP_42 \def (Bind b0) in (let TMP_43 
\def (CHead x0 TMP_42 w0) in (let TMP_44 \def (Bind b) in (let TMP_45 \def 
(CHead x TMP_44 w) in (let H_y0 \def (getl_conf_le TMP_41 TMP_43 c2 H5 TMP_45 
i H2) in (let TMP_46 \def (S h) in (let TMP_47 \def (plus TMP_46 i) in (let 
H6 \def (refl_equal nat TMP_47) in (let TMP_48 \def (plus h i) in (let TMP_49 
\def (S TMP_48) in (let TMP_55 \def (\lambda (n: nat).(let TMP_50 \def (minus 
n i) in (let TMP_51 \def (Bind b) in (let TMP_52 \def (CHead x TMP_51 w) in 
(let TMP_53 \def (Bind b0) in (let TMP_54 \def (CHead x0 TMP_53 w0) in (getl 
TMP_50 TMP_52 TMP_54))))))) in (let TMP_56 \def (plus h i) in (let TMP_57 
\def (le_plus_r h i) in (let TMP_58 \def (le_S i TMP_56 TMP_57) in (let 
TMP_59 \def (H_y0 TMP_58) in (let TMP_60 \def (S h) in (let TMP_61 \def (plus 
TMP_60 i) in (let H7 \def (eq_ind nat TMP_49 TMP_55 TMP_59 TMP_61 H6) in (let 
TMP_62 \def (S h) in (let TMP_63 \def (plus TMP_62 i) in (let TMP_64 \def 
(minus TMP_63 i) in (let TMP_69 \def (\lambda (n: nat).(let TMP_65 \def (Bind 
b) in (let TMP_66 \def (CHead x TMP_65 w) in (let TMP_67 \def (Bind b0) in 
(let TMP_68 \def (CHead x0 TMP_67 w0) in (getl n TMP_66 TMP_68)))))) in (let 
TMP_70 \def (S h) in (let TMP_71 \def (S h) in (let TMP_72 \def (minus_plus_r 
TMP_71 i) in (let H8 \def (eq_ind nat TMP_64 TMP_69 H7 TMP_70 TMP_72) in (let 
TMP_75 \def (\lambda (d2: C).(let TMP_73 \def (Bind b0) in (let TMP_74 \def 
(CHead d2 TMP_73 w0) in (getl h x TMP_74)))) in (let TMP_76 \def (Bind b) in 
(let TMP_77 \def (Bind b0) in (let TMP_78 \def (CHead x0 TMP_77 w0) in (let 
TMP_79 \def (getl_gen_S TMP_76 x TMP_78 w h H8) in (ex_intro C TMP_75 x0 
TMP_79)))))))))))))))))))))))))))))))))))) in (ex_ind C TMP_35 TMP_39 TMP_80 
H4))))))))))))))))))))))))) in (ex_intro2 C TMP_15 TMP_18 x TMP_81 H2)))))) 
in (ex_ind C TMP_3 TMP_11 TMP_82 H1))))))))))))))).

