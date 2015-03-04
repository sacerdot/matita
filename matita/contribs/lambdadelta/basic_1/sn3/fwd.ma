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

include "basic_1/sn3/defs.ma".

include "basic_1/pr3/props.ma".

let rec sn3_ind (c: C) (P: (T \to Prop)) (f: (\forall (t1: T).(((\forall (t2: 
T).((((eq T t1 t2) \to (\forall (P0: Prop).P0))) \to ((pr3 c t1 t2) \to (sn3 
c t2))))) \to (((\forall (t2: T).((((eq T t1 t2) \to (\forall (P0: 
Prop).P0))) \to ((pr3 c t1 t2) \to (P t2))))) \to (P t1))))) (t: T) (s0: sn3 
c t) on s0: P t \def match s0 with [(sn3_sing t1 s1) \Rightarrow (let TMP_2 
\def (\lambda (t2: T).(\lambda (p: (((eq T t1 t2) \to (\forall (P0: 
Prop).P0)))).(\lambda (p0: (pr3 c t1 t2)).(let TMP_1 \def (s1 t2 p p0) in 
((sn3_ind c P f) t2 TMP_1))))) in (f t1 s1 TMP_2))].

theorem sn3_gen_bind:
 \forall (b: B).(\forall (c: C).(\forall (u: T).(\forall (t: T).((sn3 c 
(THead (Bind b) u t)) \to (land (sn3 c u) (sn3 (CHead c (Bind b) u) t))))))
\def
 \lambda (b: B).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: 
(sn3 c (THead (Bind b) u t))).(let TMP_1 \def (Bind b) in (let TMP_2 \def 
(THead TMP_1 u t) in (let TMP_3 \def (\lambda (t0: T).(sn3 c t0)) in (let 
TMP_8 \def (\lambda (_: T).(let TMP_4 \def (sn3 c u) in (let TMP_5 \def (Bind 
b) in (let TMP_6 \def (CHead c TMP_5 u) in (let TMP_7 \def (sn3 TMP_6 t) in 
(land TMP_4 TMP_7)))))) in (let TMP_99 \def (\lambda (y: T).(\lambda (H0: 
(sn3 c y)).(let TMP_13 \def (\lambda (t0: T).((eq T y (THead (Bind b) u t0)) 
\to (let TMP_9 \def (sn3 c u) in (let TMP_10 \def (Bind b) in (let TMP_11 
\def (CHead c TMP_10 u) in (let TMP_12 \def (sn3 TMP_11 t0) in (land TMP_9 
TMP_12))))))) in (let TMP_18 \def (\lambda (t0: T).(\forall (x: T).((eq T y 
(THead (Bind b) t0 x)) \to (let TMP_14 \def (sn3 c t0) in (let TMP_15 \def 
(Bind b) in (let TMP_16 \def (CHead c TMP_15 t0) in (let TMP_17 \def (sn3 
TMP_16 x) in (land TMP_14 TMP_17)))))))) in (let TMP_23 \def (\lambda (t0: 
T).(\forall (x: T).(\forall (x0: T).((eq T t0 (THead (Bind b) x x0)) \to (let 
TMP_19 \def (sn3 c x) in (let TMP_20 \def (Bind b) in (let TMP_21 \def (CHead 
c TMP_20 x) in (let TMP_22 \def (sn3 TMP_21 x0) in (land TMP_19 
TMP_22))))))))) in (let TMP_96 \def (\lambda (t1: T).(\lambda (H1: ((\forall 
(t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to 
(sn3 c t2)))))).(\lambda (H2: ((\forall (t2: T).((((eq T t1 t2) \to (\forall 
(P: Prop).P))) \to ((pr3 c t1 t2) \to (\forall (x: T).(\forall (x0: T).((eq T 
t2 (THead (Bind b) x x0)) \to (land (sn3 c x) (sn3 (CHead c (Bind b) x) 
x0)))))))))).(\lambda (x: T).(\lambda (x0: T).(\lambda (H3: (eq T t1 (THead 
(Bind b) x x0))).(let TMP_28 \def (\lambda (t0: T).(\forall (t2: T).((((eq T 
t0 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t0 t2) \to (\forall (x1: 
T).(\forall (x2: T).((eq T t2 (THead (Bind b) x1 x2)) \to (let TMP_24 \def 
(sn3 c x1) in (let TMP_25 \def (Bind b) in (let TMP_26 \def (CHead c TMP_25 
x1) in (let TMP_27 \def (sn3 TMP_26 x2) in (land TMP_24 TMP_27)))))))))))) in 
(let TMP_29 \def (Bind b) in (let TMP_30 \def (THead TMP_29 x x0) in (let H4 
\def (eq_ind T t1 TMP_28 H2 TMP_30 H3) in (let TMP_31 \def (\lambda (t0: 
T).(\forall (t2: T).((((eq T t0 t2) \to (\forall (P: Prop).P))) \to ((pr3 c 
t0 t2) \to (sn3 c t2))))) in (let TMP_32 \def (Bind b) in (let TMP_33 \def 
(THead TMP_32 x x0) in (let H5 \def (eq_ind T t1 TMP_31 H1 TMP_33 H3) in (let 
TMP_34 \def (sn3 c x) in (let TMP_35 \def (Bind b) in (let TMP_36 \def (CHead 
c TMP_35 x) in (let TMP_37 \def (sn3 TMP_36 x0) in (let TMP_63 \def (\lambda 
(t2: T).(\lambda (H6: (((eq T x t2) \to (\forall (P: Prop).P)))).(\lambda 
(H7: (pr3 c x t2)).(let TMP_38 \def (Bind b) in (let TMP_39 \def (THead 
TMP_38 t2 x0) in (let TMP_48 \def (\lambda (H8: (eq T (THead (Bind b) x x0) 
(THead (Bind b) t2 x0))).(\lambda (P: Prop).(let TMP_40 \def (\lambda (e: 
T).(match e with [(TSort _) \Rightarrow x | (TLRef _) \Rightarrow x | (THead 
_ t0 _) \Rightarrow t0])) in (let TMP_41 \def (Bind b) in (let TMP_42 \def 
(THead TMP_41 x x0) in (let TMP_43 \def (Bind b) in (let TMP_44 \def (THead 
TMP_43 t2 x0) in (let H9 \def (f_equal T T TMP_40 TMP_42 TMP_44 H8) in (let 
TMP_45 \def (\lambda (t0: T).(pr3 c x t0)) in (let H10 \def (eq_ind_r T t2 
TMP_45 H7 x H9) in (let TMP_46 \def (\lambda (t0: T).((eq T x t0) \to 
(\forall (P0: Prop).P0))) in (let H11 \def (eq_ind_r T t2 TMP_46 H6 x H9) in 
(let TMP_47 \def (refl_equal T x) in (H11 TMP_47 P)))))))))))))) in (let 
TMP_49 \def (Bind b) in (let TMP_50 \def (Bind b) in (let TMP_51 \def (CHead 
c TMP_50 t2) in (let TMP_52 \def (pr3_refl TMP_51 x0) in (let TMP_53 \def 
(pr3_head_12 c x t2 H7 TMP_49 x0 x0 TMP_52) in (let TMP_54 \def (Bind b) in 
(let TMP_55 \def (THead TMP_54 t2 x0) in (let TMP_56 \def (refl_equal T 
TMP_55) in (let H8 \def (H4 TMP_39 TMP_48 TMP_53 t2 x0 TMP_56) in (let TMP_57 
\def (sn3 c t2) in (let TMP_58 \def (Bind b) in (let TMP_59 \def (CHead c 
TMP_58 t2) in (let TMP_60 \def (sn3 TMP_59 x0) in (let TMP_61 \def (sn3 c t2) 
in (let TMP_62 \def (\lambda (H9: (sn3 c t2)).(\lambda (_: (sn3 (CHead c 
(Bind b) t2) x0)).H9)) in (land_ind TMP_57 TMP_60 TMP_61 TMP_62 
H8)))))))))))))))))))))) in (let TMP_64 \def (sn3_sing c x TMP_63) in (let 
TMP_65 \def (Bind b) in (let TMP_66 \def (CHead c TMP_65 x) in (let TMP_94 
\def (\lambda (t2: T).(\lambda (H6: (((eq T x0 t2) \to (\forall (P: 
Prop).P)))).(\lambda (H7: (pr3 (CHead c (Bind b) x) x0 t2)).(let TMP_67 \def 
(Bind b) in (let TMP_68 \def (THead TMP_67 x t2) in (let TMP_79 \def (\lambda 
(H8: (eq T (THead (Bind b) x x0) (THead (Bind b) x t2))).(\lambda (P: 
Prop).(let TMP_69 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow 
x0 | (TLRef _) \Rightarrow x0 | (THead _ _ t0) \Rightarrow t0])) in (let 
TMP_70 \def (Bind b) in (let TMP_71 \def (THead TMP_70 x x0) in (let TMP_72 
\def (Bind b) in (let TMP_73 \def (THead TMP_72 x t2) in (let H9 \def 
(f_equal T T TMP_69 TMP_71 TMP_73 H8) in (let TMP_76 \def (\lambda (t0: 
T).(let TMP_74 \def (Bind b) in (let TMP_75 \def (CHead c TMP_74 x) in (pr3 
TMP_75 x0 t0)))) in (let H10 \def (eq_ind_r T t2 TMP_76 H7 x0 H9) in (let 
TMP_77 \def (\lambda (t0: T).((eq T x0 t0) \to (\forall (P0: Prop).P0))) in 
(let H11 \def (eq_ind_r T t2 TMP_77 H6 x0 H9) in (let TMP_78 \def (refl_equal 
T x0) in (H11 TMP_78 P)))))))))))))) in (let TMP_80 \def (pr3_refl c x) in 
(let TMP_81 \def (Bind b) in (let TMP_82 \def (pr3_head_12 c x x TMP_80 
TMP_81 x0 t2 H7) in (let TMP_83 \def (Bind b) in (let TMP_84 \def (THead 
TMP_83 x t2) in (let TMP_85 \def (refl_equal T TMP_84) in (let H8 \def (H4 
TMP_68 TMP_79 TMP_82 x t2 TMP_85) in (let TMP_86 \def (sn3 c x) in (let 
TMP_87 \def (Bind b) in (let TMP_88 \def (CHead c TMP_87 x) in (let TMP_89 
\def (sn3 TMP_88 t2) in (let TMP_90 \def (Bind b) in (let TMP_91 \def (CHead 
c TMP_90 x) in (let TMP_92 \def (sn3 TMP_91 t2) in (let TMP_93 \def (\lambda 
(_: (sn3 c x)).(\lambda (H10: (sn3 (CHead c (Bind b) x) t2)).H10)) in 
(land_ind TMP_86 TMP_89 TMP_92 TMP_93 H8)))))))))))))))))))))) in (let TMP_95 
\def (sn3_sing TMP_66 x0 TMP_94) in (conj TMP_34 TMP_37 TMP_64 
TMP_95))))))))))))))))))))))))) in (let TMP_97 \def (sn3_ind c TMP_23 TMP_96 
y H0) in (let TMP_98 \def (unintro T u TMP_18 TMP_97) in (unintro T t TMP_13 
TMP_98))))))))) in (insert_eq T TMP_2 TMP_3 TMP_8 TMP_99 H)))))))))).

theorem sn3_gen_flat:
 \forall (f: F).(\forall (c: C).(\forall (u: T).(\forall (t: T).((sn3 c 
(THead (Flat f) u t)) \to (land (sn3 c u) (sn3 c t))))))
\def
 \lambda (f: F).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: 
(sn3 c (THead (Flat f) u t))).(let TMP_1 \def (Flat f) in (let TMP_2 \def 
(THead TMP_1 u t) in (let TMP_3 \def (\lambda (t0: T).(sn3 c t0)) in (let 
TMP_6 \def (\lambda (_: T).(let TMP_4 \def (sn3 c u) in (let TMP_5 \def (sn3 
c t) in (land TMP_4 TMP_5)))) in (let TMP_75 \def (\lambda (y: T).(\lambda 
(H0: (sn3 c y)).(let TMP_9 \def (\lambda (t0: T).((eq T y (THead (Flat f) u 
t0)) \to (let TMP_7 \def (sn3 c u) in (let TMP_8 \def (sn3 c t0) in (land 
TMP_7 TMP_8))))) in (let TMP_12 \def (\lambda (t0: T).(\forall (x: T).((eq T 
y (THead (Flat f) t0 x)) \to (let TMP_10 \def (sn3 c t0) in (let TMP_11 \def 
(sn3 c x) in (land TMP_10 TMP_11)))))) in (let TMP_15 \def (\lambda (t0: 
T).(\forall (x: T).(\forall (x0: T).((eq T t0 (THead (Flat f) x x0)) \to (let 
TMP_13 \def (sn3 c x) in (let TMP_14 \def (sn3 c x0) in (land TMP_13 
TMP_14))))))) in (let TMP_72 \def (\lambda (t1: T).(\lambda (H1: ((\forall 
(t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to 
(sn3 c t2)))))).(\lambda (H2: ((\forall (t2: T).((((eq T t1 t2) \to (\forall 
(P: Prop).P))) \to ((pr3 c t1 t2) \to (\forall (x: T).(\forall (x0: T).((eq T 
t2 (THead (Flat f) x x0)) \to (land (sn3 c x) (sn3 c x0)))))))))).(\lambda 
(x: T).(\lambda (x0: T).(\lambda (H3: (eq T t1 (THead (Flat f) x x0))).(let 
TMP_18 \def (\lambda (t0: T).(\forall (t2: T).((((eq T t0 t2) \to (\forall 
(P: Prop).P))) \to ((pr3 c t0 t2) \to (\forall (x1: T).(\forall (x2: T).((eq 
T t2 (THead (Flat f) x1 x2)) \to (let TMP_16 \def (sn3 c x1) in (let TMP_17 
\def (sn3 c x2) in (land TMP_16 TMP_17)))))))))) in (let TMP_19 \def (Flat f) 
in (let TMP_20 \def (THead TMP_19 x x0) in (let H4 \def (eq_ind T t1 TMP_18 
H2 TMP_20 H3) in (let TMP_21 \def (\lambda (t0: T).(\forall (t2: T).((((eq T 
t0 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t0 t2) \to (sn3 c t2))))) in 
(let TMP_22 \def (Flat f) in (let TMP_23 \def (THead TMP_22 x x0) in (let H5 
\def (eq_ind T t1 TMP_21 H1 TMP_23 H3) in (let TMP_24 \def (sn3 c x) in (let 
TMP_25 \def (sn3 c x0) in (let TMP_49 \def (\lambda (t2: T).(\lambda (H6: 
(((eq T x t2) \to (\forall (P: Prop).P)))).(\lambda (H7: (pr3 c x t2)).(let 
TMP_26 \def (Flat f) in (let TMP_27 \def (THead TMP_26 t2 x0) in (let TMP_36 
\def (\lambda (H8: (eq T (THead (Flat f) x x0) (THead (Flat f) t2 
x0))).(\lambda (P: Prop).(let TMP_28 \def (\lambda (e: T).(match e with 
[(TSort _) \Rightarrow x | (TLRef _) \Rightarrow x | (THead _ t0 _) 
\Rightarrow t0])) in (let TMP_29 \def (Flat f) in (let TMP_30 \def (THead 
TMP_29 x x0) in (let TMP_31 \def (Flat f) in (let TMP_32 \def (THead TMP_31 
t2 x0) in (let H9 \def (f_equal T T TMP_28 TMP_30 TMP_32 H8) in (let TMP_33 
\def (\lambda (t0: T).(pr3 c x t0)) in (let H10 \def (eq_ind_r T t2 TMP_33 H7 
x H9) in (let TMP_34 \def (\lambda (t0: T).((eq T x t0) \to (\forall (P0: 
Prop).P0))) in (let H11 \def (eq_ind_r T t2 TMP_34 H6 x H9) in (let TMP_35 
\def (refl_equal T x) in (H11 TMP_35 P)))))))))))))) in (let TMP_37 \def 
(Flat f) in (let TMP_38 \def (Flat f) in (let TMP_39 \def (CHead c TMP_38 t2) 
in (let TMP_40 \def (pr3_refl TMP_39 x0) in (let TMP_41 \def (pr3_head_12 c x 
t2 H7 TMP_37 x0 x0 TMP_40) in (let TMP_42 \def (Flat f) in (let TMP_43 \def 
(THead TMP_42 t2 x0) in (let TMP_44 \def (refl_equal T TMP_43) in (let H8 
\def (H4 TMP_27 TMP_36 TMP_41 t2 x0 TMP_44) in (let TMP_45 \def (sn3 c t2) in 
(let TMP_46 \def (sn3 c x0) in (let TMP_47 \def (sn3 c t2) in (let TMP_48 
\def (\lambda (H9: (sn3 c t2)).(\lambda (_: (sn3 c x0)).H9)) in (land_ind 
TMP_45 TMP_46 TMP_47 TMP_48 H8)))))))))))))))))))) in (let TMP_50 \def 
(sn3_sing c x TMP_49) in (let TMP_70 \def (\lambda (t2: T).(\lambda (H6: 
(((eq T x0 t2) \to (\forall (P: Prop).P)))).(\lambda (H7: (pr3 c x0 t2)).(let 
TMP_51 \def (Flat f) in (let TMP_52 \def (THead TMP_51 x t2) in (let TMP_61 
\def (\lambda (H8: (eq T (THead (Flat f) x x0) (THead (Flat f) x 
t2))).(\lambda (P: Prop).(let TMP_53 \def (\lambda (e: T).(match e with 
[(TSort _) \Rightarrow x0 | (TLRef _) \Rightarrow x0 | (THead _ _ t0) 
\Rightarrow t0])) in (let TMP_54 \def (Flat f) in (let TMP_55 \def (THead 
TMP_54 x x0) in (let TMP_56 \def (Flat f) in (let TMP_57 \def (THead TMP_56 x 
t2) in (let H9 \def (f_equal T T TMP_53 TMP_55 TMP_57 H8) in (let TMP_58 \def 
(\lambda (t0: T).(pr3 c x0 t0)) in (let H10 \def (eq_ind_r T t2 TMP_58 H7 x0 
H9) in (let TMP_59 \def (\lambda (t0: T).((eq T x0 t0) \to (\forall (P0: 
Prop).P0))) in (let H11 \def (eq_ind_r T t2 TMP_59 H6 x0 H9) in (let TMP_60 
\def (refl_equal T x0) in (H11 TMP_60 P)))))))))))))) in (let TMP_62 \def 
(pr3_thin_dx c x0 t2 H7 x f) in (let TMP_63 \def (Flat f) in (let TMP_64 \def 
(THead TMP_63 x t2) in (let TMP_65 \def (refl_equal T TMP_64) in (let H8 \def 
(H4 TMP_52 TMP_61 TMP_62 x t2 TMP_65) in (let TMP_66 \def (sn3 c x) in (let 
TMP_67 \def (sn3 c t2) in (let TMP_68 \def (sn3 c t2) in (let TMP_69 \def 
(\lambda (_: (sn3 c x)).(\lambda (H10: (sn3 c t2)).H10)) in (land_ind TMP_66 
TMP_67 TMP_68 TMP_69 H8)))))))))))))))) in (let TMP_71 \def (sn3_sing c x0 
TMP_70) in (conj TMP_24 TMP_25 TMP_50 TMP_71))))))))))))))))))))) in (let 
TMP_73 \def (sn3_ind c TMP_15 TMP_72 y H0) in (let TMP_74 \def (unintro T u 
TMP_12 TMP_73) in (unintro T t TMP_9 TMP_74))))))))) in (insert_eq T TMP_2 
TMP_3 TMP_6 TMP_75 H)))))))))).

theorem sn3_gen_head:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).((sn3 c 
(THead k u t)) \to (sn3 c u)))))
\def
 \lambda (k: K).(let TMP_1 \def (\lambda (k0: K).(\forall (c: C).(\forall (u: 
T).(\forall (t: T).((sn3 c (THead k0 u t)) \to (sn3 c u)))))) in (let TMP_8 
\def (\lambda (b: B).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda 
(H: (sn3 c (THead (Bind b) u t))).(let H_x \def (sn3_gen_bind b c u t H) in 
(let H0 \def H_x in (let TMP_2 \def (sn3 c u) in (let TMP_3 \def (Bind b) in 
(let TMP_4 \def (CHead c TMP_3 u) in (let TMP_5 \def (sn3 TMP_4 t) in (let 
TMP_6 \def (sn3 c u) in (let TMP_7 \def (\lambda (H1: (sn3 c u)).(\lambda (_: 
(sn3 (CHead c (Bind b) u) t)).H1)) in (land_ind TMP_2 TMP_5 TMP_6 TMP_7 
H0)))))))))))))) in (let TMP_13 \def (\lambda (f: F).(\lambda (c: C).(\lambda 
(u: T).(\lambda (t: T).(\lambda (H: (sn3 c (THead (Flat f) u t))).(let H_x 
\def (sn3_gen_flat f c u t H) in (let H0 \def H_x in (let TMP_9 \def (sn3 c 
u) in (let TMP_10 \def (sn3 c t) in (let TMP_11 \def (sn3 c u) in (let TMP_12 
\def (\lambda (H1: (sn3 c u)).(\lambda (_: (sn3 c t)).H1)) in (land_ind TMP_9 
TMP_10 TMP_11 TMP_12 H0)))))))))))) in (K_ind TMP_1 TMP_8 TMP_13 k)))).

theorem sn3_gen_cflat:
 \forall (f: F).(\forall (c: C).(\forall (u: T).(\forall (t: T).((sn3 (CHead 
c (Flat f) u) t) \to (sn3 c t)))))
\def
 \lambda (f: F).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (H: 
(sn3 (CHead c (Flat f) u) t)).(let TMP_1 \def (Flat f) in (let TMP_2 \def 
(CHead c TMP_1 u) in (let TMP_3 \def (\lambda (t0: T).(sn3 c t0)) in (let 
TMP_6 \def (\lambda (t1: T).(\lambda (_: ((\forall (t2: T).((((eq T t1 t2) 
\to (\forall (P: Prop).P))) \to ((pr3 (CHead c (Flat f) u) t1 t2) \to (sn3 
(CHead c (Flat f) u) t2)))))).(\lambda (H1: ((\forall (t2: T).((((eq T t1 t2) 
\to (\forall (P: Prop).P))) \to ((pr3 (CHead c (Flat f) u) t1 t2) \to (sn3 c 
t2)))))).(let TMP_5 \def (\lambda (t2: T).(\lambda (H2: (((eq T t1 t2) \to 
(\forall (P: Prop).P)))).(\lambda (H3: (pr3 c t1 t2)).(let TMP_4 \def 
(pr3_cflat c t1 t2 H3 f u) in (H1 t2 H2 TMP_4))))) in (sn3_sing c t1 
TMP_5))))) in (sn3_ind TMP_2 TMP_3 TMP_6 t H))))))))).

theorem sn3_gen_lift:
 \forall (c1: C).(\forall (t: T).(\forall (h: nat).(\forall (d: nat).((sn3 c1 
(lift h d t)) \to (\forall (c2: C).((drop h d c1 c2) \to (sn3 c2 t)))))))
\def
 \lambda (c1: C).(\lambda (t: T).(\lambda (h: nat).(\lambda (d: nat).(\lambda 
(H: (sn3 c1 (lift h d t))).(let TMP_1 \def (lift h d t) in (let TMP_2 \def 
(\lambda (t0: T).(sn3 c1 t0)) in (let TMP_3 \def (\lambda (_: T).(\forall 
(c2: C).((drop h d c1 c2) \to (sn3 c2 t)))) in (let TMP_23 \def (\lambda (y: 
T).(\lambda (H0: (sn3 c1 y)).(let TMP_4 \def (\lambda (t0: T).((eq T y (lift 
h d t0)) \to (\forall (c2: C).((drop h d c1 c2) \to (sn3 c2 t0))))) in (let 
TMP_5 \def (\lambda (t0: T).(\forall (x: T).((eq T t0 (lift h d x)) \to 
(\forall (c2: C).((drop h d c1 c2) \to (sn3 c2 x)))))) in (let TMP_21 \def 
(\lambda (t1: T).(\lambda (H1: ((\forall (t2: T).((((eq T t1 t2) \to (\forall 
(P: Prop).P))) \to ((pr3 c1 t1 t2) \to (sn3 c1 t2)))))).(\lambda (H2: 
((\forall (t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c1 t1 
t2) \to (\forall (x: T).((eq T t2 (lift h d x)) \to (\forall (c2: C).((drop h 
d c1 c2) \to (sn3 c2 x)))))))))).(\lambda (x: T).(\lambda (H3: (eq T t1 (lift 
h d x))).(\lambda (c2: C).(\lambda (H4: (drop h d c1 c2)).(let TMP_6 \def 
(\lambda (t0: T).(\forall (t2: T).((((eq T t0 t2) \to (\forall (P: Prop).P))) 
\to ((pr3 c1 t0 t2) \to (\forall (x0: T).((eq T t2 (lift h d x0)) \to 
(\forall (c3: C).((drop h d c1 c3) \to (sn3 c3 x0))))))))) in (let TMP_7 \def 
(lift h d x) in (let H5 \def (eq_ind T t1 TMP_6 H2 TMP_7 H3) in (let TMP_8 
\def (\lambda (t0: T).(\forall (t2: T).((((eq T t0 t2) \to (\forall (P: 
Prop).P))) \to ((pr3 c1 t0 t2) \to (sn3 c1 t2))))) in (let TMP_9 \def (lift h 
d x) in (let H6 \def (eq_ind T t1 TMP_8 H1 TMP_9 H3) in (let TMP_20 \def 
(\lambda (t2: T).(\lambda (H7: (((eq T x t2) \to (\forall (P: 
Prop).P)))).(\lambda (H8: (pr3 c2 x t2)).(let TMP_10 \def (lift h d t2) in 
(let TMP_16 \def (\lambda (H9: (eq T (lift h d x) (lift h d t2))).(\lambda 
(P: Prop).(let TMP_11 \def (\lambda (t0: T).(pr3 c2 x t0)) in (let TMP_12 
\def (lift_inj x t2 h d H9) in (let H10 \def (eq_ind_r T t2 TMP_11 H8 x 
TMP_12) in (let TMP_13 \def (\lambda (t0: T).((eq T x t0) \to (\forall (P0: 
Prop).P0))) in (let TMP_14 \def (lift_inj x t2 h d H9) in (let H11 \def 
(eq_ind_r T t2 TMP_13 H7 x TMP_14) in (let TMP_15 \def (refl_equal T x) in 
(H11 TMP_15 P)))))))))) in (let TMP_17 \def (pr3_lift c1 c2 h d H4 x t2 H8) 
in (let TMP_18 \def (lift h d t2) in (let TMP_19 \def (refl_equal T TMP_18) 
in (H5 TMP_10 TMP_16 TMP_17 t2 TMP_19 c2 H4))))))))) in (sn3_sing c2 x 
TMP_20))))))))))))))) in (let TMP_22 \def (sn3_ind c1 TMP_5 TMP_21 y H0) in 
(unintro T t TMP_4 TMP_22))))))) in (insert_eq T TMP_1 TMP_2 TMP_3 TMP_23 
H))))))))).

