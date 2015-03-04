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

include "basic_1/pr2/fwd.ma".

theorem nf2_sort:
 \forall (c: C).(\forall (n: nat).(nf2 c (TSort n)))
\def
 \lambda (c: C).(\lambda (n: nat).(\lambda (t2: T).(\lambda (H: (pr2 c (TSort 
n) t2)).(let TMP_1 \def (TSort n) in (let TMP_3 \def (\lambda (t: T).(let 
TMP_2 \def (TSort n) in (eq T TMP_2 t))) in (let TMP_4 \def (TSort n) in (let 
TMP_5 \def (refl_equal T TMP_4) in (let TMP_6 \def (pr2_gen_sort c t2 n H) in 
(eq_ind_r T TMP_1 TMP_3 TMP_5 t2 TMP_6))))))))).

theorem nf2_csort_lref:
 \forall (n: nat).(\forall (i: nat).(nf2 (CSort n) (TLRef i)))
\def
 \lambda (n: nat).(\lambda (i: nat).(\lambda (t2: T).(\lambda (H: (pr2 (CSort 
n) (TLRef i) t2)).(let TMP_1 \def (CSort n) in (let H0 \def (pr2_gen_lref 
TMP_1 t2 i H) in (let TMP_2 \def (TLRef i) in (let TMP_3 \def (eq T t2 TMP_2) 
in (let TMP_7 \def (\lambda (d: C).(\lambda (u: T).(let TMP_4 \def (CSort n) 
in (let TMP_5 \def (Bind Abbr) in (let TMP_6 \def (CHead d TMP_5 u) in (getl 
i TMP_4 TMP_6)))))) in (let TMP_10 \def (\lambda (_: C).(\lambda (u: T).(let 
TMP_8 \def (S i) in (let TMP_9 \def (lift TMP_8 O u) in (eq T t2 TMP_9))))) 
in (let TMP_11 \def (ex2_2 C T TMP_7 TMP_10) in (let TMP_12 \def (TLRef i) in 
(let TMP_13 \def (eq T TMP_12 t2) in (let TMP_19 \def (\lambda (H1: (eq T t2 
(TLRef i))).(let TMP_14 \def (TLRef i) in (let TMP_16 \def (\lambda (t: 
T).(let TMP_15 \def (TLRef i) in (eq T TMP_15 t))) in (let TMP_17 \def (TLRef 
i) in (let TMP_18 \def (refl_equal T TMP_17) in (eq_ind_r T TMP_14 TMP_16 
TMP_18 t2 H1)))))) in (let TMP_41 \def (\lambda (H1: (ex2_2 C T (\lambda (d: 
C).(\lambda (u: T).(getl i (CSort n) (CHead d (Bind Abbr) u)))) (\lambda (_: 
C).(\lambda (u: T).(eq T t2 (lift (S i) O u)))))).(let TMP_23 \def (\lambda 
(d: C).(\lambda (u: T).(let TMP_20 \def (CSort n) in (let TMP_21 \def (Bind 
Abbr) in (let TMP_22 \def (CHead d TMP_21 u) in (getl i TMP_20 TMP_22)))))) 
in (let TMP_26 \def (\lambda (_: C).(\lambda (u: T).(let TMP_24 \def (S i) in 
(let TMP_25 \def (lift TMP_24 O u) in (eq T t2 TMP_25))))) in (let TMP_27 
\def (TLRef i) in (let TMP_28 \def (eq T TMP_27 t2) in (let TMP_40 \def 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (H2: (getl i (CSort n) (CHead x0 
(Bind Abbr) x1))).(\lambda (H3: (eq T t2 (lift (S i) O x1))).(let TMP_29 \def 
(S i) in (let TMP_30 \def (lift TMP_29 O x1) in (let TMP_32 \def (\lambda (t: 
T).(let TMP_31 \def (TLRef i) in (eq T TMP_31 t))) in (let TMP_33 \def (Bind 
Abbr) in (let TMP_34 \def (CHead x0 TMP_33 x1) in (let TMP_35 \def (TLRef i) 
in (let TMP_36 \def (S i) in (let TMP_37 \def (lift TMP_36 O x1) in (let 
TMP_38 \def (eq T TMP_35 TMP_37) in (let TMP_39 \def (getl_gen_sort n i 
TMP_34 H2 TMP_38) in (eq_ind_r T TMP_30 TMP_32 TMP_39 t2 H3))))))))))))))) in 
(ex2_2_ind C T TMP_23 TMP_26 TMP_28 TMP_40 H1))))))) in (or_ind TMP_3 TMP_11 
TMP_13 TMP_19 TMP_41 H0))))))))))))))).

theorem nf2_abst:
 \forall (c: C).(\forall (u: T).((nf2 c u) \to (\forall (b: B).(\forall (v: 
T).(\forall (t: T).((nf2 (CHead c (Bind b) v) t) \to (nf2 c (THead (Bind 
Abst) u t))))))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (H: ((\forall (t2: T).((pr2 c u t2) 
\to (eq T u t2))))).(\lambda (b: B).(\lambda (v: T).(\lambda (t: T).(\lambda 
(H0: ((\forall (t2: T).((pr2 (CHead c (Bind b) v) t t2) \to (eq T t 
t2))))).(\lambda (t2: T).(\lambda (H1: (pr2 c (THead (Bind Abst) u t) 
t2)).(let H2 \def (pr2_gen_abst c u t t2 H1) in (let TMP_3 \def (\lambda (u2: 
T).(\lambda (t3: T).(let TMP_1 \def (Bind Abst) in (let TMP_2 \def (THead 
TMP_1 u2 t3) in (eq T t2 TMP_2))))) in (let TMP_4 \def (\lambda (u2: 
T).(\lambda (_: T).(pr2 c u u2))) in (let TMP_7 \def (\lambda (_: T).(\lambda 
(t3: T).(\forall (b0: B).(\forall (u0: T).(let TMP_5 \def (Bind b0) in (let 
TMP_6 \def (CHead c TMP_5 u0) in (pr2 TMP_6 t t3))))))) in (let TMP_8 \def 
(Bind Abst) in (let TMP_9 \def (THead TMP_8 u t) in (let TMP_10 \def (eq T 
TMP_9 t2) in (let TMP_24 \def (\lambda (x0: T).(\lambda (x1: T).(\lambda (H3: 
(eq T t2 (THead (Bind Abst) x0 x1))).(\lambda (H4: (pr2 c u x0)).(\lambda 
(H5: ((\forall (b0: B).(\forall (u0: T).(pr2 (CHead c (Bind b0) u0) t 
x1))))).(let TMP_11 \def (Bind Abst) in (let TMP_12 \def (THead TMP_11 x0 x1) 
in (let TMP_15 \def (\lambda (t0: T).(let TMP_13 \def (Bind Abst) in (let 
TMP_14 \def (THead TMP_13 u t) in (eq T TMP_14 t0)))) in (let TMP_16 \def 
(Bind Abst) in (let TMP_17 \def (Bind Abst) in (let TMP_18 \def (Bind Abst) 
in (let TMP_19 \def (refl_equal K TMP_18) in (let TMP_20 \def (H x0 H4) in 
(let TMP_21 \def (H5 b v) in (let TMP_22 \def (H0 x1 TMP_21) in (let TMP_23 
\def (f_equal3 K T T T THead TMP_16 TMP_17 u x0 t x1 TMP_19 TMP_20 TMP_22) in 
(eq_ind_r T TMP_12 TMP_15 TMP_23 t2 H3))))))))))))))))) in (ex3_2_ind T T 
TMP_3 TMP_4 TMP_7 TMP_10 TMP_24 H2))))))))))))))))).

theorem nf2_abst_shift:
 \forall (c: C).(\forall (u: T).((nf2 c u) \to (\forall (t: T).((nf2 (CHead c 
(Bind Abst) u) t) \to (nf2 c (THead (Bind Abst) u t))))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (H: ((\forall (t2: T).((pr2 c u t2) 
\to (eq T u t2))))).(\lambda (t: T).(\lambda (H0: ((\forall (t2: T).((pr2 
(CHead c (Bind Abst) u) t t2) \to (eq T t t2))))).(\lambda (t2: T).(\lambda 
(H1: (pr2 c (THead (Bind Abst) u t) t2)).(let H2 \def (pr2_gen_abst c u t t2 
H1) in (let TMP_3 \def (\lambda (u2: T).(\lambda (t3: T).(let TMP_1 \def 
(Bind Abst) in (let TMP_2 \def (THead TMP_1 u2 t3) in (eq T t2 TMP_2))))) in 
(let TMP_4 \def (\lambda (u2: T).(\lambda (_: T).(pr2 c u u2))) in (let TMP_7 
\def (\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u0: T).(let 
TMP_5 \def (Bind b) in (let TMP_6 \def (CHead c TMP_5 u0) in (pr2 TMP_6 t 
t3))))))) in (let TMP_8 \def (Bind Abst) in (let TMP_9 \def (THead TMP_8 u t) 
in (let TMP_10 \def (eq T TMP_9 t2) in (let TMP_24 \def (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H3: (eq T t2 (THead (Bind Abst) x0 
x1))).(\lambda (H4: (pr2 c u x0)).(\lambda (H5: ((\forall (b: B).(\forall 
(u0: T).(pr2 (CHead c (Bind b) u0) t x1))))).(let TMP_11 \def (Bind Abst) in 
(let TMP_12 \def (THead TMP_11 x0 x1) in (let TMP_15 \def (\lambda (t0: 
T).(let TMP_13 \def (Bind Abst) in (let TMP_14 \def (THead TMP_13 u t) in (eq 
T TMP_14 t0)))) in (let TMP_16 \def (Bind Abst) in (let TMP_17 \def (Bind 
Abst) in (let TMP_18 \def (Bind Abst) in (let TMP_19 \def (refl_equal K 
TMP_18) in (let TMP_20 \def (H x0 H4) in (let TMP_21 \def (H5 Abst u) in (let 
TMP_22 \def (H0 x1 TMP_21) in (let TMP_23 \def (f_equal3 K T T T THead TMP_16 
TMP_17 u x0 t x1 TMP_19 TMP_20 TMP_22) in (eq_ind_r T TMP_12 TMP_15 TMP_23 t2 
H3))))))))))))))))) in (ex3_2_ind T T TMP_3 TMP_4 TMP_7 TMP_10 TMP_24 
H2))))))))))))))).

theorem nfs2_tapp:
 \forall (c: C).(\forall (t: T).(\forall (ts: TList).((nfs2 c (TApp ts t)) 
\to (land (nfs2 c ts) (nf2 c t)))))
\def
 \lambda (c: C).(\lambda (t: T).(\lambda (ts: TList).(let TMP_3 \def (\lambda 
(t0: TList).((nfs2 c (TApp t0 t)) \to (let TMP_1 \def (nfs2 c t0) in (let 
TMP_2 \def (nf2 c t) in (land TMP_1 TMP_2))))) in (let TMP_9 \def (\lambda 
(H: (land (nf2 c t) True)).(let H0 \def H in (let TMP_4 \def (nf2 c t) in 
(let TMP_5 \def (nf2 c t) in (let TMP_6 \def (land True TMP_5) in (let TMP_8 
\def (\lambda (H1: (nf2 c t)).(\lambda (_: True).(let TMP_7 \def (nf2 c t) in 
(conj True TMP_7 I H1)))) in (land_ind TMP_4 True TMP_6 TMP_8 H0))))))) in 
(let TMP_34 \def (\lambda (t0: T).(\lambda (t1: TList).(\lambda (H: (((nfs2 c 
(TApp t1 t)) \to (land (nfs2 c t1) (nf2 c t))))).(\lambda (H0: (land (nf2 c 
t0) (nfs2 c (TApp t1 t)))).(let H1 \def H0 in (let TMP_10 \def (nf2 c t0) in 
(let TMP_11 \def (TApp t1 t) in (let TMP_12 \def (nfs2 c TMP_11) in (let 
TMP_13 \def (nf2 c t0) in (let TMP_14 \def (nfs2 c t1) in (let TMP_15 \def 
(land TMP_13 TMP_14) in (let TMP_16 \def (nf2 c t) in (let TMP_17 \def (land 
TMP_15 TMP_16) in (let TMP_33 \def (\lambda (H2: (nf2 c t0)).(\lambda (H3: 
(nfs2 c (TApp t1 t))).(let H_x \def (H H3) in (let H4 \def H_x in (let TMP_18 
\def (nfs2 c t1) in (let TMP_19 \def (nf2 c t) in (let TMP_20 \def (nf2 c t0) 
in (let TMP_21 \def (nfs2 c t1) in (let TMP_22 \def (land TMP_20 TMP_21) in 
(let TMP_23 \def (nf2 c t) in (let TMP_24 \def (land TMP_22 TMP_23) in (let 
TMP_32 \def (\lambda (H5: (nfs2 c t1)).(\lambda (H6: (nf2 c t)).(let TMP_25 
\def (nf2 c t0) in (let TMP_26 \def (nfs2 c t1) in (let TMP_27 \def (land 
TMP_25 TMP_26) in (let TMP_28 \def (nf2 c t) in (let TMP_29 \def (nf2 c t0) 
in (let TMP_30 \def (nfs2 c t1) in (let TMP_31 \def (conj TMP_29 TMP_30 H2 
H5) in (conj TMP_27 TMP_28 TMP_31 H6)))))))))) in (land_ind TMP_18 TMP_19 
TMP_24 TMP_32 H4))))))))))))) in (land_ind TMP_10 TMP_12 TMP_17 TMP_33 
H1))))))))))))))) in (TList_ind TMP_3 TMP_9 TMP_34 ts)))))).

theorem nf2_appls_lref:
 \forall (c: C).(\forall (i: nat).((nf2 c (TLRef i)) \to (\forall (vs: 
TList).((nfs2 c vs) \to (nf2 c (THeads (Flat Appl) vs (TLRef i)))))))
\def
 \lambda (c: C).(\lambda (i: nat).(\lambda (H: (nf2 c (TLRef i))).(\lambda 
(vs: TList).(let TMP_4 \def (\lambda (t: TList).((nfs2 c t) \to (let TMP_1 
\def (Flat Appl) in (let TMP_2 \def (TLRef i) in (let TMP_3 \def (THeads 
TMP_1 t TMP_2) in (nf2 c TMP_3)))))) in (let TMP_5 \def (\lambda (_: True).H) 
in (let TMP_295 \def (\lambda (t: T).(\lambda (t0: TList).(\lambda (H0: 
(((nfs2 c t0) \to (nf2 c (THeads (Flat Appl) t0 (TLRef i)))))).(\lambda (H1: 
(land (nf2 c t) (nfs2 c t0))).(let H2 \def H1 in (let TMP_6 \def (nf2 c t) in 
(let TMP_7 \def (nfs2 c t0) in (let TMP_8 \def (Flat Appl) in (let TMP_9 \def 
(Flat Appl) in (let TMP_10 \def (TLRef i) in (let TMP_11 \def (THeads TMP_9 
t0 TMP_10) in (let TMP_12 \def (THead TMP_8 t TMP_11) in (let TMP_13 \def 
(nf2 c TMP_12) in (let TMP_294 \def (\lambda (H3: (nf2 c t)).(\lambda (H4: 
(nfs2 c t0)).(let H_y \def (H0 H4) in (\lambda (t2: T).(\lambda (H5: (pr2 c 
(THead (Flat Appl) t (THeads (Flat Appl) t0 (TLRef i))) t2)).(let TMP_14 \def 
(Flat Appl) in (let TMP_15 \def (TLRef i) in (let TMP_16 \def (THeads TMP_14 
t0 TMP_15) in (let H6 \def (pr2_gen_appl c t TMP_16 t2 H5) in (let TMP_19 
\def (\lambda (u2: T).(\lambda (t3: T).(let TMP_17 \def (Flat Appl) in (let 
TMP_18 \def (THead TMP_17 u2 t3) in (eq T t2 TMP_18))))) in (let TMP_20 \def 
(\lambda (u2: T).(\lambda (_: T).(pr2 c t u2))) in (let TMP_24 \def (\lambda 
(_: T).(\lambda (t3: T).(let TMP_21 \def (Flat Appl) in (let TMP_22 \def 
(TLRef i) in (let TMP_23 \def (THeads TMP_21 t0 TMP_22) in (pr2 c TMP_23 
t3)))))) in (let TMP_25 \def (ex3_2 T T TMP_19 TMP_20 TMP_24) in (let TMP_31 
\def (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(let 
TMP_26 \def (Flat Appl) in (let TMP_27 \def (TLRef i) in (let TMP_28 \def 
(THeads TMP_26 t0 TMP_27) in (let TMP_29 \def (Bind Abst) in (let TMP_30 \def 
(THead TMP_29 y1 z1) in (eq T TMP_28 TMP_30)))))))))) in (let TMP_34 \def 
(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(let TMP_32 
\def (Bind Abbr) in (let TMP_33 \def (THead TMP_32 u2 t3) in (eq T t2 
TMP_33))))))) in (let TMP_35 \def (\lambda (_: T).(\lambda (_: T).(\lambda 
(u2: T).(\lambda (_: T).(pr2 c t u2))))) in (let TMP_38 \def (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u: T).(let TMP_36 \def (Bind b) in (let TMP_37 \def (CHead c TMP_36 u) in 
(pr2 TMP_37 z1 t3))))))))) in (let TMP_39 \def (ex4_4 T T T T TMP_31 TMP_34 
TMP_35 TMP_38) in (let TMP_41 \def (\lambda (b: B).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(let TMP_40 \def (eq B 
b Abst) in (not TMP_40)))))))) in (let TMP_47 \def (\lambda (b: B).(\lambda 
(y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(let 
TMP_42 \def (Flat Appl) in (let TMP_43 \def (TLRef i) in (let TMP_44 \def 
(THeads TMP_42 t0 TMP_43) in (let TMP_45 \def (Bind b) in (let TMP_46 \def 
(THead TMP_45 y1 z1) in (eq T TMP_44 TMP_46)))))))))))) in (let TMP_54 \def 
(\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda 
(u2: T).(\lambda (y2: T).(let TMP_48 \def (Bind b) in (let TMP_49 \def (Flat 
Appl) in (let TMP_50 \def (S O) in (let TMP_51 \def (lift TMP_50 O u2) in 
(let TMP_52 \def (THead TMP_49 TMP_51 z2) in (let TMP_53 \def (THead TMP_48 
y2 TMP_52) in (eq T t2 TMP_53))))))))))))) in (let TMP_55 \def (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c t u2))))))) in (let TMP_56 \def (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) in (let TMP_59 \def (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(let TMP_57 \def (Bind 
b) in (let TMP_58 \def (CHead c TMP_57 y2) in (pr2 TMP_58 z1 z2))))))))) in 
(let TMP_60 \def (ex6_6 B T T T T T TMP_41 TMP_47 TMP_54 TMP_55 TMP_56 
TMP_59) in (let TMP_61 \def (Flat Appl) in (let TMP_62 \def (Flat Appl) in 
(let TMP_63 \def (TLRef i) in (let TMP_64 \def (THeads TMP_62 t0 TMP_63) in 
(let TMP_65 \def (THead TMP_61 t TMP_64) in (let TMP_66 \def (eq T TMP_65 t2) 
in (let TMP_132 \def (\lambda (H7: (ex3_2 T T (\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Flat Appl) u2 t3)))) (\lambda (u2: T).(\lambda (_: 
T).(pr2 c t u2))) (\lambda (_: T).(\lambda (t3: T).(pr2 c (THeads (Flat Appl) 
t0 (TLRef i)) t3))))).(let TMP_69 \def (\lambda (u2: T).(\lambda (t3: T).(let 
TMP_67 \def (Flat Appl) in (let TMP_68 \def (THead TMP_67 u2 t3) in (eq T t2 
TMP_68))))) in (let TMP_70 \def (\lambda (u2: T).(\lambda (_: T).(pr2 c t 
u2))) in (let TMP_74 \def (\lambda (_: T).(\lambda (t3: T).(let TMP_71 \def 
(Flat Appl) in (let TMP_72 \def (TLRef i) in (let TMP_73 \def (THeads TMP_71 
t0 TMP_72) in (pr2 c TMP_73 t3)))))) in (let TMP_75 \def (Flat Appl) in (let 
TMP_76 \def (Flat Appl) in (let TMP_77 \def (TLRef i) in (let TMP_78 \def 
(THeads TMP_76 t0 TMP_77) in (let TMP_79 \def (THead TMP_75 t TMP_78) in (let 
TMP_80 \def (eq T TMP_79 t2) in (let TMP_131 \def (\lambda (x0: T).(\lambda 
(x1: T).(\lambda (H8: (eq T t2 (THead (Flat Appl) x0 x1))).(\lambda (H9: (pr2 
c t x0)).(\lambda (H10: (pr2 c (THeads (Flat Appl) t0 (TLRef i)) x1)).(let 
TMP_81 \def (Flat Appl) in (let TMP_82 \def (THead TMP_81 x0 x1) in (let 
TMP_88 \def (\lambda (t1: T).(let TMP_83 \def (Flat Appl) in (let TMP_84 \def 
(Flat Appl) in (let TMP_85 \def (TLRef i) in (let TMP_86 \def (THeads TMP_84 
t0 TMP_85) in (let TMP_87 \def (THead TMP_83 t TMP_86) in (eq T TMP_87 
t1))))))) in (let TMP_92 \def (\lambda (t1: T).(let TMP_89 \def (Flat Appl) 
in (let TMP_90 \def (TLRef i) in (let TMP_91 \def (THeads TMP_89 t0 TMP_90) 
in (pr2 c TMP_91 t1))))) in (let TMP_93 \def (Flat Appl) in (let TMP_94 \def 
(TLRef i) in (let TMP_95 \def (THeads TMP_93 t0 TMP_94) in (let TMP_96 \def 
(H_y x1 H10) in (let H11 \def (eq_ind_r T x1 TMP_92 H10 TMP_95 TMP_96) in 
(let TMP_97 \def (Flat Appl) in (let TMP_98 \def (TLRef i) in (let TMP_99 
\def (THeads TMP_97 t0 TMP_98) in (let TMP_107 \def (\lambda (t1: T).(let 
TMP_100 \def (Flat Appl) in (let TMP_101 \def (Flat Appl) in (let TMP_102 
\def (TLRef i) in (let TMP_103 \def (THeads TMP_101 t0 TMP_102) in (let 
TMP_104 \def (THead TMP_100 t TMP_103) in (let TMP_105 \def (Flat Appl) in 
(let TMP_106 \def (THead TMP_105 x0 t1) in (eq T TMP_104 TMP_106))))))))) in 
(let TMP_108 \def (\lambda (t1: T).(pr2 c t t1)) in (let TMP_109 \def (H3 x0 
H9) in (let H12 \def (eq_ind_r T x0 TMP_108 H9 t TMP_109) in (let TMP_120 
\def (\lambda (t1: T).(let TMP_110 \def (Flat Appl) in (let TMP_111 \def 
(Flat Appl) in (let TMP_112 \def (TLRef i) in (let TMP_113 \def (THeads 
TMP_111 t0 TMP_112) in (let TMP_114 \def (THead TMP_110 t TMP_113) in (let 
TMP_115 \def (Flat Appl) in (let TMP_116 \def (Flat Appl) in (let TMP_117 
\def (TLRef i) in (let TMP_118 \def (THeads TMP_116 t0 TMP_117) in (let 
TMP_119 \def (THead TMP_115 t1 TMP_118) in (eq T TMP_114 TMP_119)))))))))))) 
in (let TMP_121 \def (Flat Appl) in (let TMP_122 \def (Flat Appl) in (let 
TMP_123 \def (TLRef i) in (let TMP_124 \def (THeads TMP_122 t0 TMP_123) in 
(let TMP_125 \def (THead TMP_121 t TMP_124) in (let TMP_126 \def (refl_equal 
T TMP_125) in (let TMP_127 \def (H3 x0 H9) in (let TMP_128 \def (eq_ind T t 
TMP_120 TMP_126 x0 TMP_127) in (let TMP_129 \def (H_y x1 H10) in (let TMP_130 
\def (eq_ind T TMP_99 TMP_107 TMP_128 x1 TMP_129) in (eq_ind_r T TMP_82 
TMP_88 TMP_130 t2 H8))))))))))))))))))))))))))))))))) in (ex3_2_ind T T 
TMP_69 TMP_70 TMP_74 TMP_80 TMP_131 H7)))))))))))) in (let TMP_201 \def 
(\lambda (H7: (ex4_4 T T T T (\lambda (y1: T).(\lambda (z1: T).(\lambda (_: 
T).(\lambda (_: T).(eq T (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind Abst) 
y1 z1)))))) (\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: 
T).(eq T t2 (THead (Bind Abbr) u2 t3)))))) (\lambda (_: T).(\lambda (_: 
T).(\lambda (u2: T).(\lambda (_: T).(pr2 c t u2))))) (\lambda (_: T).(\lambda 
(z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall (u: T).(pr2 
(CHead c (Bind b) u) z1 t3))))))))).(let TMP_138 \def (\lambda (y1: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (_: T).(let TMP_133 \def (Flat 
Appl) in (let TMP_134 \def (TLRef i) in (let TMP_135 \def (THeads TMP_133 t0 
TMP_134) in (let TMP_136 \def (Bind Abst) in (let TMP_137 \def (THead TMP_136 
y1 z1) in (eq T TMP_135 TMP_137)))))))))) in (let TMP_141 \def (\lambda (_: 
T).(\lambda (_: T).(\lambda (u2: T).(\lambda (t3: T).(let TMP_139 \def (Bind 
Abbr) in (let TMP_140 \def (THead TMP_139 u2 t3) in (eq T t2 TMP_140))))))) 
in (let TMP_142 \def (\lambda (_: T).(\lambda (_: T).(\lambda (u2: 
T).(\lambda (_: T).(pr2 c t u2))))) in (let TMP_145 \def (\lambda (_: 
T).(\lambda (z1: T).(\lambda (_: T).(\lambda (t3: T).(\forall (b: B).(\forall 
(u: T).(let TMP_143 \def (Bind b) in (let TMP_144 \def (CHead c TMP_143 u) in 
(pr2 TMP_144 z1 t3))))))))) in (let TMP_146 \def (Flat Appl) in (let TMP_147 
\def (Flat Appl) in (let TMP_148 \def (TLRef i) in (let TMP_149 \def (THeads 
TMP_147 t0 TMP_148) in (let TMP_150 \def (THead TMP_146 t TMP_149) in (let 
TMP_151 \def (eq T TMP_150 t2) in (let TMP_200 \def (\lambda (x0: T).(\lambda 
(x1: T).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H8: (eq T (THeads (Flat 
Appl) t0 (TLRef i)) (THead (Bind Abst) x0 x1))).(\lambda (H9: (eq T t2 (THead 
(Bind Abbr) x2 x3))).(\lambda (_: (pr2 c t x2)).(\lambda (_: ((\forall (b: 
B).(\forall (u: T).(pr2 (CHead c (Bind b) u) x1 x3))))).(let TMP_152 \def 
(Bind Abbr) in (let TMP_153 \def (THead TMP_152 x2 x3) in (let TMP_159 \def 
(\lambda (t1: T).(let TMP_154 \def (Flat Appl) in (let TMP_155 \def (Flat 
Appl) in (let TMP_156 \def (TLRef i) in (let TMP_157 \def (THeads TMP_155 t0 
TMP_156) in (let TMP_158 \def (THead TMP_154 t TMP_157) in (eq T TMP_158 
t1))))))) in (let TMP_167 \def (\lambda (t1: TList).((nf2 c (THeads (Flat 
Appl) t1 (TLRef i))) \to ((eq T (THeads (Flat Appl) t1 (TLRef i)) (THead 
(Bind Abst) x0 x1)) \to (let TMP_160 \def (Flat Appl) in (let TMP_161 \def 
(Flat Appl) in (let TMP_162 \def (TLRef i) in (let TMP_163 \def (THeads 
TMP_161 t1 TMP_162) in (let TMP_164 \def (THead TMP_160 t TMP_163) in (let 
TMP_165 \def (Bind Abbr) in (let TMP_166 \def (THead TMP_165 x2 x3) in (eq T 
TMP_164 TMP_166))))))))))) in (let TMP_180 \def (\lambda (_: (nf2 c (THeads 
(Flat Appl) TNil (TLRef i)))).(\lambda (H13: (eq T (THeads (Flat Appl) TNil 
(TLRef i)) (THead (Bind Abst) x0 x1))).(let TMP_168 \def (TLRef i) in (let 
TMP_169 \def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) in (let 
TMP_170 \def (Bind Abst) in (let TMP_171 \def (THead TMP_170 x0 x1) in (let 
H14 \def (eq_ind T TMP_168 TMP_169 I TMP_171 H13) in (let TMP_172 \def (Flat 
Appl) in (let TMP_173 \def (Flat Appl) in (let TMP_174 \def (TLRef i) in (let 
TMP_175 \def (THeads TMP_173 TNil TMP_174) in (let TMP_176 \def (THead 
TMP_172 t TMP_175) in (let TMP_177 \def (Bind Abbr) in (let TMP_178 \def 
(THead TMP_177 x2 x3) in (let TMP_179 \def (eq T TMP_176 TMP_178) in 
(False_ind TMP_179 H14)))))))))))))))) in (let TMP_198 \def (\lambda (t1: 
T).(\lambda (t3: TList).(\lambda (_: (((nf2 c (THeads (Flat Appl) t3 (TLRef 
i))) \to ((eq T (THeads (Flat Appl) t3 (TLRef i)) (THead (Bind Abst) x0 x1)) 
\to (eq T (THead (Flat Appl) t (THeads (Flat Appl) t3 (TLRef i))) (THead 
(Bind Abbr) x2 x3)))))).(\lambda (_: (nf2 c (THeads (Flat Appl) (TCons t1 t3) 
(TLRef i)))).(\lambda (H13: (eq T (THeads (Flat Appl) (TCons t1 t3) (TLRef 
i)) (THead (Bind Abst) x0 x1))).(let TMP_181 \def (Flat Appl) in (let TMP_182 
\def (Flat Appl) in (let TMP_183 \def (TLRef i) in (let TMP_184 \def (THeads 
TMP_182 t3 TMP_183) in (let TMP_185 \def (THead TMP_181 t1 TMP_184) in (let 
TMP_186 \def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead k _ _) \Rightarrow (match k with [(Bind 
_) \Rightarrow False | (Flat _) \Rightarrow True])])) in (let TMP_187 \def 
(Bind Abst) in (let TMP_188 \def (THead TMP_187 x0 x1) in (let H14 \def 
(eq_ind T TMP_185 TMP_186 I TMP_188 H13) in (let TMP_189 \def (Flat Appl) in 
(let TMP_190 \def (Flat Appl) in (let TMP_191 \def (TCons t1 t3) in (let 
TMP_192 \def (TLRef i) in (let TMP_193 \def (THeads TMP_190 TMP_191 TMP_192) 
in (let TMP_194 \def (THead TMP_189 t TMP_193) in (let TMP_195 \def (Bind 
Abbr) in (let TMP_196 \def (THead TMP_195 x2 x3) in (let TMP_197 \def (eq T 
TMP_194 TMP_196) in (False_ind TMP_197 H14)))))))))))))))))))))))) in (let 
TMP_199 \def (TList_ind TMP_167 TMP_180 TMP_198 t0 H_y H8) in (eq_ind_r T 
TMP_153 TMP_159 TMP_199 t2 H9)))))))))))))))) in (ex4_4_ind T T T T TMP_138 
TMP_141 TMP_142 TMP_145 TMP_151 TMP_200 H7))))))))))))) in (let TMP_293 \def 
(\lambda (H7: (ex6_6 B T T T T T (\lambda (b: B).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(not (eq B b Abst)))))))) 
(\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda (_: T).(\lambda 
(_: T).(\lambda (_: T).(eq T (THeads (Flat Appl) t0 (TLRef i)) (THead (Bind 
b) y1 z1)))))))) (\lambda (b: B).(\lambda (_: T).(\lambda (_: T).(\lambda 
(z2: T).(\lambda (u2: T).(\lambda (y2: T).(eq T t2 (THead (Bind b) y2 (THead 
(Flat Appl) (lift (S O) O u2) z2))))))))) (\lambda (_: B).(\lambda (_: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda (_: T).(pr2 c t 
u2))))))) (\lambda (_: B).(\lambda (y1: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 y2))))))) (\lambda (b: 
B).(\lambda (_: T).(\lambda (z1: T).(\lambda (z2: T).(\lambda (_: T).(\lambda 
(y2: T).(pr2 (CHead c (Bind b) y2) z1 z2))))))))).(let TMP_203 \def (\lambda 
(b: B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: 
T).(\lambda (_: T).(let TMP_202 \def (eq B b Abst) in (not TMP_202)))))))) in 
(let TMP_209 \def (\lambda (b: B).(\lambda (y1: T).(\lambda (z1: T).(\lambda 
(_: T).(\lambda (_: T).(\lambda (_: T).(let TMP_204 \def (Flat Appl) in (let 
TMP_205 \def (TLRef i) in (let TMP_206 \def (THeads TMP_204 t0 TMP_205) in 
(let TMP_207 \def (Bind b) in (let TMP_208 \def (THead TMP_207 y1 z1) in (eq 
T TMP_206 TMP_208)))))))))))) in (let TMP_216 \def (\lambda (b: B).(\lambda 
(_: T).(\lambda (_: T).(\lambda (z2: T).(\lambda (u2: T).(\lambda (y2: 
T).(let TMP_210 \def (Bind b) in (let TMP_211 \def (Flat Appl) in (let 
TMP_212 \def (S O) in (let TMP_213 \def (lift TMP_212 O u2) in (let TMP_214 
\def (THead TMP_211 TMP_213 z2) in (let TMP_215 \def (THead TMP_210 y2 
TMP_214) in (eq T t2 TMP_215))))))))))))) in (let TMP_217 \def (\lambda (_: 
B).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (u2: T).(\lambda 
(_: T).(pr2 c t u2))))))) in (let TMP_218 \def (\lambda (_: B).(\lambda (y1: 
T).(\lambda (_: T).(\lambda (_: T).(\lambda (_: T).(\lambda (y2: T).(pr2 c y1 
y2))))))) in (let TMP_221 \def (\lambda (b: B).(\lambda (_: T).(\lambda (z1: 
T).(\lambda (z2: T).(\lambda (_: T).(\lambda (y2: T).(let TMP_219 \def (Bind 
b) in (let TMP_220 \def (CHead c TMP_219 y2) in (pr2 TMP_220 z1 z2))))))))) 
in (let TMP_222 \def (Flat Appl) in (let TMP_223 \def (Flat Appl) in (let 
TMP_224 \def (TLRef i) in (let TMP_225 \def (THeads TMP_223 t0 TMP_224) in 
(let TMP_226 \def (THead TMP_222 t TMP_225) in (let TMP_227 \def (eq T 
TMP_226 t2) in (let TMP_292 \def (\lambda (x0: B).(\lambda (x1: T).(\lambda 
(x2: T).(\lambda (x3: T).(\lambda (x4: T).(\lambda (x5: T).(\lambda (_: (not 
(eq B x0 Abst))).(\lambda (H9: (eq T (THeads (Flat Appl) t0 (TLRef i)) (THead 
(Bind x0) x1 x2))).(\lambda (H10: (eq T t2 (THead (Bind x0) x5 (THead (Flat 
Appl) (lift (S O) O x4) x3)))).(\lambda (_: (pr2 c t x4)).(\lambda (_: (pr2 c 
x1 x5)).(\lambda (_: (pr2 (CHead c (Bind x0) x5) x2 x3)).(let TMP_228 \def 
(Bind x0) in (let TMP_229 \def (Flat Appl) in (let TMP_230 \def (S O) in (let 
TMP_231 \def (lift TMP_230 O x4) in (let TMP_232 \def (THead TMP_229 TMP_231 
x3) in (let TMP_233 \def (THead TMP_228 x5 TMP_232) in (let TMP_239 \def 
(\lambda (t1: T).(let TMP_234 \def (Flat Appl) in (let TMP_235 \def (Flat 
Appl) in (let TMP_236 \def (TLRef i) in (let TMP_237 \def (THeads TMP_235 t0 
TMP_236) in (let TMP_238 \def (THead TMP_234 t TMP_237) in (eq T TMP_238 
t1))))))) in (let TMP_251 \def (\lambda (t1: TList).((nf2 c (THeads (Flat 
Appl) t1 (TLRef i))) \to ((eq T (THeads (Flat Appl) t1 (TLRef i)) (THead 
(Bind x0) x1 x2)) \to (let TMP_240 \def (Flat Appl) in (let TMP_241 \def 
(Flat Appl) in (let TMP_242 \def (TLRef i) in (let TMP_243 \def (THeads 
TMP_241 t1 TMP_242) in (let TMP_244 \def (THead TMP_240 t TMP_243) in (let 
TMP_245 \def (Bind x0) in (let TMP_246 \def (Flat Appl) in (let TMP_247 \def 
(S O) in (let TMP_248 \def (lift TMP_247 O x4) in (let TMP_249 \def (THead 
TMP_246 TMP_248 x3) in (let TMP_250 \def (THead TMP_245 x5 TMP_249) in (eq T 
TMP_244 TMP_250))))))))))))))) in (let TMP_268 \def (\lambda (_: (nf2 c 
(THeads (Flat Appl) TNil (TLRef i)))).(\lambda (H15: (eq T (THeads (Flat 
Appl) TNil (TLRef i)) (THead (Bind x0) x1 x2))).(let TMP_252 \def (TLRef i) 
in (let TMP_253 \def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow 
False | (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) in 
(let TMP_254 \def (Bind x0) in (let TMP_255 \def (THead TMP_254 x1 x2) in 
(let H16 \def (eq_ind T TMP_252 TMP_253 I TMP_255 H15) in (let TMP_256 \def 
(Flat Appl) in (let TMP_257 \def (Flat Appl) in (let TMP_258 \def (TLRef i) 
in (let TMP_259 \def (THeads TMP_257 TNil TMP_258) in (let TMP_260 \def 
(THead TMP_256 t TMP_259) in (let TMP_261 \def (Bind x0) in (let TMP_262 \def 
(Flat Appl) in (let TMP_263 \def (S O) in (let TMP_264 \def (lift TMP_263 O 
x4) in (let TMP_265 \def (THead TMP_262 TMP_264 x3) in (let TMP_266 \def 
(THead TMP_261 x5 TMP_265) in (let TMP_267 \def (eq T TMP_260 TMP_266) in 
(False_ind TMP_267 H16)))))))))))))))))))) in (let TMP_290 \def (\lambda (t1: 
T).(\lambda (t3: TList).(\lambda (_: (((nf2 c (THeads (Flat Appl) t3 (TLRef 
i))) \to ((eq T (THeads (Flat Appl) t3 (TLRef i)) (THead (Bind x0) x1 x2)) 
\to (eq T (THead (Flat Appl) t (THeads (Flat Appl) t3 (TLRef i))) (THead 
(Bind x0) x5 (THead (Flat Appl) (lift (S O) O x4) x3))))))).(\lambda (_: (nf2 
c (THeads (Flat Appl) (TCons t1 t3) (TLRef i)))).(\lambda (H15: (eq T (THeads 
(Flat Appl) (TCons t1 t3) (TLRef i)) (THead (Bind x0) x1 x2))).(let TMP_269 
\def (Flat Appl) in (let TMP_270 \def (Flat Appl) in (let TMP_271 \def (TLRef 
i) in (let TMP_272 \def (THeads TMP_270 t3 TMP_271) in (let TMP_273 \def 
(THead TMP_269 t1 TMP_272) in (let TMP_274 \def (\lambda (ee: T).(match ee 
with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False | (THead k _ 
_) \Rightarrow (match k with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])])) in (let TMP_275 \def (Bind x0) in (let TMP_276 \def 
(THead TMP_275 x1 x2) in (let H16 \def (eq_ind T TMP_273 TMP_274 I TMP_276 
H15) in (let TMP_277 \def (Flat Appl) in (let TMP_278 \def (Flat Appl) in 
(let TMP_279 \def (TCons t1 t3) in (let TMP_280 \def (TLRef i) in (let 
TMP_281 \def (THeads TMP_278 TMP_279 TMP_280) in (let TMP_282 \def (THead 
TMP_277 t TMP_281) in (let TMP_283 \def (Bind x0) in (let TMP_284 \def (Flat 
Appl) in (let TMP_285 \def (S O) in (let TMP_286 \def (lift TMP_285 O x4) in 
(let TMP_287 \def (THead TMP_284 TMP_286 x3) in (let TMP_288 \def (THead 
TMP_283 x5 TMP_287) in (let TMP_289 \def (eq T TMP_282 TMP_288) in (False_ind 
TMP_289 H16)))))))))))))))))))))))))))) in (let TMP_291 \def (TList_ind 
TMP_251 TMP_268 TMP_290 t0 H_y H9) in (eq_ind_r T TMP_233 TMP_239 TMP_291 t2 
H10)))))))))))))))))))))))) in (ex6_6_ind B T T T T T TMP_203 TMP_209 TMP_216 
TMP_217 TMP_218 TMP_221 TMP_227 TMP_292 H7))))))))))))))) in (or3_ind TMP_25 
TMP_39 TMP_60 TMP_66 TMP_132 TMP_201 TMP_293 
H6))))))))))))))))))))))))))))))))))) in (land_ind TMP_6 TMP_7 TMP_13 TMP_294 
H2))))))))))))))) in (TList_ind TMP_4 TMP_5 TMP_295 vs))))))).

theorem nf2_appl_lref:
 \forall (c: C).(\forall (u: T).((nf2 c u) \to (\forall (i: nat).((nf2 c 
(TLRef i)) \to (nf2 c (THead (Flat Appl) u (TLRef i)))))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (H: (nf2 c u)).(\lambda (i: 
nat).(\lambda (H0: (nf2 c (TLRef i))).(let TMP_1 \def (TCons u TNil) in (let 
H_y \def (nf2_appls_lref c i H0 TMP_1) in (let TMP_2 \def (nf2 c u) in (let 
TMP_3 \def (conj TMP_2 True H I) in (H_y TMP_3))))))))).

theorem nf2_lref_abst:
 \forall (c: C).(\forall (e: C).(\forall (u: T).(\forall (i: nat).((getl i c 
(CHead e (Bind Abst) u)) \to (nf2 c (TLRef i))))))
\def
 \lambda (c: C).(\lambda (e: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead e (Bind Abst) u))).(\lambda (t2: T).(\lambda (H0: (pr2 c 
(TLRef i) t2)).(let H1 \def (pr2_gen_lref c t2 i H0) in (let TMP_1 \def 
(TLRef i) in (let TMP_2 \def (eq T t2 TMP_1) in (let TMP_5 \def (\lambda (d: 
C).(\lambda (u0: T).(let TMP_3 \def (Bind Abbr) in (let TMP_4 \def (CHead d 
TMP_3 u0) in (getl i c TMP_4))))) in (let TMP_8 \def (\lambda (_: C).(\lambda 
(u0: T).(let TMP_6 \def (S i) in (let TMP_7 \def (lift TMP_6 O u0) in (eq T 
t2 TMP_7))))) in (let TMP_9 \def (ex2_2 C T TMP_5 TMP_8) in (let TMP_10 \def 
(TLRef i) in (let TMP_11 \def (eq T TMP_10 t2) in (let TMP_17 \def (\lambda 
(H2: (eq T t2 (TLRef i))).(let TMP_12 \def (TLRef i) in (let TMP_14 \def 
(\lambda (t: T).(let TMP_13 \def (TLRef i) in (eq T TMP_13 t))) in (let 
TMP_15 \def (TLRef i) in (let TMP_16 \def (refl_equal T TMP_15) in (eq_ind_r 
T TMP_12 TMP_14 TMP_16 t2 H2)))))) in (let TMP_56 \def (\lambda (H2: (ex2_2 C 
T (\lambda (d: C).(\lambda (u0: T).(getl i c (CHead d (Bind Abbr) u0)))) 
(\lambda (_: C).(\lambda (u0: T).(eq T t2 (lift (S i) O u0)))))).(let TMP_20 
\def (\lambda (d: C).(\lambda (u0: T).(let TMP_18 \def (Bind Abbr) in (let 
TMP_19 \def (CHead d TMP_18 u0) in (getl i c TMP_19))))) in (let TMP_23 \def 
(\lambda (_: C).(\lambda (u0: T).(let TMP_21 \def (S i) in (let TMP_22 \def 
(lift TMP_21 O u0) in (eq T t2 TMP_22))))) in (let TMP_24 \def (TLRef i) in 
(let TMP_25 \def (eq T TMP_24 t2) in (let TMP_55 \def (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H3: (getl i c (CHead x0 (Bind Abbr) 
x1))).(\lambda (H4: (eq T t2 (lift (S i) O x1))).(let TMP_26 \def (S i) in 
(let TMP_27 \def (lift TMP_26 O x1) in (let TMP_29 \def (\lambda (t: T).(let 
TMP_28 \def (TLRef i) in (eq T TMP_28 t))) in (let TMP_30 \def (Bind Abst) in 
(let TMP_31 \def (CHead e TMP_30 u) in (let TMP_32 \def (\lambda (c0: 
C).(getl i c c0)) in (let TMP_33 \def (Bind Abbr) in (let TMP_34 \def (CHead 
x0 TMP_33 x1) in (let TMP_35 \def (Bind Abst) in (let TMP_36 \def (CHead e 
TMP_35 u) in (let TMP_37 \def (Bind Abbr) in (let TMP_38 \def (CHead x0 
TMP_37 x1) in (let TMP_39 \def (getl_mono c TMP_36 i H TMP_38 H3) in (let H5 
\def (eq_ind C TMP_31 TMP_32 H TMP_34 TMP_39) in (let TMP_40 \def (Bind Abst) 
in (let TMP_41 \def (CHead e TMP_40 u) in (let TMP_42 \def (\lambda (ee: 
C).(match ee with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow 
(match k with [(Bind b) \Rightarrow (match b with [Abbr \Rightarrow False | 
Abst \Rightarrow True | Void \Rightarrow False]) | (Flat _) \Rightarrow 
False])])) in (let TMP_43 \def (Bind Abbr) in (let TMP_44 \def (CHead x0 
TMP_43 x1) in (let TMP_45 \def (Bind Abst) in (let TMP_46 \def (CHead e 
TMP_45 u) in (let TMP_47 \def (Bind Abbr) in (let TMP_48 \def (CHead x0 
TMP_47 x1) in (let TMP_49 \def (getl_mono c TMP_46 i H TMP_48 H3) in (let H6 
\def (eq_ind C TMP_41 TMP_42 I TMP_44 TMP_49) in (let TMP_50 \def (TLRef i) 
in (let TMP_51 \def (S i) in (let TMP_52 \def (lift TMP_51 O x1) in (let 
TMP_53 \def (eq T TMP_50 TMP_52) in (let TMP_54 \def (False_ind TMP_53 H6) in 
(eq_ind_r T TMP_27 TMP_29 TMP_54 t2 H4))))))))))))))))))))))))))))))))))) in 
(ex2_2_ind C T TMP_20 TMP_23 TMP_25 TMP_55 H2))))))) in (or_ind TMP_2 TMP_9 
TMP_11 TMP_17 TMP_56 H1))))))))))))))))).

theorem nf2_lift:
 \forall (d: C).(\forall (t: T).((nf2 d t) \to (\forall (c: C).(\forall (h: 
nat).(\forall (i: nat).((drop h i c d) \to (nf2 c (lift h i t))))))))
\def
 \lambda (d: C).(\lambda (t: T).(\lambda (H: ((\forall (t2: T).((pr2 d t t2) 
\to (eq T t t2))))).(\lambda (c: C).(\lambda (h: nat).(\lambda (i: 
nat).(\lambda (H0: (drop h i c d)).(\lambda (t2: T).(\lambda (H1: (pr2 c 
(lift h i t) t2)).(let H2 \def (pr2_gen_lift c t t2 h i H1 d H0) in (let 
TMP_2 \def (\lambda (t3: T).(let TMP_1 \def (lift h i t3) in (eq T t2 
TMP_1))) in (let TMP_3 \def (\lambda (t3: T).(pr2 d t t3)) in (let TMP_4 \def 
(lift h i t) in (let TMP_5 \def (eq T TMP_4 t2) in (let TMP_16 \def (\lambda 
(x: T).(\lambda (H3: (eq T t2 (lift h i x))).(\lambda (H4: (pr2 d t x)).(let 
TMP_6 \def (lift h i x) in (let TMP_8 \def (\lambda (t0: T).(let TMP_7 \def 
(lift h i t) in (eq T TMP_7 t0))) in (let H_y \def (H x H4) in (let TMP_9 
\def (\lambda (t0: T).(pr2 d t t0)) in (let H5 \def (eq_ind_r T x TMP_9 H4 t 
H_y) in (let TMP_12 \def (\lambda (t0: T).(let TMP_10 \def (lift h i t) in 
(let TMP_11 \def (lift h i t0) in (eq T TMP_10 TMP_11)))) in (let TMP_13 \def 
(lift h i t) in (let TMP_14 \def (refl_equal T TMP_13) in (let TMP_15 \def 
(eq_ind T t TMP_12 TMP_14 x H_y) in (eq_ind_r T TMP_6 TMP_8 TMP_15 t2 
H3))))))))))))) in (ex2_ind T TMP_2 TMP_3 TMP_5 TMP_16 H2))))))))))))))).

