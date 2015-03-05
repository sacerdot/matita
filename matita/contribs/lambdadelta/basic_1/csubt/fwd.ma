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

include "basic_1/csubt/defs.ma".

let rec csubt_ind (g: G) (P: (C \to (C \to Prop))) (f: (\forall (n: nat).(P 
(CSort n) (CSort n)))) (f0: (\forall (c1: C).(\forall (c2: C).((csubt g c1 
c2) \to ((P c1 c2) \to (\forall (k: K).(\forall (u: T).(P (CHead c1 k u) 
(CHead c2 k u))))))))) (f1: (\forall (c1: C).(\forall (c2: C).((csubt g c1 
c2) \to ((P c1 c2) \to (\forall (b: B).((not (eq B b Void)) \to (\forall (u1: 
T).(\forall (u2: T).(P (CHead c1 (Bind Void) u1) (CHead c2 (Bind b) 
u2))))))))))) (f2: (\forall (c1: C).(\forall (c2: C).((csubt g c1 c2) \to ((P 
c1 c2) \to (\forall (u: T).(\forall (t: T).((ty3 g c1 u t) \to ((ty3 g c2 u 
t) \to (P (CHead c1 (Bind Abst) t) (CHead c2 (Bind Abbr) u))))))))))) (c: C) 
(c0: C) (c1: csubt g c c0) on c1: P c c0 \def match c1 with [(csubt_sort n) 
\Rightarrow (f n) | (csubt_head c2 c3 c4 k u) \Rightarrow (let TMP_3 \def 
((csubt_ind g P f f0 f1 f2) c2 c3 c4) in (f0 c2 c3 c4 TMP_3 k u)) | 
(csubt_void c2 c3 c4 b n u1 u2) \Rightarrow (let TMP_2 \def ((csubt_ind g P f 
f0 f1 f2) c2 c3 c4) in (f1 c2 c3 c4 TMP_2 b n u1 u2)) | (csubt_abst c2 c3 c4 
u t t0 t1) \Rightarrow (let TMP_1 \def ((csubt_ind g P f f0 f1 f2) c2 c3 c4) 
in (f2 c2 c3 c4 TMP_1 u t t0 t1))].

theorem csubt_gen_abbr:
 \forall (g: G).(\forall (e1: C).(\forall (c2: C).(\forall (v: T).((csubt g 
(CHead e1 (Bind Abbr) v) c2) \to (ex2 C (\lambda (e2: C).(eq C c2 (CHead e2 
(Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 e2)))))))
\def
 \lambda (g: G).(\lambda (e1: C).(\lambda (c2: C).(\lambda (v: T).(\lambda 
(H: (csubt g (CHead e1 (Bind Abbr) v) c2)).(let TMP_1 \def (Bind Abbr) in 
(let TMP_2 \def (CHead e1 TMP_1 v) in (let TMP_3 \def (\lambda (c: C).(csubt 
g c c2)) in (let TMP_8 \def (\lambda (_: C).(let TMP_6 \def (\lambda (e2: 
C).(let TMP_4 \def (Bind Abbr) in (let TMP_5 \def (CHead e2 TMP_4 v) in (eq C 
c2 TMP_5)))) in (let TMP_7 \def (\lambda (e2: C).(csubt g e1 e2)) in (ex2 C 
TMP_6 TMP_7)))) in (let TMP_96 \def (\lambda (y: C).(\lambda (H0: (csubt g y 
c2)).(let TMP_13 \def (\lambda (c: C).(\lambda (c0: C).((eq C c (CHead e1 
(Bind Abbr) v)) \to (let TMP_11 \def (\lambda (e2: C).(let TMP_9 \def (Bind 
Abbr) in (let TMP_10 \def (CHead e2 TMP_9 v) in (eq C c0 TMP_10)))) in (let 
TMP_12 \def (\lambda (e2: C).(csubt g e1 e2)) in (ex2 C TMP_11 TMP_12)))))) 
in (let TMP_24 \def (\lambda (n: nat).(\lambda (H1: (eq C (CSort n) (CHead e1 
(Bind Abbr) v))).(let TMP_14 \def (CSort n) in (let TMP_15 \def (\lambda (ee: 
C).(match ee with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow 
False])) in (let TMP_16 \def (Bind Abbr) in (let TMP_17 \def (CHead e1 TMP_16 
v) in (let H2 \def (eq_ind C TMP_14 TMP_15 I TMP_17 H1) in (let TMP_21 \def 
(\lambda (e2: C).(let TMP_18 \def (CSort n) in (let TMP_19 \def (Bind Abbr) 
in (let TMP_20 \def (CHead e2 TMP_19 v) in (eq C TMP_18 TMP_20))))) in (let 
TMP_22 \def (\lambda (e2: C).(csubt g e1 e2)) in (let TMP_23 \def (ex2 C 
TMP_21 TMP_22) in (False_ind TMP_23 H2))))))))))) in (let TMP_69 \def 
(\lambda (c1: C).(\lambda (c3: C).(\lambda (H1: (csubt g c1 c3)).(\lambda 
(H2: (((eq C c1 (CHead e1 (Bind Abbr) v)) \to (ex2 C (\lambda (e2: C).(eq C 
c3 (CHead e2 (Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 e2)))))).(\lambda 
(k: K).(\lambda (u: T).(\lambda (H3: (eq C (CHead c1 k u) (CHead e1 (Bind 
Abbr) v))).(let TMP_25 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow c1 | (CHead c _ _) \Rightarrow c])) in (let TMP_26 \def (CHead c1 
k u) in (let TMP_27 \def (Bind Abbr) in (let TMP_28 \def (CHead e1 TMP_27 v) 
in (let H4 \def (f_equal C C TMP_25 TMP_26 TMP_28 H3) in (let TMP_29 \def 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow k | (CHead _ k0 _) 
\Rightarrow k0])) in (let TMP_30 \def (CHead c1 k u) in (let TMP_31 \def 
(Bind Abbr) in (let TMP_32 \def (CHead e1 TMP_31 v) in (let H5 \def (f_equal 
C K TMP_29 TMP_30 TMP_32 H3) in (let TMP_33 \def (\lambda (e: C).(match e 
with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) in (let TMP_34 
\def (CHead c1 k u) in (let TMP_35 \def (Bind Abbr) in (let TMP_36 \def 
(CHead e1 TMP_35 v) in (let H6 \def (f_equal C T TMP_33 TMP_34 TMP_36 H3) in 
(let TMP_67 \def (\lambda (H7: (eq K k (Bind Abbr))).(\lambda (H8: (eq C c1 
e1)).(let TMP_42 \def (\lambda (t: T).(let TMP_40 \def (\lambda (e2: C).(let 
TMP_37 \def (CHead c3 k t) in (let TMP_38 \def (Bind Abbr) in (let TMP_39 
\def (CHead e2 TMP_38 v) in (eq C TMP_37 TMP_39))))) in (let TMP_41 \def 
(\lambda (e2: C).(csubt g e1 e2)) in (ex2 C TMP_40 TMP_41)))) in (let TMP_43 
\def (Bind Abbr) in (let TMP_49 \def (\lambda (k0: K).(let TMP_47 \def 
(\lambda (e2: C).(let TMP_44 \def (CHead c3 k0 v) in (let TMP_45 \def (Bind 
Abbr) in (let TMP_46 \def (CHead e2 TMP_45 v) in (eq C TMP_44 TMP_46))))) in 
(let TMP_48 \def (\lambda (e2: C).(csubt g e1 e2)) in (ex2 C TMP_47 
TMP_48)))) in (let TMP_54 \def (\lambda (c: C).((eq C c (CHead e1 (Bind Abbr) 
v)) \to (let TMP_52 \def (\lambda (e2: C).(let TMP_50 \def (Bind Abbr) in 
(let TMP_51 \def (CHead e2 TMP_50 v) in (eq C c3 TMP_51)))) in (let TMP_53 
\def (\lambda (e2: C).(csubt g e1 e2)) in (ex2 C TMP_52 TMP_53))))) in (let 
H9 \def (eq_ind C c1 TMP_54 H2 e1 H8) in (let TMP_55 \def (\lambda (c: 
C).(csubt g c c3)) in (let H10 \def (eq_ind C c1 TMP_55 H1 e1 H8) in (let 
TMP_60 \def (\lambda (e2: C).(let TMP_56 \def (Bind Abbr) in (let TMP_57 \def 
(CHead c3 TMP_56 v) in (let TMP_58 \def (Bind Abbr) in (let TMP_59 \def 
(CHead e2 TMP_58 v) in (eq C TMP_57 TMP_59)))))) in (let TMP_61 \def (\lambda 
(e2: C).(csubt g e1 e2)) in (let TMP_62 \def (Bind Abbr) in (let TMP_63 \def 
(CHead c3 TMP_62 v) in (let TMP_64 \def (refl_equal C TMP_63) in (let TMP_65 
\def (ex_intro2 C TMP_60 TMP_61 c3 TMP_64 H10) in (let TMP_66 \def (eq_ind_r 
K TMP_43 TMP_49 TMP_65 k H7) in (eq_ind_r T v TMP_42 TMP_66 u 
H6))))))))))))))))) in (let TMP_68 \def (TMP_67 H5) in (TMP_68 
H4))))))))))))))))))))))))) in (let TMP_82 \def (\lambda (c1: C).(\lambda 
(c3: C).(\lambda (_: (csubt g c1 c3)).(\lambda (_: (((eq C c1 (CHead e1 (Bind 
Abbr) v)) \to (ex2 C (\lambda (e2: C).(eq C c3 (CHead e2 (Bind Abbr) v))) 
(\lambda (e2: C).(csubt g e1 e2)))))).(\lambda (b: B).(\lambda (_: (not (eq B 
b Void))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead c1 
(Bind Void) u1) (CHead e1 (Bind Abbr) v))).(let TMP_70 \def (Bind Void) in 
(let TMP_71 \def (CHead c1 TMP_70 u1) in (let TMP_72 \def (\lambda (ee: 
C).(match ee with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow 
(match k with [(Bind b0) \Rightarrow (match b0 with [Abbr \Rightarrow False | 
Abst \Rightarrow False | Void \Rightarrow True]) | (Flat _) \Rightarrow 
False])])) in (let TMP_73 \def (Bind Abbr) in (let TMP_74 \def (CHead e1 
TMP_73 v) in (let H5 \def (eq_ind C TMP_71 TMP_72 I TMP_74 H4) in (let TMP_79 
\def (\lambda (e2: C).(let TMP_75 \def (Bind b) in (let TMP_76 \def (CHead c3 
TMP_75 u2) in (let TMP_77 \def (Bind Abbr) in (let TMP_78 \def (CHead e2 
TMP_77 v) in (eq C TMP_76 TMP_78)))))) in (let TMP_80 \def (\lambda (e2: 
C).(csubt g e1 e2)) in (let TMP_81 \def (ex2 C TMP_79 TMP_80) in (False_ind 
TMP_81 H5))))))))))))))))))) in (let TMP_95 \def (\lambda (c1: C).(\lambda 
(c3: C).(\lambda (_: (csubt g c1 c3)).(\lambda (_: (((eq C c1 (CHead e1 (Bind 
Abbr) v)) \to (ex2 C (\lambda (e2: C).(eq C c3 (CHead e2 (Bind Abbr) v))) 
(\lambda (e2: C).(csubt g e1 e2)))))).(\lambda (u: T).(\lambda (t: 
T).(\lambda (_: (ty3 g c1 u t)).(\lambda (_: (ty3 g c3 u t)).(\lambda (H5: 
(eq C (CHead c1 (Bind Abst) t) (CHead e1 (Bind Abbr) v))).(let TMP_83 \def 
(Bind Abst) in (let TMP_84 \def (CHead c1 TMP_83 t) in (let TMP_85 \def 
(\lambda (ee: C).(match ee with [(CSort _) \Rightarrow False | (CHead _ k _) 
\Rightarrow (match k with [(Bind b) \Rightarrow (match b with [Abbr 
\Rightarrow False | Abst \Rightarrow True | Void \Rightarrow False]) | (Flat 
_) \Rightarrow False])])) in (let TMP_86 \def (Bind Abbr) in (let TMP_87 \def 
(CHead e1 TMP_86 v) in (let H6 \def (eq_ind C TMP_84 TMP_85 I TMP_87 H5) in 
(let TMP_92 \def (\lambda (e2: C).(let TMP_88 \def (Bind Abbr) in (let TMP_89 
\def (CHead c3 TMP_88 u) in (let TMP_90 \def (Bind Abbr) in (let TMP_91 \def 
(CHead e2 TMP_90 v) in (eq C TMP_89 TMP_91)))))) in (let TMP_93 \def (\lambda 
(e2: C).(csubt g e1 e2)) in (let TMP_94 \def (ex2 C TMP_92 TMP_93) in 
(False_ind TMP_94 H6))))))))))))))))))) in (csubt_ind g TMP_13 TMP_24 TMP_69 
TMP_82 TMP_95 y c2 H0)))))))) in (insert_eq C TMP_2 TMP_3 TMP_8 TMP_96 
H)))))))))).

theorem csubt_gen_abst:
 \forall (g: G).(\forall (e1: C).(\forall (c2: C).(\forall (v1: T).((csubt g 
(CHead e1 (Bind Abst) v1) c2) \to (or (ex2 C (\lambda (e2: C).(eq C c2 (CHead 
e2 (Bind Abst) v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex4_2 C T (\lambda 
(e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (_: C).(\lambda (v2: T).(ty3 g 
e1 v2 v1))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1)))))))))
\def
 \lambda (g: G).(\lambda (e1: C).(\lambda (c2: C).(\lambda (v1: T).(\lambda 
(H: (csubt g (CHead e1 (Bind Abst) v1) c2)).(let TMP_1 \def (Bind Abst) in 
(let TMP_2 \def (CHead e1 TMP_1 v1) in (let TMP_3 \def (\lambda (c: C).(csubt 
g c c2)) in (let TMP_16 \def (\lambda (_: C).(let TMP_6 \def (\lambda (e2: 
C).(let TMP_4 \def (Bind Abst) in (let TMP_5 \def (CHead e2 TMP_4 v1) in (eq 
C c2 TMP_5)))) in (let TMP_7 \def (\lambda (e2: C).(csubt g e1 e2)) in (let 
TMP_8 \def (ex2 C TMP_6 TMP_7) in (let TMP_11 \def (\lambda (e2: C).(\lambda 
(v2: T).(let TMP_9 \def (Bind Abbr) in (let TMP_10 \def (CHead e2 TMP_9 v2) 
in (eq C c2 TMP_10))))) in (let TMP_12 \def (\lambda (e2: C).(\lambda (_: 
T).(csubt g e1 e2))) in (let TMP_13 \def (\lambda (_: C).(\lambda (v2: 
T).(ty3 g e1 v2 v1))) in (let TMP_14 \def (\lambda (e2: C).(\lambda (v2: 
T).(ty3 g e2 v2 v1))) in (let TMP_15 \def (ex4_2 C T TMP_11 TMP_12 TMP_13 
TMP_14) in (or TMP_8 TMP_15)))))))))) in (let TMP_218 \def (\lambda (y: 
C).(\lambda (H0: (csubt g y c2)).(let TMP_29 \def (\lambda (c: C).(\lambda 
(c0: C).((eq C c (CHead e1 (Bind Abst) v1)) \to (let TMP_19 \def (\lambda 
(e2: C).(let TMP_17 \def (Bind Abst) in (let TMP_18 \def (CHead e2 TMP_17 v1) 
in (eq C c0 TMP_18)))) in (let TMP_20 \def (\lambda (e2: C).(csubt g e1 e2)) 
in (let TMP_21 \def (ex2 C TMP_19 TMP_20) in (let TMP_24 \def (\lambda (e2: 
C).(\lambda (v2: T).(let TMP_22 \def (Bind Abbr) in (let TMP_23 \def (CHead 
e2 TMP_22 v2) in (eq C c0 TMP_23))))) in (let TMP_25 \def (\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2))) in (let TMP_26 \def (\lambda (_: 
C).(\lambda (v2: T).(ty3 g e1 v2 v1))) in (let TMP_27 \def (\lambda (e2: 
C).(\lambda (v2: T).(ty3 g e2 v2 v1))) in (let TMP_28 \def (ex4_2 C T TMP_24 
TMP_25 TMP_26 TMP_27) in (or TMP_21 TMP_28)))))))))))) in (let TMP_49 \def 
(\lambda (n: nat).(\lambda (H1: (eq C (CSort n) (CHead e1 (Bind Abst) 
v1))).(let TMP_30 \def (CSort n) in (let TMP_31 \def (\lambda (ee: C).(match 
ee with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow False])) in 
(let TMP_32 \def (Bind Abst) in (let TMP_33 \def (CHead e1 TMP_32 v1) in (let 
H2 \def (eq_ind C TMP_30 TMP_31 I TMP_33 H1) in (let TMP_37 \def (\lambda 
(e2: C).(let TMP_34 \def (CSort n) in (let TMP_35 \def (Bind Abst) in (let 
TMP_36 \def (CHead e2 TMP_35 v1) in (eq C TMP_34 TMP_36))))) in (let TMP_38 
\def (\lambda (e2: C).(csubt g e1 e2)) in (let TMP_39 \def (ex2 C TMP_37 
TMP_38) in (let TMP_43 \def (\lambda (e2: C).(\lambda (v2: T).(let TMP_40 
\def (CSort n) in (let TMP_41 \def (Bind Abbr) in (let TMP_42 \def (CHead e2 
TMP_41 v2) in (eq C TMP_40 TMP_42)))))) in (let TMP_44 \def (\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2))) in (let TMP_45 \def (\lambda (_: 
C).(\lambda (v2: T).(ty3 g e1 v2 v1))) in (let TMP_46 \def (\lambda (e2: 
C).(\lambda (v2: T).(ty3 g e2 v2 v1))) in (let TMP_47 \def (ex4_2 C T TMP_43 
TMP_44 TMP_45 TMP_46) in (let TMP_48 \def (or TMP_39 TMP_47) in (False_ind 
TMP_48 H2))))))))))))))))) in (let TMP_137 \def (\lambda (c1: C).(\lambda 
(c3: C).(\lambda (H1: (csubt g c1 c3)).(\lambda (H2: (((eq C c1 (CHead e1 
(Bind Abst) v1)) \to (or (ex2 C (\lambda (e2: C).(eq C c3 (CHead e2 (Bind 
Abst) v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex4_2 C T (\lambda (e2: 
C).(\lambda (v2: T).(eq C c3 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (_: C).(\lambda (v2: T).(ty3 g 
e1 v2 v1))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 
v1)))))))).(\lambda (k: K).(\lambda (u: T).(\lambda (H3: (eq C (CHead c1 k u) 
(CHead e1 (Bind Abst) v1))).(let TMP_50 \def (\lambda (e: C).(match e with 
[(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) in (let TMP_51 
\def (CHead c1 k u) in (let TMP_52 \def (Bind Abst) in (let TMP_53 \def 
(CHead e1 TMP_52 v1) in (let H4 \def (f_equal C C TMP_50 TMP_51 TMP_53 H3) in 
(let TMP_54 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow k | 
(CHead _ k0 _) \Rightarrow k0])) in (let TMP_55 \def (CHead c1 k u) in (let 
TMP_56 \def (Bind Abst) in (let TMP_57 \def (CHead e1 TMP_56 v1) in (let H5 
\def (f_equal C K TMP_54 TMP_55 TMP_57 H3) in (let TMP_58 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) in 
(let TMP_59 \def (CHead c1 k u) in (let TMP_60 \def (Bind Abst) in (let 
TMP_61 \def (CHead e1 TMP_60 v1) in (let H6 \def (f_equal C T TMP_58 TMP_59 
TMP_61 H3) in (let TMP_135 \def (\lambda (H7: (eq K k (Bind Abst))).(\lambda 
(H8: (eq C c1 e1)).(let TMP_76 \def (\lambda (t: T).(let TMP_65 \def (\lambda 
(e2: C).(let TMP_62 \def (CHead c3 k t) in (let TMP_63 \def (Bind Abst) in 
(let TMP_64 \def (CHead e2 TMP_63 v1) in (eq C TMP_62 TMP_64))))) in (let 
TMP_66 \def (\lambda (e2: C).(csubt g e1 e2)) in (let TMP_67 \def (ex2 C 
TMP_65 TMP_66) in (let TMP_71 \def (\lambda (e2: C).(\lambda (v2: T).(let 
TMP_68 \def (CHead c3 k t) in (let TMP_69 \def (Bind Abbr) in (let TMP_70 
\def (CHead e2 TMP_69 v2) in (eq C TMP_68 TMP_70)))))) in (let TMP_72 \def 
(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2))) in (let TMP_73 \def 
(\lambda (_: C).(\lambda (v2: T).(ty3 g e1 v2 v1))) in (let TMP_74 \def 
(\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1))) in (let TMP_75 \def 
(ex4_2 C T TMP_71 TMP_72 TMP_73 TMP_74) in (or TMP_67 TMP_75)))))))))) in 
(let TMP_77 \def (Bind Abst) in (let TMP_92 \def (\lambda (k0: K).(let TMP_81 
\def (\lambda (e2: C).(let TMP_78 \def (CHead c3 k0 v1) in (let TMP_79 \def 
(Bind Abst) in (let TMP_80 \def (CHead e2 TMP_79 v1) in (eq C TMP_78 
TMP_80))))) in (let TMP_82 \def (\lambda (e2: C).(csubt g e1 e2)) in (let 
TMP_83 \def (ex2 C TMP_81 TMP_82) in (let TMP_87 \def (\lambda (e2: 
C).(\lambda (v2: T).(let TMP_84 \def (CHead c3 k0 v1) in (let TMP_85 \def 
(Bind Abbr) in (let TMP_86 \def (CHead e2 TMP_85 v2) in (eq C TMP_84 
TMP_86)))))) in (let TMP_88 \def (\lambda (e2: C).(\lambda (_: T).(csubt g e1 
e2))) in (let TMP_89 \def (\lambda (_: C).(\lambda (v2: T).(ty3 g e1 v2 v1))) 
in (let TMP_90 \def (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1))) in 
(let TMP_91 \def (ex4_2 C T TMP_87 TMP_88 TMP_89 TMP_90) in (or TMP_83 
TMP_91)))))))))) in (let TMP_105 \def (\lambda (c: C).((eq C c (CHead e1 
(Bind Abst) v1)) \to (let TMP_95 \def (\lambda (e2: C).(let TMP_93 \def (Bind 
Abst) in (let TMP_94 \def (CHead e2 TMP_93 v1) in (eq C c3 TMP_94)))) in (let 
TMP_96 \def (\lambda (e2: C).(csubt g e1 e2)) in (let TMP_97 \def (ex2 C 
TMP_95 TMP_96) in (let TMP_100 \def (\lambda (e2: C).(\lambda (v2: T).(let 
TMP_98 \def (Bind Abbr) in (let TMP_99 \def (CHead e2 TMP_98 v2) in (eq C c3 
TMP_99))))) in (let TMP_101 \def (\lambda (e2: C).(\lambda (_: T).(csubt g e1 
e2))) in (let TMP_102 \def (\lambda (_: C).(\lambda (v2: T).(ty3 g e1 v2 
v1))) in (let TMP_103 \def (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 
v1))) in (let TMP_104 \def (ex4_2 C T TMP_100 TMP_101 TMP_102 TMP_103) in (or 
TMP_97 TMP_104))))))))))) in (let H9 \def (eq_ind C c1 TMP_105 H2 e1 H8) in 
(let TMP_106 \def (\lambda (c: C).(csubt g c c3)) in (let H10 \def (eq_ind C 
c1 TMP_106 H1 e1 H8) in (let TMP_111 \def (\lambda (e2: C).(let TMP_107 \def 
(Bind Abst) in (let TMP_108 \def (CHead c3 TMP_107 v1) in (let TMP_109 \def 
(Bind Abst) in (let TMP_110 \def (CHead e2 TMP_109 v1) in (eq C TMP_108 
TMP_110)))))) in (let TMP_112 \def (\lambda (e2: C).(csubt g e1 e2)) in (let 
TMP_113 \def (ex2 C TMP_111 TMP_112) in (let TMP_118 \def (\lambda (e2: 
C).(\lambda (v2: T).(let TMP_114 \def (Bind Abst) in (let TMP_115 \def (CHead 
c3 TMP_114 v1) in (let TMP_116 \def (Bind Abbr) in (let TMP_117 \def (CHead 
e2 TMP_116 v2) in (eq C TMP_115 TMP_117))))))) in (let TMP_119 \def (\lambda 
(e2: C).(\lambda (_: T).(csubt g e1 e2))) in (let TMP_120 \def (\lambda (_: 
C).(\lambda (v2: T).(ty3 g e1 v2 v1))) in (let TMP_121 \def (\lambda (e2: 
C).(\lambda (v2: T).(ty3 g e2 v2 v1))) in (let TMP_122 \def (ex4_2 C T 
TMP_118 TMP_119 TMP_120 TMP_121) in (let TMP_127 \def (\lambda (e2: C).(let 
TMP_123 \def (Bind Abst) in (let TMP_124 \def (CHead c3 TMP_123 v1) in (let 
TMP_125 \def (Bind Abst) in (let TMP_126 \def (CHead e2 TMP_125 v1) in (eq C 
TMP_124 TMP_126)))))) in (let TMP_128 \def (\lambda (e2: C).(csubt g e1 e2)) 
in (let TMP_129 \def (Bind Abst) in (let TMP_130 \def (CHead c3 TMP_129 v1) 
in (let TMP_131 \def (refl_equal C TMP_130) in (let TMP_132 \def (ex_intro2 C 
TMP_127 TMP_128 c3 TMP_131 H10) in (let TMP_133 \def (or_introl TMP_113 
TMP_122 TMP_132) in (let TMP_134 \def (eq_ind_r K TMP_77 TMP_92 TMP_133 k H7) 
in (eq_ind_r T v1 TMP_76 TMP_134 u H6)))))))))))))))))))))))))) in (let 
TMP_136 \def (TMP_135 H5) in (TMP_136 H4))))))))))))))))))))))))) in (let 
TMP_160 \def (\lambda (c1: C).(\lambda (c3: C).(\lambda (_: (csubt g c1 
c3)).(\lambda (_: (((eq C c1 (CHead e1 (Bind Abst) v1)) \to (or (ex2 C 
(\lambda (e2: C).(eq C c3 (CHead e2 (Bind Abst) v1))) (\lambda (e2: C).(csubt 
g e1 e2))) (ex4_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C c3 (CHead e2 
(Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2))) 
(\lambda (_: C).(\lambda (v2: T).(ty3 g e1 v2 v1))) (\lambda (e2: C).(\lambda 
(v2: T).(ty3 g e2 v2 v1)))))))).(\lambda (b: B).(\lambda (_: (not (eq B b 
Void))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead c1 (Bind 
Void) u1) (CHead e1 (Bind Abst) v1))).(let TMP_138 \def (Bind Void) in (let 
TMP_139 \def (CHead c1 TMP_138 u1) in (let TMP_140 \def (\lambda (ee: 
C).(match ee with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow 
(match k with [(Bind b0) \Rightarrow (match b0 with [Abbr \Rightarrow False | 
Abst \Rightarrow False | Void \Rightarrow True]) | (Flat _) \Rightarrow 
False])])) in (let TMP_141 \def (Bind Abst) in (let TMP_142 \def (CHead e1 
TMP_141 v1) in (let H5 \def (eq_ind C TMP_139 TMP_140 I TMP_142 H4) in (let 
TMP_147 \def (\lambda (e2: C).(let TMP_143 \def (Bind b) in (let TMP_144 \def 
(CHead c3 TMP_143 u2) in (let TMP_145 \def (Bind Abst) in (let TMP_146 \def 
(CHead e2 TMP_145 v1) in (eq C TMP_144 TMP_146)))))) in (let TMP_148 \def 
(\lambda (e2: C).(csubt g e1 e2)) in (let TMP_149 \def (ex2 C TMP_147 
TMP_148) in (let TMP_154 \def (\lambda (e2: C).(\lambda (v2: T).(let TMP_150 
\def (Bind b) in (let TMP_151 \def (CHead c3 TMP_150 u2) in (let TMP_152 \def 
(Bind Abbr) in (let TMP_153 \def (CHead e2 TMP_152 v2) in (eq C TMP_151 
TMP_153))))))) in (let TMP_155 \def (\lambda (e2: C).(\lambda (_: T).(csubt g 
e1 e2))) in (let TMP_156 \def (\lambda (_: C).(\lambda (v2: T).(ty3 g e1 v2 
v1))) in (let TMP_157 \def (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 
v1))) in (let TMP_158 \def (ex4_2 C T TMP_154 TMP_155 TMP_156 TMP_157) in 
(let TMP_159 \def (or TMP_149 TMP_158) in (False_ind TMP_159 
H5))))))))))))))))))))))))) in (let TMP_217 \def (\lambda (c1: C).(\lambda 
(c3: C).(\lambda (H1: (csubt g c1 c3)).(\lambda (H2: (((eq C c1 (CHead e1 
(Bind Abst) v1)) \to (or (ex2 C (\lambda (e2: C).(eq C c3 (CHead e2 (Bind 
Abst) v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex4_2 C T (\lambda (e2: 
C).(\lambda (v2: T).(eq C c3 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (_: C).(\lambda (v2: T).(ty3 g 
e1 v2 v1))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 
v1)))))))).(\lambda (u: T).(\lambda (t: T).(\lambda (H3: (ty3 g c1 u 
t)).(\lambda (H4: (ty3 g c3 u t)).(\lambda (H5: (eq C (CHead c1 (Bind Abst) 
t) (CHead e1 (Bind Abst) v1))).(let TMP_161 \def (\lambda (e: C).(match e 
with [(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) in (let 
TMP_162 \def (Bind Abst) in (let TMP_163 \def (CHead c1 TMP_162 t) in (let 
TMP_164 \def (Bind Abst) in (let TMP_165 \def (CHead e1 TMP_164 v1) in (let 
H6 \def (f_equal C C TMP_161 TMP_163 TMP_165 H5) in (let TMP_166 \def 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow t | (CHead _ _ t0) 
\Rightarrow t0])) in (let TMP_167 \def (Bind Abst) in (let TMP_168 \def 
(CHead c1 TMP_167 t) in (let TMP_169 \def (Bind Abst) in (let TMP_170 \def 
(CHead e1 TMP_169 v1) in (let H7 \def (f_equal C T TMP_166 TMP_168 TMP_170 
H5) in (let TMP_216 \def (\lambda (H8: (eq C c1 e1)).(let TMP_171 \def 
(\lambda (t0: T).(ty3 g c3 u t0)) in (let H9 \def (eq_ind T t TMP_171 H4 v1 
H7) in (let TMP_172 \def (\lambda (t0: T).(ty3 g c1 u t0)) in (let H10 \def 
(eq_ind T t TMP_172 H3 v1 H7) in (let TMP_173 \def (\lambda (c: C).(ty3 g c u 
v1)) in (let H11 \def (eq_ind C c1 TMP_173 H10 e1 H8) in (let TMP_186 \def 
(\lambda (c: C).((eq C c (CHead e1 (Bind Abst) v1)) \to (let TMP_176 \def 
(\lambda (e2: C).(let TMP_174 \def (Bind Abst) in (let TMP_175 \def (CHead e2 
TMP_174 v1) in (eq C c3 TMP_175)))) in (let TMP_177 \def (\lambda (e2: 
C).(csubt g e1 e2)) in (let TMP_178 \def (ex2 C TMP_176 TMP_177) in (let 
TMP_181 \def (\lambda (e2: C).(\lambda (v2: T).(let TMP_179 \def (Bind Abbr) 
in (let TMP_180 \def (CHead e2 TMP_179 v2) in (eq C c3 TMP_180))))) in (let 
TMP_182 \def (\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2))) in (let 
TMP_183 \def (\lambda (_: C).(\lambda (v2: T).(ty3 g e1 v2 v1))) in (let 
TMP_184 \def (\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 v1))) in (let 
TMP_185 \def (ex4_2 C T TMP_181 TMP_182 TMP_183 TMP_184) in (or TMP_178 
TMP_185))))))))))) in (let H12 \def (eq_ind C c1 TMP_186 H2 e1 H8) in (let 
TMP_187 \def (\lambda (c: C).(csubt g c c3)) in (let H13 \def (eq_ind C c1 
TMP_187 H1 e1 H8) in (let TMP_192 \def (\lambda (e2: C).(let TMP_188 \def 
(Bind Abbr) in (let TMP_189 \def (CHead c3 TMP_188 u) in (let TMP_190 \def 
(Bind Abst) in (let TMP_191 \def (CHead e2 TMP_190 v1) in (eq C TMP_189 
TMP_191)))))) in (let TMP_193 \def (\lambda (e2: C).(csubt g e1 e2)) in (let 
TMP_194 \def (ex2 C TMP_192 TMP_193) in (let TMP_199 \def (\lambda (e2: 
C).(\lambda (v2: T).(let TMP_195 \def (Bind Abbr) in (let TMP_196 \def (CHead 
c3 TMP_195 u) in (let TMP_197 \def (Bind Abbr) in (let TMP_198 \def (CHead e2 
TMP_197 v2) in (eq C TMP_196 TMP_198))))))) in (let TMP_200 \def (\lambda 
(e2: C).(\lambda (_: T).(csubt g e1 e2))) in (let TMP_201 \def (\lambda (_: 
C).(\lambda (v2: T).(ty3 g e1 v2 v1))) in (let TMP_202 \def (\lambda (e2: 
C).(\lambda (v2: T).(ty3 g e2 v2 v1))) in (let TMP_203 \def (ex4_2 C T 
TMP_199 TMP_200 TMP_201 TMP_202) in (let TMP_208 \def (\lambda (e2: 
C).(\lambda (v2: T).(let TMP_204 \def (Bind Abbr) in (let TMP_205 \def (CHead 
c3 TMP_204 u) in (let TMP_206 \def (Bind Abbr) in (let TMP_207 \def (CHead e2 
TMP_206 v2) in (eq C TMP_205 TMP_207))))))) in (let TMP_209 \def (\lambda 
(e2: C).(\lambda (_: T).(csubt g e1 e2))) in (let TMP_210 \def (\lambda (_: 
C).(\lambda (v2: T).(ty3 g e1 v2 v1))) in (let TMP_211 \def (\lambda (e2: 
C).(\lambda (v2: T).(ty3 g e2 v2 v1))) in (let TMP_212 \def (Bind Abbr) in 
(let TMP_213 \def (CHead c3 TMP_212 u) in (let TMP_214 \def (refl_equal C 
TMP_213) in (let TMP_215 \def (ex4_2_intro C T TMP_208 TMP_209 TMP_210 
TMP_211 c3 u TMP_214 H13 H11 H9) in (or_intror TMP_194 TMP_203 
TMP_215)))))))))))))))))))))))))))) in (TMP_216 H6))))))))))))))))))))))) in 
(csubt_ind g TMP_29 TMP_49 TMP_137 TMP_160 TMP_217 y c2 H0)))))))) in 
(insert_eq C TMP_2 TMP_3 TMP_16 TMP_218 H)))))))))).

theorem csubt_gen_flat:
 \forall (g: G).(\forall (e1: C).(\forall (c2: C).(\forall (v: T).(\forall 
(f: F).((csubt g (CHead e1 (Flat f) v) c2) \to (ex2 C (\lambda (e2: C).(eq C 
c2 (CHead e2 (Flat f) v))) (\lambda (e2: C).(csubt g e1 e2))))))))
\def
 \lambda (g: G).(\lambda (e1: C).(\lambda (c2: C).(\lambda (v: T).(\lambda 
(f: F).(\lambda (H: (csubt g (CHead e1 (Flat f) v) c2)).(let TMP_1 \def (Flat 
f) in (let TMP_2 \def (CHead e1 TMP_1 v) in (let TMP_3 \def (\lambda (c: 
C).(csubt g c c2)) in (let TMP_8 \def (\lambda (_: C).(let TMP_6 \def 
(\lambda (e2: C).(let TMP_4 \def (Flat f) in (let TMP_5 \def (CHead e2 TMP_4 
v) in (eq C c2 TMP_5)))) in (let TMP_7 \def (\lambda (e2: C).(csubt g e1 e2)) 
in (ex2 C TMP_6 TMP_7)))) in (let TMP_96 \def (\lambda (y: C).(\lambda (H0: 
(csubt g y c2)).(let TMP_13 \def (\lambda (c: C).(\lambda (c0: C).((eq C c 
(CHead e1 (Flat f) v)) \to (let TMP_11 \def (\lambda (e2: C).(let TMP_9 \def 
(Flat f) in (let TMP_10 \def (CHead e2 TMP_9 v) in (eq C c0 TMP_10)))) in 
(let TMP_12 \def (\lambda (e2: C).(csubt g e1 e2)) in (ex2 C TMP_11 
TMP_12)))))) in (let TMP_24 \def (\lambda (n: nat).(\lambda (H1: (eq C (CSort 
n) (CHead e1 (Flat f) v))).(let TMP_14 \def (CSort n) in (let TMP_15 \def 
(\lambda (ee: C).(match ee with [(CSort _) \Rightarrow True | (CHead _ _ _) 
\Rightarrow False])) in (let TMP_16 \def (Flat f) in (let TMP_17 \def (CHead 
e1 TMP_16 v) in (let H2 \def (eq_ind C TMP_14 TMP_15 I TMP_17 H1) in (let 
TMP_21 \def (\lambda (e2: C).(let TMP_18 \def (CSort n) in (let TMP_19 \def 
(Flat f) in (let TMP_20 \def (CHead e2 TMP_19 v) in (eq C TMP_18 TMP_20))))) 
in (let TMP_22 \def (\lambda (e2: C).(csubt g e1 e2)) in (let TMP_23 \def 
(ex2 C TMP_21 TMP_22) in (False_ind TMP_23 H2))))))))))) in (let TMP_69 \def 
(\lambda (c1: C).(\lambda (c3: C).(\lambda (H1: (csubt g c1 c3)).(\lambda 
(H2: (((eq C c1 (CHead e1 (Flat f) v)) \to (ex2 C (\lambda (e2: C).(eq C c3 
(CHead e2 (Flat f) v))) (\lambda (e2: C).(csubt g e1 e2)))))).(\lambda (k: 
K).(\lambda (u: T).(\lambda (H3: (eq C (CHead c1 k u) (CHead e1 (Flat f) 
v))).(let TMP_25 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow c1 
| (CHead c _ _) \Rightarrow c])) in (let TMP_26 \def (CHead c1 k u) in (let 
TMP_27 \def (Flat f) in (let TMP_28 \def (CHead e1 TMP_27 v) in (let H4 \def 
(f_equal C C TMP_25 TMP_26 TMP_28 H3) in (let TMP_29 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow k | (CHead _ k0 _) \Rightarrow k0])) 
in (let TMP_30 \def (CHead c1 k u) in (let TMP_31 \def (Flat f) in (let 
TMP_32 \def (CHead e1 TMP_31 v) in (let H5 \def (f_equal C K TMP_29 TMP_30 
TMP_32 H3) in (let TMP_33 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow u | (CHead _ _ t) \Rightarrow t])) in (let TMP_34 \def (CHead c1 
k u) in (let TMP_35 \def (Flat f) in (let TMP_36 \def (CHead e1 TMP_35 v) in 
(let H6 \def (f_equal C T TMP_33 TMP_34 TMP_36 H3) in (let TMP_67 \def 
(\lambda (H7: (eq K k (Flat f))).(\lambda (H8: (eq C c1 e1)).(let TMP_42 \def 
(\lambda (t: T).(let TMP_40 \def (\lambda (e2: C).(let TMP_37 \def (CHead c3 
k t) in (let TMP_38 \def (Flat f) in (let TMP_39 \def (CHead e2 TMP_38 v) in 
(eq C TMP_37 TMP_39))))) in (let TMP_41 \def (\lambda (e2: C).(csubt g e1 
e2)) in (ex2 C TMP_40 TMP_41)))) in (let TMP_43 \def (Flat f) in (let TMP_49 
\def (\lambda (k0: K).(let TMP_47 \def (\lambda (e2: C).(let TMP_44 \def 
(CHead c3 k0 v) in (let TMP_45 \def (Flat f) in (let TMP_46 \def (CHead e2 
TMP_45 v) in (eq C TMP_44 TMP_46))))) in (let TMP_48 \def (\lambda (e2: 
C).(csubt g e1 e2)) in (ex2 C TMP_47 TMP_48)))) in (let TMP_54 \def (\lambda 
(c: C).((eq C c (CHead e1 (Flat f) v)) \to (let TMP_52 \def (\lambda (e2: 
C).(let TMP_50 \def (Flat f) in (let TMP_51 \def (CHead e2 TMP_50 v) in (eq C 
c3 TMP_51)))) in (let TMP_53 \def (\lambda (e2: C).(csubt g e1 e2)) in (ex2 C 
TMP_52 TMP_53))))) in (let H9 \def (eq_ind C c1 TMP_54 H2 e1 H8) in (let 
TMP_55 \def (\lambda (c: C).(csubt g c c3)) in (let H10 \def (eq_ind C c1 
TMP_55 H1 e1 H8) in (let TMP_60 \def (\lambda (e2: C).(let TMP_56 \def (Flat 
f) in (let TMP_57 \def (CHead c3 TMP_56 v) in (let TMP_58 \def (Flat f) in 
(let TMP_59 \def (CHead e2 TMP_58 v) in (eq C TMP_57 TMP_59)))))) in (let 
TMP_61 \def (\lambda (e2: C).(csubt g e1 e2)) in (let TMP_62 \def (Flat f) in 
(let TMP_63 \def (CHead c3 TMP_62 v) in (let TMP_64 \def (refl_equal C 
TMP_63) in (let TMP_65 \def (ex_intro2 C TMP_60 TMP_61 c3 TMP_64 H10) in (let 
TMP_66 \def (eq_ind_r K TMP_43 TMP_49 TMP_65 k H7) in (eq_ind_r T v TMP_42 
TMP_66 u H6))))))))))))))))) in (let TMP_68 \def (TMP_67 H5) in (TMP_68 
H4))))))))))))))))))))))))) in (let TMP_82 \def (\lambda (c1: C).(\lambda 
(c3: C).(\lambda (_: (csubt g c1 c3)).(\lambda (_: (((eq C c1 (CHead e1 (Flat 
f) v)) \to (ex2 C (\lambda (e2: C).(eq C c3 (CHead e2 (Flat f) v))) (\lambda 
(e2: C).(csubt g e1 e2)))))).(\lambda (b: B).(\lambda (_: (not (eq B b 
Void))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead c1 (Bind 
Void) u1) (CHead e1 (Flat f) v))).(let TMP_70 \def (Bind Void) in (let TMP_71 
\def (CHead c1 TMP_70 u1) in (let TMP_72 \def (\lambda (ee: C).(match ee with 
[(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match k with [(Bind 
_) \Rightarrow True | (Flat _) \Rightarrow False])])) in (let TMP_73 \def 
(Flat f) in (let TMP_74 \def (CHead e1 TMP_73 v) in (let H5 \def (eq_ind C 
TMP_71 TMP_72 I TMP_74 H4) in (let TMP_79 \def (\lambda (e2: C).(let TMP_75 
\def (Bind b) in (let TMP_76 \def (CHead c3 TMP_75 u2) in (let TMP_77 \def 
(Flat f) in (let TMP_78 \def (CHead e2 TMP_77 v) in (eq C TMP_76 TMP_78)))))) 
in (let TMP_80 \def (\lambda (e2: C).(csubt g e1 e2)) in (let TMP_81 \def 
(ex2 C TMP_79 TMP_80) in (False_ind TMP_81 H5))))))))))))))))))) in (let 
TMP_95 \def (\lambda (c1: C).(\lambda (c3: C).(\lambda (_: (csubt g c1 
c3)).(\lambda (_: (((eq C c1 (CHead e1 (Flat f) v)) \to (ex2 C (\lambda (e2: 
C).(eq C c3 (CHead e2 (Flat f) v))) (\lambda (e2: C).(csubt g e1 
e2)))))).(\lambda (u: T).(\lambda (t: T).(\lambda (_: (ty3 g c1 u 
t)).(\lambda (_: (ty3 g c3 u t)).(\lambda (H5: (eq C (CHead c1 (Bind Abst) t) 
(CHead e1 (Flat f) v))).(let TMP_83 \def (Bind Abst) in (let TMP_84 \def 
(CHead c1 TMP_83 t) in (let TMP_85 \def (\lambda (ee: C).(match ee with 
[(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match k with [(Bind 
_) \Rightarrow True | (Flat _) \Rightarrow False])])) in (let TMP_86 \def 
(Flat f) in (let TMP_87 \def (CHead e1 TMP_86 v) in (let H6 \def (eq_ind C 
TMP_84 TMP_85 I TMP_87 H5) in (let TMP_92 \def (\lambda (e2: C).(let TMP_88 
\def (Bind Abbr) in (let TMP_89 \def (CHead c3 TMP_88 u) in (let TMP_90 \def 
(Flat f) in (let TMP_91 \def (CHead e2 TMP_90 v) in (eq C TMP_89 TMP_91)))))) 
in (let TMP_93 \def (\lambda (e2: C).(csubt g e1 e2)) in (let TMP_94 \def 
(ex2 C TMP_92 TMP_93) in (False_ind TMP_94 H6))))))))))))))))))) in 
(csubt_ind g TMP_13 TMP_24 TMP_69 TMP_82 TMP_95 y c2 H0)))))))) in (insert_eq 
C TMP_2 TMP_3 TMP_8 TMP_96 H))))))))))).

theorem csubt_gen_bind:
 \forall (g: G).(\forall (b1: B).(\forall (e1: C).(\forall (c2: C).(\forall 
(v1: T).((csubt g (CHead e1 (Bind b1) v1) c2) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2))))))))))
\def
 \lambda (g: G).(\lambda (b1: B).(\lambda (e1: C).(\lambda (c2: C).(\lambda 
(v1: T).(\lambda (H: (csubt g (CHead e1 (Bind b1) v1) c2)).(let TMP_1 \def 
(Bind b1) in (let TMP_2 \def (CHead e1 TMP_1 v1) in (let TMP_3 \def (\lambda 
(c: C).(csubt g c c2)) in (let TMP_8 \def (\lambda (_: C).(let TMP_6 \def 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(let TMP_4 \def (Bind b2) 
in (let TMP_5 \def (CHead e2 TMP_4 v2) in (eq C c2 TMP_5)))))) in (let TMP_7 
\def (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2)))) in 
(ex2_3 B C T TMP_6 TMP_7)))) in (let TMP_149 \def (\lambda (y: C).(\lambda 
(H0: (csubt g y c2)).(let TMP_13 \def (\lambda (c: C).(\lambda (c0: C).((eq C 
c (CHead e1 (Bind b1) v1)) \to (let TMP_11 \def (\lambda (b2: B).(\lambda 
(e2: C).(\lambda (v2: T).(let TMP_9 \def (Bind b2) in (let TMP_10 \def (CHead 
e2 TMP_9 v2) in (eq C c0 TMP_10)))))) in (let TMP_12 \def (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2)))) in (ex2_3 B C T TMP_11 
TMP_12)))))) in (let TMP_24 \def (\lambda (n: nat).(\lambda (H1: (eq C (CSort 
n) (CHead e1 (Bind b1) v1))).(let TMP_14 \def (CSort n) in (let TMP_15 \def 
(\lambda (ee: C).(match ee with [(CSort _) \Rightarrow True | (CHead _ _ _) 
\Rightarrow False])) in (let TMP_16 \def (Bind b1) in (let TMP_17 \def (CHead 
e1 TMP_16 v1) in (let H2 \def (eq_ind C TMP_14 TMP_15 I TMP_17 H1) in (let 
TMP_21 \def (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(let TMP_18 
\def (CSort n) in (let TMP_19 \def (Bind b2) in (let TMP_20 \def (CHead e2 
TMP_19 v2) in (eq C TMP_18 TMP_20))))))) in (let TMP_22 \def (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2)))) in (let TMP_23 \def 
(ex2_3 B C T TMP_21 TMP_22) in (False_ind TMP_23 H2))))))))))) in (let TMP_69 
\def (\lambda (c1: C).(\lambda (c3: C).(\lambda (H1: (csubt g c1 
c3)).(\lambda (H2: (((eq C c1 (CHead e1 (Bind b1) v1)) \to (ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c3 (CHead e2 (Bind 
b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 
e2)))))))).(\lambda (k: K).(\lambda (u: T).(\lambda (H3: (eq C (CHead c1 k u) 
(CHead e1 (Bind b1) v1))).(let TMP_25 \def (\lambda (e: C).(match e with 
[(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) in (let TMP_26 
\def (CHead c1 k u) in (let TMP_27 \def (Bind b1) in (let TMP_28 \def (CHead 
e1 TMP_27 v1) in (let H4 \def (f_equal C C TMP_25 TMP_26 TMP_28 H3) in (let 
TMP_29 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow k | (CHead _ 
k0 _) \Rightarrow k0])) in (let TMP_30 \def (CHead c1 k u) in (let TMP_31 
\def (Bind b1) in (let TMP_32 \def (CHead e1 TMP_31 v1) in (let H5 \def 
(f_equal C K TMP_29 TMP_30 TMP_32 H3) in (let TMP_33 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) in 
(let TMP_34 \def (CHead c1 k u) in (let TMP_35 \def (Bind b1) in (let TMP_36 
\def (CHead e1 TMP_35 v1) in (let H6 \def (f_equal C T TMP_33 TMP_34 TMP_36 
H3) in (let TMP_67 \def (\lambda (H7: (eq K k (Bind b1))).(\lambda (H8: (eq C 
c1 e1)).(let TMP_42 \def (\lambda (t: T).(let TMP_40 \def (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(let TMP_37 \def (CHead c3 k t) in (let 
TMP_38 \def (Bind b2) in (let TMP_39 \def (CHead e2 TMP_38 v2) in (eq C 
TMP_37 TMP_39))))))) in (let TMP_41 \def (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2)))) in (ex2_3 B C T TMP_40 TMP_41)))) in 
(let TMP_43 \def (Bind b1) in (let TMP_49 \def (\lambda (k0: K).(let TMP_47 
\def (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(let TMP_44 \def 
(CHead c3 k0 v1) in (let TMP_45 \def (Bind b2) in (let TMP_46 \def (CHead e2 
TMP_45 v2) in (eq C TMP_44 TMP_46))))))) in (let TMP_48 \def (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2)))) in (ex2_3 B C T TMP_47 
TMP_48)))) in (let TMP_54 \def (\lambda (c: C).((eq C c (CHead e1 (Bind b1) 
v1)) \to (let TMP_52 \def (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: 
T).(let TMP_50 \def (Bind b2) in (let TMP_51 \def (CHead e2 TMP_50 v2) in (eq 
C c3 TMP_51)))))) in (let TMP_53 \def (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2)))) in (ex2_3 B C T TMP_52 TMP_53))))) in 
(let H9 \def (eq_ind C c1 TMP_54 H2 e1 H8) in (let TMP_55 \def (\lambda (c: 
C).(csubt g c c3)) in (let H10 \def (eq_ind C c1 TMP_55 H1 e1 H8) in (let 
TMP_60 \def (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(let TMP_56 
\def (Bind b1) in (let TMP_57 \def (CHead c3 TMP_56 v1) in (let TMP_58 \def 
(Bind b2) in (let TMP_59 \def (CHead e2 TMP_58 v2) in (eq C TMP_57 
TMP_59)))))))) in (let TMP_61 \def (\lambda (_: B).(\lambda (e2: C).(\lambda 
(_: T).(csubt g e1 e2)))) in (let TMP_62 \def (Bind b1) in (let TMP_63 \def 
(CHead c3 TMP_62 v1) in (let TMP_64 \def (refl_equal C TMP_63) in (let TMP_65 
\def (ex2_3_intro B C T TMP_60 TMP_61 b1 c3 v1 TMP_64 H10) in (let TMP_66 
\def (eq_ind_r K TMP_43 TMP_49 TMP_65 k H7) in (eq_ind_r T v1 TMP_42 TMP_66 u 
H6))))))))))))))))) in (let TMP_68 \def (TMP_67 H5) in (TMP_68 
H4))))))))))))))))))))))))) in (let TMP_107 \def (\lambda (c1: C).(\lambda 
(c3: C).(\lambda (H1: (csubt g c1 c3)).(\lambda (H2: (((eq C c1 (CHead e1 
(Bind b1) v1)) \to (ex2_3 B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda 
(v2: T).(eq C c3 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2)))))))).(\lambda (b: B).(\lambda (_: (not 
(eq B b Void))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H4: (eq C (CHead 
c1 (Bind Void) u1) (CHead e1 (Bind b1) v1))).(let TMP_70 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) 
in (let TMP_71 \def (Bind Void) in (let TMP_72 \def (CHead c1 TMP_71 u1) in 
(let TMP_73 \def (Bind b1) in (let TMP_74 \def (CHead e1 TMP_73 v1) in (let 
H5 \def (f_equal C C TMP_70 TMP_72 TMP_74 H4) in (let TMP_75 \def (\lambda 
(e: C).(match e with [(CSort _) \Rightarrow Void | (CHead _ k _) \Rightarrow 
(match k with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Void])])) in 
(let TMP_76 \def (Bind Void) in (let TMP_77 \def (CHead c1 TMP_76 u1) in (let 
TMP_78 \def (Bind b1) in (let TMP_79 \def (CHead e1 TMP_78 v1) in (let H6 
\def (f_equal C B TMP_75 TMP_77 TMP_79 H4) in (let TMP_80 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow u1 | (CHead _ _ t) \Rightarrow t])) 
in (let TMP_81 \def (Bind Void) in (let TMP_82 \def (CHead c1 TMP_81 u1) in 
(let TMP_83 \def (Bind b1) in (let TMP_84 \def (CHead e1 TMP_83 v1) in (let 
H7 \def (f_equal C T TMP_80 TMP_82 TMP_84 H4) in (let TMP_105 \def (\lambda 
(H8: (eq B Void b1)).(\lambda (H9: (eq C c1 e1)).(let TMP_89 \def (\lambda 
(c: C).((eq C c (CHead e1 (Bind b1) v1)) \to (let TMP_87 \def (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(let TMP_85 \def (Bind b2) in (let 
TMP_86 \def (CHead e2 TMP_85 v2) in (eq C c3 TMP_86)))))) in (let TMP_88 \def 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2)))) in (ex2_3 
B C T TMP_87 TMP_88))))) in (let H10 \def (eq_ind C c1 TMP_89 H2 e1 H9) in 
(let TMP_90 \def (\lambda (c: C).(csubt g c c3)) in (let H11 \def (eq_ind C 
c1 TMP_90 H1 e1 H9) in (let TMP_95 \def (\lambda (b0: B).((eq C e1 (CHead e1 
(Bind b0) v1)) \to (let TMP_93 \def (\lambda (b2: B).(\lambda (e2: 
C).(\lambda (v2: T).(let TMP_91 \def (Bind b2) in (let TMP_92 \def (CHead e2 
TMP_91 v2) in (eq C c3 TMP_92)))))) in (let TMP_94 \def (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2)))) in (ex2_3 B C T TMP_93 
TMP_94))))) in (let H12 \def (eq_ind_r B b1 TMP_95 H10 Void H8) in (let 
TMP_100 \def (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(let TMP_96 
\def (Bind b) in (let TMP_97 \def (CHead c3 TMP_96 u2) in (let TMP_98 \def 
(Bind b2) in (let TMP_99 \def (CHead e2 TMP_98 v2) in (eq C TMP_97 
TMP_99)))))))) in (let TMP_101 \def (\lambda (_: B).(\lambda (e2: C).(\lambda 
(_: T).(csubt g e1 e2)))) in (let TMP_102 \def (Bind b) in (let TMP_103 \def 
(CHead c3 TMP_102 u2) in (let TMP_104 \def (refl_equal C TMP_103) in 
(ex2_3_intro B C T TMP_100 TMP_101 b c3 u2 TMP_104 H11)))))))))))))) in (let 
TMP_106 \def (TMP_105 H6) in (TMP_106 H5)))))))))))))))))))))))))))))) in 
(let TMP_148 \def (\lambda (c1: C).(\lambda (c3: C).(\lambda (H1: (csubt g c1 
c3)).(\lambda (H2: (((eq C c1 (CHead e1 (Bind b1) v1)) \to (ex2_3 B C T 
(\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C c3 (CHead e2 (Bind 
b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 
e2)))))))).(\lambda (u: T).(\lambda (t: T).(\lambda (H3: (ty3 g c1 u 
t)).(\lambda (H4: (ty3 g c3 u t)).(\lambda (H5: (eq C (CHead c1 (Bind Abst) 
t) (CHead e1 (Bind b1) v1))).(let TMP_108 \def (\lambda (e: C).(match e with 
[(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) in (let TMP_109 
\def (Bind Abst) in (let TMP_110 \def (CHead c1 TMP_109 t) in (let TMP_111 
\def (Bind b1) in (let TMP_112 \def (CHead e1 TMP_111 v1) in (let H6 \def 
(f_equal C C TMP_108 TMP_110 TMP_112 H5) in (let TMP_113 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow Abst | (CHead _ k _) \Rightarrow 
(match k with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow Abst])])) in 
(let TMP_114 \def (Bind Abst) in (let TMP_115 \def (CHead c1 TMP_114 t) in 
(let TMP_116 \def (Bind b1) in (let TMP_117 \def (CHead e1 TMP_116 v1) in 
(let H7 \def (f_equal C B TMP_113 TMP_115 TMP_117 H5) in (let TMP_118 \def 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow t | (CHead _ _ t0) 
\Rightarrow t0])) in (let TMP_119 \def (Bind Abst) in (let TMP_120 \def 
(CHead c1 TMP_119 t) in (let TMP_121 \def (Bind b1) in (let TMP_122 \def 
(CHead e1 TMP_121 v1) in (let H8 \def (f_equal C T TMP_118 TMP_120 TMP_122 
H5) in (let TMP_146 \def (\lambda (H9: (eq B Abst b1)).(\lambda (H10: (eq C 
c1 e1)).(let TMP_123 \def (\lambda (t0: T).(ty3 g c3 u t0)) in (let H11 \def 
(eq_ind T t TMP_123 H4 v1 H8) in (let TMP_124 \def (\lambda (t0: T).(ty3 g c1 
u t0)) in (let H12 \def (eq_ind T t TMP_124 H3 v1 H8) in (let TMP_125 \def 
(\lambda (c: C).(ty3 g c u v1)) in (let H13 \def (eq_ind C c1 TMP_125 H12 e1 
H10) in (let TMP_130 \def (\lambda (c: C).((eq C c (CHead e1 (Bind b1) v1)) 
\to (let TMP_128 \def (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(let 
TMP_126 \def (Bind b2) in (let TMP_127 \def (CHead e2 TMP_126 v2) in (eq C c3 
TMP_127)))))) in (let TMP_129 \def (\lambda (_: B).(\lambda (e2: C).(\lambda 
(_: T).(csubt g e1 e2)))) in (ex2_3 B C T TMP_128 TMP_129))))) in (let H14 
\def (eq_ind C c1 TMP_130 H2 e1 H10) in (let TMP_131 \def (\lambda (c: 
C).(csubt g c c3)) in (let H15 \def (eq_ind C c1 TMP_131 H1 e1 H10) in (let 
TMP_136 \def (\lambda (b: B).((eq C e1 (CHead e1 (Bind b) v1)) \to (let 
TMP_134 \def (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(let TMP_132 
\def (Bind b2) in (let TMP_133 \def (CHead e2 TMP_132 v2) in (eq C c3 
TMP_133)))))) in (let TMP_135 \def (\lambda (_: B).(\lambda (e2: C).(\lambda 
(_: T).(csubt g e1 e2)))) in (ex2_3 B C T TMP_134 TMP_135))))) in (let H16 
\def (eq_ind_r B b1 TMP_136 H14 Abst H9) in (let TMP_141 \def (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(let TMP_137 \def (Bind Abbr) in (let 
TMP_138 \def (CHead c3 TMP_137 u) in (let TMP_139 \def (Bind b2) in (let 
TMP_140 \def (CHead e2 TMP_139 v2) in (eq C TMP_138 TMP_140)))))))) in (let 
TMP_142 \def (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 
e2)))) in (let TMP_143 \def (Bind Abbr) in (let TMP_144 \def (CHead c3 
TMP_143 u) in (let TMP_145 \def (refl_equal C TMP_144) in (ex2_3_intro B C T 
TMP_141 TMP_142 Abbr c3 u TMP_145 H15)))))))))))))))))))) in (let TMP_147 
\def (TMP_146 H7) in (TMP_147 H6)))))))))))))))))))))))))))))) in (csubt_ind 
g TMP_13 TMP_24 TMP_69 TMP_107 TMP_148 y c2 H0)))))))) in (insert_eq C TMP_2 
TMP_3 TMP_8 TMP_149 H))))))))))).

