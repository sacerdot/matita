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

include "basic_1/wf3/defs.ma".

let rec wf3_ind (g: G) (P: (C \to (C \to Prop))) (f: (\forall (m: nat).(P 
(CSort m) (CSort m)))) (f0: (\forall (c1: C).(\forall (c2: C).((wf3 g c1 c2) 
\to ((P c1 c2) \to (\forall (u: T).(\forall (t: T).((ty3 g c1 u t) \to 
(\forall (b: B).(P (CHead c1 (Bind b) u) (CHead c2 (Bind b) u))))))))))) (f1: 
(\forall (c1: C).(\forall (c2: C).((wf3 g c1 c2) \to ((P c1 c2) \to (\forall 
(u: T).(((\forall (t: T).((ty3 g c1 u t) \to False))) \to (\forall (b: B).(P 
(CHead c1 (Bind b) u) (CHead c2 (Bind Void) (TSort O))))))))))) (f2: (\forall 
(c1: C).(\forall (c2: C).((wf3 g c1 c2) \to ((P c1 c2) \to (\forall (u: 
T).(\forall (f2: F).(P (CHead c1 (Flat f2) u) c2)))))))) (c: C) (c0: C) (w: 
wf3 g c c0) on w: P c c0 \def match w with [(wf3_sort m) \Rightarrow (f m) | 
(wf3_bind c1 c2 w0 u t t0 b) \Rightarrow (let TMP_3 \def ((wf3_ind g P f f0 
f1 f2) c1 c2 w0) in (f0 c1 c2 w0 TMP_3 u t t0 b)) | (wf3_void c1 c2 w0 u f3 
b) \Rightarrow (let TMP_2 \def ((wf3_ind g P f f0 f1 f2) c1 c2 w0) in (f1 c1 
c2 w0 TMP_2 u f3 b)) | (wf3_flat c1 c2 w0 u f3) \Rightarrow (let TMP_1 \def 
((wf3_ind g P f f0 f1 f2) c1 c2 w0) in (f2 c1 c2 w0 TMP_1 u f3))].

theorem wf3_gen_sort1:
 \forall (g: G).(\forall (x: C).(\forall (m: nat).((wf3 g (CSort m) x) \to 
(eq C x (CSort m)))))
\def
 \lambda (g: G).(\lambda (x: C).(\lambda (m: nat).(\lambda (H: (wf3 g (CSort 
m) x)).(let TMP_1 \def (CSort m) in (let TMP_2 \def (\lambda (c: C).(wf3 g c 
x)) in (let TMP_3 \def (\lambda (c: C).(eq C x c)) in (let TMP_43 \def 
(\lambda (y: C).(\lambda (H0: (wf3 g y x)).(let TMP_4 \def (\lambda (c: 
C).(\lambda (c0: C).((eq C c (CSort m)) \to (eq C c0 c)))) in (let TMP_13 
\def (\lambda (m0: nat).(\lambda (H1: (eq C (CSort m0) (CSort m))).(let TMP_5 
\def (\lambda (e: C).(match e with [(CSort n) \Rightarrow n | (CHead _ _ _) 
\Rightarrow m0])) in (let TMP_6 \def (CSort m0) in (let TMP_7 \def (CSort m) 
in (let H2 \def (f_equal C nat TMP_5 TMP_6 TMP_7 H1) in (let TMP_10 \def 
(\lambda (n: nat).(let TMP_8 \def (CSort n) in (let TMP_9 \def (CSort n) in 
(eq C TMP_8 TMP_9)))) in (let TMP_11 \def (CSort m) in (let TMP_12 \def 
(refl_equal C TMP_11) in (eq_ind_r nat m TMP_10 TMP_12 m0 H2)))))))))) in 
(let TMP_23 \def (\lambda (c1: C).(\lambda (c2: C).(\lambda (_: (wf3 g c1 
c2)).(\lambda (_: (((eq C c1 (CSort m)) \to (eq C c2 c1)))).(\lambda (u: 
T).(\lambda (t: T).(\lambda (_: (ty3 g c1 u t)).(\lambda (b: B).(\lambda (H4: 
(eq C (CHead c1 (Bind b) u) (CSort m))).(let TMP_14 \def (Bind b) in (let 
TMP_15 \def (CHead c1 TMP_14 u) in (let TMP_16 \def (\lambda (ee: C).(match 
ee with [(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow True])) in 
(let TMP_17 \def (CSort m) in (let H5 \def (eq_ind C TMP_15 TMP_16 I TMP_17 
H4) in (let TMP_18 \def (Bind b) in (let TMP_19 \def (CHead c2 TMP_18 u) in 
(let TMP_20 \def (Bind b) in (let TMP_21 \def (CHead c1 TMP_20 u) in (let 
TMP_22 \def (eq C TMP_19 TMP_21) in (False_ind TMP_22 H5)))))))))))))))))))) 
in (let TMP_34 \def (\lambda (c1: C).(\lambda (c2: C).(\lambda (_: (wf3 g c1 
c2)).(\lambda (_: (((eq C c1 (CSort m)) \to (eq C c2 c1)))).(\lambda (u: 
T).(\lambda (_: ((\forall (t: T).((ty3 g c1 u t) \to False)))).(\lambda (b: 
B).(\lambda (H4: (eq C (CHead c1 (Bind b) u) (CSort m))).(let TMP_24 \def 
(Bind b) in (let TMP_25 \def (CHead c1 TMP_24 u) in (let TMP_26 \def (\lambda 
(ee: C).(match ee with [(CSort _) \Rightarrow False | (CHead _ _ _) 
\Rightarrow True])) in (let TMP_27 \def (CSort m) in (let H5 \def (eq_ind C 
TMP_25 TMP_26 I TMP_27 H4) in (let TMP_28 \def (Bind Void) in (let TMP_29 
\def (TSort O) in (let TMP_30 \def (CHead c2 TMP_28 TMP_29) in (let TMP_31 
\def (Bind b) in (let TMP_32 \def (CHead c1 TMP_31 u) in (let TMP_33 \def (eq 
C TMP_30 TMP_32) in (False_ind TMP_33 H5)))))))))))))))))))) in (let TMP_42 
\def (\lambda (c1: C).(\lambda (c2: C).(\lambda (_: (wf3 g c1 c2)).(\lambda 
(_: (((eq C c1 (CSort m)) \to (eq C c2 c1)))).(\lambda (u: T).(\lambda (f: 
F).(\lambda (H3: (eq C (CHead c1 (Flat f) u) (CSort m))).(let TMP_35 \def 
(Flat f) in (let TMP_36 \def (CHead c1 TMP_35 u) in (let TMP_37 \def (\lambda 
(ee: C).(match ee with [(CSort _) \Rightarrow False | (CHead _ _ _) 
\Rightarrow True])) in (let TMP_38 \def (CSort m) in (let H4 \def (eq_ind C 
TMP_36 TMP_37 I TMP_38 H3) in (let TMP_39 \def (Flat f) in (let TMP_40 \def 
(CHead c1 TMP_39 u) in (let TMP_41 \def (eq C c2 TMP_40) in (False_ind TMP_41 
H4)))))))))))))))) in (wf3_ind g TMP_4 TMP_13 TMP_23 TMP_34 TMP_42 y x 
H0)))))))) in (insert_eq C TMP_1 TMP_2 TMP_3 TMP_43 H)))))))).

theorem wf3_gen_bind1:
 \forall (g: G).(\forall (c1: C).(\forall (x: C).(\forall (v: T).(\forall (b: 
B).((wf3 g (CHead c1 (Bind b) v) x) \to (or (ex3_2 C T (\lambda (c2: 
C).(\lambda (_: T).(eq C x (CHead c2 (Bind b) v)))) (\lambda (c2: C).(\lambda 
(_: T).(wf3 g c1 c2))) (\lambda (_: C).(\lambda (w: T).(ty3 g c1 v w)))) (ex3 
C (\lambda (c2: C).(eq C x (CHead c2 (Bind Void) (TSort O)))) (\lambda (c2: 
C).(wf3 g c1 c2)) (\lambda (_: C).(\forall (w: T).((ty3 g c1 v w) \to 
False))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (x: C).(\lambda (v: T).(\lambda (b: 
B).(\lambda (H: (wf3 g (CHead c1 (Bind b) v) x)).(let TMP_1 \def (Bind b) in 
(let TMP_2 \def (CHead c1 TMP_1 v) in (let TMP_3 \def (\lambda (c: C).(wf3 g 
c x)) in (let TMP_17 \def (\lambda (_: C).(let TMP_6 \def (\lambda (c2: 
C).(\lambda (_: T).(let TMP_4 \def (Bind b) in (let TMP_5 \def (CHead c2 
TMP_4 v) in (eq C x TMP_5))))) in (let TMP_7 \def (\lambda (c2: C).(\lambda 
(_: T).(wf3 g c1 c2))) in (let TMP_8 \def (\lambda (_: C).(\lambda (w: 
T).(ty3 g c1 v w))) in (let TMP_9 \def (ex3_2 C T TMP_6 TMP_7 TMP_8) in (let 
TMP_13 \def (\lambda (c2: C).(let TMP_10 \def (Bind Void) in (let TMP_11 \def 
(TSort O) in (let TMP_12 \def (CHead c2 TMP_10 TMP_11) in (eq C x TMP_12))))) 
in (let TMP_14 \def (\lambda (c2: C).(wf3 g c1 c2)) in (let TMP_15 \def 
(\lambda (_: C).(\forall (w: T).((ty3 g c1 v w) \to False))) in (let TMP_16 
\def (ex3 C TMP_13 TMP_14 TMP_15) in (or TMP_9 TMP_16)))))))))) in (let 
TMP_242 \def (\lambda (y: C).(\lambda (H0: (wf3 g y x)).(let TMP_31 \def 
(\lambda (c: C).(\lambda (c0: C).((eq C c (CHead c1 (Bind b) v)) \to (let 
TMP_20 \def (\lambda (c2: C).(\lambda (_: T).(let TMP_18 \def (Bind b) in 
(let TMP_19 \def (CHead c2 TMP_18 v) in (eq C c0 TMP_19))))) in (let TMP_21 
\def (\lambda (c2: C).(\lambda (_: T).(wf3 g c1 c2))) in (let TMP_22 \def 
(\lambda (_: C).(\lambda (w: T).(ty3 g c1 v w))) in (let TMP_23 \def (ex3_2 C 
T TMP_20 TMP_21 TMP_22) in (let TMP_27 \def (\lambda (c2: C).(let TMP_24 \def 
(Bind Void) in (let TMP_25 \def (TSort O) in (let TMP_26 \def (CHead c2 
TMP_24 TMP_25) in (eq C c0 TMP_26))))) in (let TMP_28 \def (\lambda (c2: 
C).(wf3 g c1 c2)) in (let TMP_29 \def (\lambda (_: C).(\forall (w: T).((ty3 g 
c1 v w) \to False))) in (let TMP_30 \def (ex3 C TMP_27 TMP_28 TMP_29) in (or 
TMP_23 TMP_30)))))))))))) in (let TMP_52 \def (\lambda (m: nat).(\lambda (H1: 
(eq C (CSort m) (CHead c1 (Bind b) v))).(let TMP_32 \def (CSort m) in (let 
TMP_33 \def (\lambda (ee: C).(match ee with [(CSort _) \Rightarrow True | 
(CHead _ _ _) \Rightarrow False])) in (let TMP_34 \def (Bind b) in (let 
TMP_35 \def (CHead c1 TMP_34 v) in (let H2 \def (eq_ind C TMP_32 TMP_33 I 
TMP_35 H1) in (let TMP_39 \def (\lambda (c2: C).(\lambda (_: T).(let TMP_36 
\def (CSort m) in (let TMP_37 \def (Bind b) in (let TMP_38 \def (CHead c2 
TMP_37 v) in (eq C TMP_36 TMP_38)))))) in (let TMP_40 \def (\lambda (c2: 
C).(\lambda (_: T).(wf3 g c1 c2))) in (let TMP_41 \def (\lambda (_: 
C).(\lambda (w: T).(ty3 g c1 v w))) in (let TMP_42 \def (ex3_2 C T TMP_39 
TMP_40 TMP_41) in (let TMP_47 \def (\lambda (c2: C).(let TMP_43 \def (CSort 
m) in (let TMP_44 \def (Bind Void) in (let TMP_45 \def (TSort O) in (let 
TMP_46 \def (CHead c2 TMP_44 TMP_45) in (eq C TMP_43 TMP_46)))))) in (let 
TMP_48 \def (\lambda (c2: C).(wf3 g c1 c2)) in (let TMP_49 \def (\lambda (_: 
C).(\forall (w: T).((ty3 g c1 v w) \to False))) in (let TMP_50 \def (ex3 C 
TMP_47 TMP_48 TMP_49) in (let TMP_51 \def (or TMP_42 TMP_50) in (False_ind 
TMP_51 H2))))))))))))))))) in (let TMP_153 \def (\lambda (c0: C).(\lambda 
(c2: C).(\lambda (H1: (wf3 g c0 c2)).(\lambda (H2: (((eq C c0 (CHead c1 (Bind 
b) v)) \to (or (ex3_2 C T (\lambda (c3: C).(\lambda (_: T).(eq C c2 (CHead c3 
(Bind b) v)))) (\lambda (c3: C).(\lambda (_: T).(wf3 g c1 c3))) (\lambda (_: 
C).(\lambda (w: T).(ty3 g c1 v w)))) (ex3 C (\lambda (c3: C).(eq C c2 (CHead 
c3 (Bind Void) (TSort O)))) (\lambda (c3: C).(wf3 g c1 c3)) (\lambda (_: 
C).(\forall (w: T).((ty3 g c1 v w) \to False)))))))).(\lambda (u: T).(\lambda 
(t: T).(\lambda (H3: (ty3 g c0 u t)).(\lambda (b0: B).(\lambda (H4: (eq C 
(CHead c0 (Bind b0) u) (CHead c1 (Bind b) v))).(let TMP_53 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) 
in (let TMP_54 \def (Bind b0) in (let TMP_55 \def (CHead c0 TMP_54 u) in (let 
TMP_56 \def (Bind b) in (let TMP_57 \def (CHead c1 TMP_56 v) in (let H5 \def 
(f_equal C C TMP_53 TMP_55 TMP_57 H4) in (let TMP_58 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow b0 | (CHead _ k _) \Rightarrow (match 
k with [(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow b0])])) in (let 
TMP_59 \def (Bind b0) in (let TMP_60 \def (CHead c0 TMP_59 u) in (let TMP_61 
\def (Bind b) in (let TMP_62 \def (CHead c1 TMP_61 v) in (let H6 \def 
(f_equal C B TMP_58 TMP_60 TMP_62 H4) in (let TMP_63 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) 
in (let TMP_64 \def (Bind b0) in (let TMP_65 \def (CHead c0 TMP_64 u) in (let 
TMP_66 \def (Bind b) in (let TMP_67 \def (CHead c1 TMP_66 v) in (let H7 \def 
(f_equal C T TMP_63 TMP_65 TMP_67 H4) in (let TMP_151 \def (\lambda (H8: (eq 
B b0 b)).(\lambda (H9: (eq C c0 c1)).(let TMP_85 \def (\lambda (b1: B).(let 
TMP_72 \def (\lambda (c3: C).(\lambda (_: T).(let TMP_68 \def (Bind b1) in 
(let TMP_69 \def (CHead c2 TMP_68 u) in (let TMP_70 \def (Bind b) in (let 
TMP_71 \def (CHead c3 TMP_70 v) in (eq C TMP_69 TMP_71))))))) in (let TMP_73 
\def (\lambda (c3: C).(\lambda (_: T).(wf3 g c1 c3))) in (let TMP_74 \def 
(\lambda (_: C).(\lambda (w: T).(ty3 g c1 v w))) in (let TMP_75 \def (ex3_2 C 
T TMP_72 TMP_73 TMP_74) in (let TMP_81 \def (\lambda (c3: C).(let TMP_76 \def 
(Bind b1) in (let TMP_77 \def (CHead c2 TMP_76 u) in (let TMP_78 \def (Bind 
Void) in (let TMP_79 \def (TSort O) in (let TMP_80 \def (CHead c3 TMP_78 
TMP_79) in (eq C TMP_77 TMP_80))))))) in (let TMP_82 \def (\lambda (c3: 
C).(wf3 g c1 c3)) in (let TMP_83 \def (\lambda (_: C).(\forall (w: T).((ty3 g 
c1 v w) \to False))) in (let TMP_84 \def (ex3 C TMP_81 TMP_82 TMP_83) in (or 
TMP_75 TMP_84)))))))))) in (let TMP_86 \def (\lambda (t0: T).(ty3 g c0 t0 t)) 
in (let H10 \def (eq_ind T u TMP_86 H3 v H7) in (let TMP_104 \def (\lambda 
(t0: T).(let TMP_91 \def (\lambda (c3: C).(\lambda (_: T).(let TMP_87 \def 
(Bind b) in (let TMP_88 \def (CHead c2 TMP_87 t0) in (let TMP_89 \def (Bind 
b) in (let TMP_90 \def (CHead c3 TMP_89 v) in (eq C TMP_88 TMP_90))))))) in 
(let TMP_92 \def (\lambda (c3: C).(\lambda (_: T).(wf3 g c1 c3))) in (let 
TMP_93 \def (\lambda (_: C).(\lambda (w: T).(ty3 g c1 v w))) in (let TMP_94 
\def (ex3_2 C T TMP_91 TMP_92 TMP_93) in (let TMP_100 \def (\lambda (c3: 
C).(let TMP_95 \def (Bind b) in (let TMP_96 \def (CHead c2 TMP_95 t0) in (let 
TMP_97 \def (Bind Void) in (let TMP_98 \def (TSort O) in (let TMP_99 \def 
(CHead c3 TMP_97 TMP_98) in (eq C TMP_96 TMP_99))))))) in (let TMP_101 \def 
(\lambda (c3: C).(wf3 g c1 c3)) in (let TMP_102 \def (\lambda (_: C).(\forall 
(w: T).((ty3 g c1 v w) \to False))) in (let TMP_103 \def (ex3 C TMP_100 
TMP_101 TMP_102) in (or TMP_94 TMP_103)))))))))) in (let TMP_105 \def 
(\lambda (c: C).(ty3 g c v t)) in (let H11 \def (eq_ind C c0 TMP_105 H10 c1 
H9) in (let TMP_119 \def (\lambda (c: C).((eq C c (CHead c1 (Bind b) v)) \to 
(let TMP_108 \def (\lambda (c3: C).(\lambda (_: T).(let TMP_106 \def (Bind b) 
in (let TMP_107 \def (CHead c3 TMP_106 v) in (eq C c2 TMP_107))))) in (let 
TMP_109 \def (\lambda (c3: C).(\lambda (_: T).(wf3 g c1 c3))) in (let TMP_110 
\def (\lambda (_: C).(\lambda (w: T).(ty3 g c1 v w))) in (let TMP_111 \def 
(ex3_2 C T TMP_108 TMP_109 TMP_110) in (let TMP_115 \def (\lambda (c3: 
C).(let TMP_112 \def (Bind Void) in (let TMP_113 \def (TSort O) in (let 
TMP_114 \def (CHead c3 TMP_112 TMP_113) in (eq C c2 TMP_114))))) in (let 
TMP_116 \def (\lambda (c3: C).(wf3 g c1 c3)) in (let TMP_117 \def (\lambda 
(_: C).(\forall (w: T).((ty3 g c1 v w) \to False))) in (let TMP_118 \def (ex3 
C TMP_115 TMP_116 TMP_117) in (or TMP_111 TMP_118))))))))))) in (let H12 \def 
(eq_ind C c0 TMP_119 H2 c1 H9) in (let TMP_120 \def (\lambda (c: C).(wf3 g c 
c2)) in (let H13 \def (eq_ind C c0 TMP_120 H1 c1 H9) in (let TMP_125 \def 
(\lambda (c3: C).(\lambda (_: T).(let TMP_121 \def (Bind b) in (let TMP_122 
\def (CHead c2 TMP_121 v) in (let TMP_123 \def (Bind b) in (let TMP_124 \def 
(CHead c3 TMP_123 v) in (eq C TMP_122 TMP_124))))))) in (let TMP_126 \def 
(\lambda (c3: C).(\lambda (_: T).(wf3 g c1 c3))) in (let TMP_127 \def 
(\lambda (_: C).(\lambda (w: T).(ty3 g c1 v w))) in (let TMP_128 \def (ex3_2 
C T TMP_125 TMP_126 TMP_127) in (let TMP_134 \def (\lambda (c3: C).(let 
TMP_129 \def (Bind b) in (let TMP_130 \def (CHead c2 TMP_129 v) in (let 
TMP_131 \def (Bind Void) in (let TMP_132 \def (TSort O) in (let TMP_133 \def 
(CHead c3 TMP_131 TMP_132) in (eq C TMP_130 TMP_133))))))) in (let TMP_135 
\def (\lambda (c3: C).(wf3 g c1 c3)) in (let TMP_136 \def (\lambda (_: 
C).(\forall (w: T).((ty3 g c1 v w) \to False))) in (let TMP_137 \def (ex3 C 
TMP_134 TMP_135 TMP_136) in (let TMP_142 \def (\lambda (c3: C).(\lambda (_: 
T).(let TMP_138 \def (Bind b) in (let TMP_139 \def (CHead c2 TMP_138 v) in 
(let TMP_140 \def (Bind b) in (let TMP_141 \def (CHead c3 TMP_140 v) in (eq C 
TMP_139 TMP_141))))))) in (let TMP_143 \def (\lambda (c3: C).(\lambda (_: 
T).(wf3 g c1 c3))) in (let TMP_144 \def (\lambda (_: C).(\lambda (w: T).(ty3 
g c1 v w))) in (let TMP_145 \def (Bind b) in (let TMP_146 \def (CHead c2 
TMP_145 v) in (let TMP_147 \def (refl_equal C TMP_146) in (let TMP_148 \def 
(ex3_2_intro C T TMP_142 TMP_143 TMP_144 c2 t TMP_147 H13 H11) in (let 
TMP_149 \def (or_introl TMP_128 TMP_137 TMP_148) in (let TMP_150 \def 
(eq_ind_r T v TMP_104 TMP_149 u H7) in (eq_ind_r B b TMP_85 TMP_150 b0 
H8)))))))))))))))))))))))))))))) in (let TMP_152 \def (TMP_151 H6) in 
(TMP_152 H5)))))))))))))))))))))))))))))) in (let TMP_221 \def (\lambda (c0: 
C).(\lambda (c2: C).(\lambda (H1: (wf3 g c0 c2)).(\lambda (H2: (((eq C c0 
(CHead c1 (Bind b) v)) \to (or (ex3_2 C T (\lambda (c3: C).(\lambda (_: 
T).(eq C c2 (CHead c3 (Bind b) v)))) (\lambda (c3: C).(\lambda (_: T).(wf3 g 
c1 c3))) (\lambda (_: C).(\lambda (w: T).(ty3 g c1 v w)))) (ex3 C (\lambda 
(c3: C).(eq C c2 (CHead c3 (Bind Void) (TSort O)))) (\lambda (c3: C).(wf3 g 
c1 c3)) (\lambda (_: C).(\forall (w: T).((ty3 g c1 v w) \to 
False)))))))).(\lambda (u: T).(\lambda (H3: ((\forall (t: T).((ty3 g c0 u t) 
\to False)))).(\lambda (b0: B).(\lambda (H4: (eq C (CHead c0 (Bind b0) u) 
(CHead c1 (Bind b) v))).(let TMP_154 \def (\lambda (e: C).(match e with 
[(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) in (let TMP_155 
\def (Bind b0) in (let TMP_156 \def (CHead c0 TMP_155 u) in (let TMP_157 \def 
(Bind b) in (let TMP_158 \def (CHead c1 TMP_157 v) in (let H5 \def (f_equal C 
C TMP_154 TMP_156 TMP_158 H4) in (let TMP_159 \def (\lambda (e: C).(match e 
with [(CSort _) \Rightarrow b0 | (CHead _ k _) \Rightarrow (match k with 
[(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow b0])])) in (let TMP_160 \def 
(Bind b0) in (let TMP_161 \def (CHead c0 TMP_160 u) in (let TMP_162 \def 
(Bind b) in (let TMP_163 \def (CHead c1 TMP_162 v) in (let H6 \def (f_equal C 
B TMP_159 TMP_161 TMP_163 H4) in (let TMP_164 \def (\lambda (e: C).(match e 
with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) in (let 
TMP_165 \def (Bind b0) in (let TMP_166 \def (CHead c0 TMP_165 u) in (let 
TMP_167 \def (Bind b) in (let TMP_168 \def (CHead c1 TMP_167 v) in (let H7 
\def (f_equal C T TMP_164 TMP_166 TMP_168 H4) in (let TMP_219 \def (\lambda 
(_: (eq B b0 b)).(\lambda (H9: (eq C c0 c1)).(let TMP_169 \def (\lambda (t: 
T).(\forall (t0: T).((ty3 g c0 t t0) \to False))) in (let H10 \def (eq_ind T 
u TMP_169 H3 v H7) in (let TMP_170 \def (\lambda (c: C).(\forall (t: T).((ty3 
g c v t) \to False))) in (let H11 \def (eq_ind C c0 TMP_170 H10 c1 H9) in 
(let TMP_184 \def (\lambda (c: C).((eq C c (CHead c1 (Bind b) v)) \to (let 
TMP_173 \def (\lambda (c3: C).(\lambda (_: T).(let TMP_171 \def (Bind b) in 
(let TMP_172 \def (CHead c3 TMP_171 v) in (eq C c2 TMP_172))))) in (let 
TMP_174 \def (\lambda (c3: C).(\lambda (_: T).(wf3 g c1 c3))) in (let TMP_175 
\def (\lambda (_: C).(\lambda (w: T).(ty3 g c1 v w))) in (let TMP_176 \def 
(ex3_2 C T TMP_173 TMP_174 TMP_175) in (let TMP_180 \def (\lambda (c3: 
C).(let TMP_177 \def (Bind Void) in (let TMP_178 \def (TSort O) in (let 
TMP_179 \def (CHead c3 TMP_177 TMP_178) in (eq C c2 TMP_179))))) in (let 
TMP_181 \def (\lambda (c3: C).(wf3 g c1 c3)) in (let TMP_182 \def (\lambda 
(_: C).(\forall (w: T).((ty3 g c1 v w) \to False))) in (let TMP_183 \def (ex3 
C TMP_180 TMP_181 TMP_182) in (or TMP_176 TMP_183))))))))))) in (let H12 \def 
(eq_ind C c0 TMP_184 H2 c1 H9) in (let TMP_185 \def (\lambda (c: C).(wf3 g c 
c2)) in (let H13 \def (eq_ind C c0 TMP_185 H1 c1 H9) in (let TMP_191 \def 
(\lambda (c3: C).(\lambda (_: T).(let TMP_186 \def (Bind Void) in (let 
TMP_187 \def (TSort O) in (let TMP_188 \def (CHead c2 TMP_186 TMP_187) in 
(let TMP_189 \def (Bind b) in (let TMP_190 \def (CHead c3 TMP_189 v) in (eq C 
TMP_188 TMP_190)))))))) in (let TMP_192 \def (\lambda (c3: C).(\lambda (_: 
T).(wf3 g c1 c3))) in (let TMP_193 \def (\lambda (_: C).(\lambda (w: T).(ty3 
g c1 v w))) in (let TMP_194 \def (ex3_2 C T TMP_191 TMP_192 TMP_193) in (let 
TMP_201 \def (\lambda (c3: C).(let TMP_195 \def (Bind Void) in (let TMP_196 
\def (TSort O) in (let TMP_197 \def (CHead c2 TMP_195 TMP_196) in (let 
TMP_198 \def (Bind Void) in (let TMP_199 \def (TSort O) in (let TMP_200 \def 
(CHead c3 TMP_198 TMP_199) in (eq C TMP_197 TMP_200)))))))) in (let TMP_202 
\def (\lambda (c3: C).(wf3 g c1 c3)) in (let TMP_203 \def (\lambda (_: 
C).(\forall (w: T).((ty3 g c1 v w) \to False))) in (let TMP_204 \def (ex3 C 
TMP_201 TMP_202 TMP_203) in (let TMP_211 \def (\lambda (c3: C).(let TMP_205 
\def (Bind Void) in (let TMP_206 \def (TSort O) in (let TMP_207 \def (CHead 
c2 TMP_205 TMP_206) in (let TMP_208 \def (Bind Void) in (let TMP_209 \def 
(TSort O) in (let TMP_210 \def (CHead c3 TMP_208 TMP_209) in (eq C TMP_207 
TMP_210)))))))) in (let TMP_212 \def (\lambda (c3: C).(wf3 g c1 c3)) in (let 
TMP_213 \def (\lambda (_: C).(\forall (w: T).((ty3 g c1 v w) \to False))) in 
(let TMP_214 \def (Bind Void) in (let TMP_215 \def (TSort O) in (let TMP_216 
\def (CHead c2 TMP_214 TMP_215) in (let TMP_217 \def (refl_equal C TMP_216) 
in (let TMP_218 \def (ex3_intro C TMP_211 TMP_212 TMP_213 c2 TMP_217 H13 H11) 
in (or_intror TMP_194 TMP_204 TMP_218))))))))))))))))))))))))))) in (let 
TMP_220 \def (TMP_219 H6) in (TMP_220 H5))))))))))))))))))))))))))))) in (let 
TMP_241 \def (\lambda (c0: C).(\lambda (c2: C).(\lambda (_: (wf3 g c0 
c2)).(\lambda (_: (((eq C c0 (CHead c1 (Bind b) v)) \to (or (ex3_2 C T 
(\lambda (c3: C).(\lambda (_: T).(eq C c2 (CHead c3 (Bind b) v)))) (\lambda 
(c3: C).(\lambda (_: T).(wf3 g c1 c3))) (\lambda (_: C).(\lambda (w: T).(ty3 
g c1 v w)))) (ex3 C (\lambda (c3: C).(eq C c2 (CHead c3 (Bind Void) (TSort 
O)))) (\lambda (c3: C).(wf3 g c1 c3)) (\lambda (_: C).(\forall (w: T).((ty3 g 
c1 v w) \to False)))))))).(\lambda (u: T).(\lambda (f: F).(\lambda (H3: (eq C 
(CHead c0 (Flat f) u) (CHead c1 (Bind b) v))).(let TMP_222 \def (Flat f) in 
(let TMP_223 \def (CHead c0 TMP_222 u) in (let TMP_224 \def (\lambda (ee: 
C).(match ee with [(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow 
(match k with [(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])])) in 
(let TMP_225 \def (Bind b) in (let TMP_226 \def (CHead c1 TMP_225 v) in (let 
H4 \def (eq_ind C TMP_223 TMP_224 I TMP_226 H3) in (let TMP_229 \def (\lambda 
(c3: C).(\lambda (_: T).(let TMP_227 \def (Bind b) in (let TMP_228 \def 
(CHead c3 TMP_227 v) in (eq C c2 TMP_228))))) in (let TMP_230 \def (\lambda 
(c3: C).(\lambda (_: T).(wf3 g c1 c3))) in (let TMP_231 \def (\lambda (_: 
C).(\lambda (w: T).(ty3 g c1 v w))) in (let TMP_232 \def (ex3_2 C T TMP_229 
TMP_230 TMP_231) in (let TMP_236 \def (\lambda (c3: C).(let TMP_233 \def 
(Bind Void) in (let TMP_234 \def (TSort O) in (let TMP_235 \def (CHead c3 
TMP_233 TMP_234) in (eq C c2 TMP_235))))) in (let TMP_237 \def (\lambda (c3: 
C).(wf3 g c1 c3)) in (let TMP_238 \def (\lambda (_: C).(\forall (w: T).((ty3 
g c1 v w) \to False))) in (let TMP_239 \def (ex3 C TMP_236 TMP_237 TMP_238) 
in (let TMP_240 \def (or TMP_232 TMP_239) in (False_ind TMP_240 
H4))))))))))))))))))))))) in (wf3_ind g TMP_31 TMP_52 TMP_153 TMP_221 TMP_241 
y x H0)))))))) in (insert_eq C TMP_2 TMP_3 TMP_17 TMP_242 H))))))))))).

theorem wf3_gen_flat1:
 \forall (g: G).(\forall (c1: C).(\forall (x: C).(\forall (v: T).(\forall (f: 
F).((wf3 g (CHead c1 (Flat f) v) x) \to (wf3 g c1 x))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (x: C).(\lambda (v: T).(\lambda (f: 
F).(\lambda (H: (wf3 g (CHead c1 (Flat f) v) x)).(let TMP_1 \def (Flat f) in 
(let TMP_2 \def (CHead c1 TMP_1 v) in (let TMP_3 \def (\lambda (c: C).(wf3 g 
c x)) in (let TMP_4 \def (\lambda (_: C).(wf3 g c1 x)) in (let TMP_52 \def 
(\lambda (y: C).(\lambda (H0: (wf3 g y x)).(let TMP_5 \def (\lambda (c: 
C).(\lambda (c0: C).((eq C c (CHead c1 (Flat f) v)) \to (wf3 g c1 c0)))) in 
(let TMP_12 \def (\lambda (m: nat).(\lambda (H1: (eq C (CSort m) (CHead c1 
(Flat f) v))).(let TMP_6 \def (CSort m) in (let TMP_7 \def (\lambda (ee: 
C).(match ee with [(CSort _) \Rightarrow True | (CHead _ _ _) \Rightarrow 
False])) in (let TMP_8 \def (Flat f) in (let TMP_9 \def (CHead c1 TMP_8 v) in 
(let H2 \def (eq_ind C TMP_6 TMP_7 I TMP_9 H1) in (let TMP_10 \def (CSort m) 
in (let TMP_11 \def (wf3 g c1 TMP_10) in (False_ind TMP_11 H2)))))))))) in 
(let TMP_21 \def (\lambda (c0: C).(\lambda (c2: C).(\lambda (_: (wf3 g c0 
c2)).(\lambda (_: (((eq C c0 (CHead c1 (Flat f) v)) \to (wf3 g c1 
c2)))).(\lambda (u: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 u t)).(\lambda 
(b: B).(\lambda (H4: (eq C (CHead c0 (Bind b) u) (CHead c1 (Flat f) v))).(let 
TMP_13 \def (Bind b) in (let TMP_14 \def (CHead c0 TMP_13 u) in (let TMP_15 
\def (\lambda (ee: C).(match ee with [(CSort _) \Rightarrow False | (CHead _ 
k _) \Rightarrow (match k with [(Bind _) \Rightarrow True | (Flat _) 
\Rightarrow False])])) in (let TMP_16 \def (Flat f) in (let TMP_17 \def 
(CHead c1 TMP_16 v) in (let H5 \def (eq_ind C TMP_14 TMP_15 I TMP_17 H4) in 
(let TMP_18 \def (Bind b) in (let TMP_19 \def (CHead c2 TMP_18 u) in (let 
TMP_20 \def (wf3 g c1 TMP_19) in (False_ind TMP_20 H5))))))))))))))))))) in 
(let TMP_31 \def (\lambda (c0: C).(\lambda (c2: C).(\lambda (_: (wf3 g c0 
c2)).(\lambda (_: (((eq C c0 (CHead c1 (Flat f) v)) \to (wf3 g c1 
c2)))).(\lambda (u: T).(\lambda (_: ((\forall (t: T).((ty3 g c0 u t) \to 
False)))).(\lambda (b: B).(\lambda (H4: (eq C (CHead c0 (Bind b) u) (CHead c1 
(Flat f) v))).(let TMP_22 \def (Bind b) in (let TMP_23 \def (CHead c0 TMP_22 
u) in (let TMP_24 \def (\lambda (ee: C).(match ee with [(CSort _) \Rightarrow 
False | (CHead _ k _) \Rightarrow (match k with [(Bind _) \Rightarrow True | 
(Flat _) \Rightarrow False])])) in (let TMP_25 \def (Flat f) in (let TMP_26 
\def (CHead c1 TMP_25 v) in (let H5 \def (eq_ind C TMP_23 TMP_24 I TMP_26 H4) 
in (let TMP_27 \def (Bind Void) in (let TMP_28 \def (TSort O) in (let TMP_29 
\def (CHead c2 TMP_27 TMP_28) in (let TMP_30 \def (wf3 g c1 TMP_29) in 
(False_ind TMP_30 H5))))))))))))))))))) in (let TMP_51 \def (\lambda (c0: 
C).(\lambda (c2: C).(\lambda (H1: (wf3 g c0 c2)).(\lambda (H2: (((eq C c0 
(CHead c1 (Flat f) v)) \to (wf3 g c1 c2)))).(\lambda (u: T).(\lambda (f0: 
F).(\lambda (H3: (eq C (CHead c0 (Flat f0) u) (CHead c1 (Flat f) v))).(let 
TMP_32 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow c0 | (CHead 
c _ _) \Rightarrow c])) in (let TMP_33 \def (Flat f0) in (let TMP_34 \def 
(CHead c0 TMP_33 u) in (let TMP_35 \def (Flat f) in (let TMP_36 \def (CHead 
c1 TMP_35 v) in (let H4 \def (f_equal C C TMP_32 TMP_34 TMP_36 H3) in (let 
TMP_37 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow f0 | (CHead 
_ k _) \Rightarrow (match k with [(Bind _) \Rightarrow f0 | (Flat f1) 
\Rightarrow f1])])) in (let TMP_38 \def (Flat f0) in (let TMP_39 \def (CHead 
c0 TMP_38 u) in (let TMP_40 \def (Flat f) in (let TMP_41 \def (CHead c1 
TMP_40 v) in (let H5 \def (f_equal C F TMP_37 TMP_39 TMP_41 H3) in (let 
TMP_42 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow u | (CHead _ 
_ t) \Rightarrow t])) in (let TMP_43 \def (Flat f0) in (let TMP_44 \def 
(CHead c0 TMP_43 u) in (let TMP_45 \def (Flat f) in (let TMP_46 \def (CHead 
c1 TMP_45 v) in (let H6 \def (f_equal C T TMP_42 TMP_44 TMP_46 H3) in (let 
TMP_49 \def (\lambda (_: (eq F f0 f)).(\lambda (H8: (eq C c0 c1)).(let TMP_47 
\def (\lambda (c: C).((eq C c (CHead c1 (Flat f) v)) \to (wf3 g c1 c2))) in 
(let H9 \def (eq_ind C c0 TMP_47 H2 c1 H8) in (let TMP_48 \def (\lambda (c: 
C).(wf3 g c c2)) in (let H10 \def (eq_ind C c0 TMP_48 H1 c1 H8) in H10)))))) 
in (let TMP_50 \def (TMP_49 H5) in (TMP_50 H4)))))))))))))))))))))))))))) in 
(wf3_ind g TMP_5 TMP_12 TMP_21 TMP_31 TMP_51 y x H0)))))))) in (insert_eq C 
TMP_2 TMP_3 TMP_4 TMP_52 H))))))))))).

theorem wf3_gen_head2:
 \forall (g: G).(\forall (x: C).(\forall (c: C).(\forall (v: T).(\forall (k: 
K).((wf3 g x (CHead c k v)) \to (ex B (\lambda (b: B).(eq K k (Bind b)))))))))
\def
 \lambda (g: G).(\lambda (x: C).(\lambda (c: C).(\lambda (v: T).(\lambda (k: 
K).(\lambda (H: (wf3 g x (CHead c k v))).(let TMP_1 \def (CHead c k v) in 
(let TMP_2 \def (\lambda (c0: C).(wf3 g x c0)) in (let TMP_5 \def (\lambda 
(_: C).(let TMP_4 \def (\lambda (b: B).(let TMP_3 \def (Bind b) in (eq K k 
TMP_3))) in (ex B TMP_4))) in (let TMP_102 \def (\lambda (y: C).(\lambda (H0: 
(wf3 g x y)).(let TMP_8 \def (\lambda (_: C).(\lambda (c1: C).((eq C c1 
(CHead c k v)) \to (let TMP_7 \def (\lambda (b: B).(let TMP_6 \def (Bind b) 
in (eq K k TMP_6))) in (ex B TMP_7))))) in (let TMP_15 \def (\lambda (m: 
nat).(\lambda (H1: (eq C (CSort m) (CHead c k v))).(let TMP_9 \def (CSort m) 
in (let TMP_10 \def (\lambda (ee: C).(match ee with [(CSort _) \Rightarrow 
True | (CHead _ _ _) \Rightarrow False])) in (let TMP_11 \def (CHead c k v) 
in (let H2 \def (eq_ind C TMP_9 TMP_10 I TMP_11 H1) in (let TMP_13 \def 
(\lambda (b: B).(let TMP_12 \def (Bind b) in (eq K k TMP_12))) in (let TMP_14 
\def (ex B TMP_13) in (False_ind TMP_14 H2))))))))) in (let TMP_49 \def 
(\lambda (c1: C).(\lambda (c2: C).(\lambda (H1: (wf3 g c1 c2)).(\lambda (H2: 
(((eq C c2 (CHead c k v)) \to (ex B (\lambda (b: B).(eq K k (Bind 
b))))))).(\lambda (u: T).(\lambda (t: T).(\lambda (H3: (ty3 g c1 u 
t)).(\lambda (b: B).(\lambda (H4: (eq C (CHead c2 (Bind b) u) (CHead c k 
v))).(let TMP_16 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow c2 
| (CHead c0 _ _) \Rightarrow c0])) in (let TMP_17 \def (Bind b) in (let 
TMP_18 \def (CHead c2 TMP_17 u) in (let TMP_19 \def (CHead c k v) in (let H5 
\def (f_equal C C TMP_16 TMP_18 TMP_19 H4) in (let TMP_20 \def (\lambda (e: 
C).(match e with [(CSort _) \Rightarrow (Bind b) | (CHead _ k0 _) \Rightarrow 
k0])) in (let TMP_21 \def (Bind b) in (let TMP_22 \def (CHead c2 TMP_21 u) in 
(let TMP_23 \def (CHead c k v) in (let H6 \def (f_equal C K TMP_20 TMP_22 
TMP_23 H4) in (let TMP_24 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) in (let TMP_25 \def (Bind b) 
in (let TMP_26 \def (CHead c2 TMP_25 u) in (let TMP_27 \def (CHead c k v) in 
(let H7 \def (f_equal C T TMP_24 TMP_26 TMP_27 H4) in (let TMP_47 \def 
(\lambda (H8: (eq K (Bind b) k)).(\lambda (H9: (eq C c2 c)).(let TMP_28 \def 
(\lambda (t0: T).(ty3 g c1 t0 t)) in (let H10 \def (eq_ind T u TMP_28 H3 v 
H7) in (let TMP_31 \def (\lambda (c0: C).((eq C c0 (CHead c k v)) \to (let 
TMP_30 \def (\lambda (b0: B).(let TMP_29 \def (Bind b0) in (eq K k TMP_29))) 
in (ex B TMP_30)))) in (let H11 \def (eq_ind C c2 TMP_31 H2 c H9) in (let 
TMP_32 \def (\lambda (c0: C).(wf3 g c1 c0)) in (let H12 \def (eq_ind C c2 
TMP_32 H1 c H9) in (let TMP_35 \def (\lambda (k0: K).((eq C c (CHead c k0 v)) 
\to (let TMP_34 \def (\lambda (b0: B).(let TMP_33 \def (Bind b0) in (eq K k0 
TMP_33))) in (ex B TMP_34)))) in (let TMP_36 \def (Bind b) in (let H13 \def 
(eq_ind_r K k TMP_35 H11 TMP_36 H8) in (let TMP_37 \def (Bind b) in (let 
TMP_40 \def (\lambda (k0: K).(let TMP_39 \def (\lambda (b0: B).(let TMP_38 
\def (Bind b0) in (eq K k0 TMP_38))) in (ex B TMP_39))) in (let TMP_43 \def 
(\lambda (b0: B).(let TMP_41 \def (Bind b) in (let TMP_42 \def (Bind b0) in 
(eq K TMP_41 TMP_42)))) in (let TMP_44 \def (Bind b) in (let TMP_45 \def 
(refl_equal K TMP_44) in (let TMP_46 \def (ex_intro B TMP_43 b TMP_45) in 
(eq_ind K TMP_37 TMP_40 TMP_46 k H8)))))))))))))))))) in (let TMP_48 \def 
(TMP_47 H6) in (TMP_48 H5))))))))))))))))))))))))))) in (let TMP_90 \def 
(\lambda (c1: C).(\lambda (c2: C).(\lambda (H1: (wf3 g c1 c2)).(\lambda (H2: 
(((eq C c2 (CHead c k v)) \to (ex B (\lambda (b: B).(eq K k (Bind 
b))))))).(\lambda (u: T).(\lambda (_: ((\forall (t: T).((ty3 g c1 u t) \to 
False)))).(\lambda (_: B).(\lambda (H4: (eq C (CHead c2 (Bind Void) (TSort 
O)) (CHead c k v))).(let TMP_50 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow c2 | (CHead c0 _ _) \Rightarrow c0])) in (let TMP_51 \def (Bind 
Void) in (let TMP_52 \def (TSort O) in (let TMP_53 \def (CHead c2 TMP_51 
TMP_52) in (let TMP_54 \def (CHead c k v) in (let H5 \def (f_equal C C TMP_50 
TMP_53 TMP_54 H4) in (let TMP_55 \def (\lambda (e: C).(match e with [(CSort 
_) \Rightarrow (Bind Void) | (CHead _ k0 _) \Rightarrow k0])) in (let TMP_56 
\def (Bind Void) in (let TMP_57 \def (TSort O) in (let TMP_58 \def (CHead c2 
TMP_56 TMP_57) in (let TMP_59 \def (CHead c k v) in (let H6 \def (f_equal C K 
TMP_55 TMP_58 TMP_59 H4) in (let TMP_60 \def (\lambda (e: C).(match e with 
[(CSort _) \Rightarrow (TSort O) | (CHead _ _ t) \Rightarrow t])) in (let 
TMP_61 \def (Bind Void) in (let TMP_62 \def (TSort O) in (let TMP_63 \def 
(CHead c2 TMP_61 TMP_62) in (let TMP_64 \def (CHead c k v) in (let H7 \def 
(f_equal C T TMP_60 TMP_63 TMP_64 H4) in (let TMP_88 \def (\lambda (H8: (eq K 
(Bind Void) k)).(\lambda (H9: (eq C c2 c)).(let TMP_67 \def (\lambda (c0: 
C).((eq C c0 (CHead c k v)) \to (let TMP_66 \def (\lambda (b0: B).(let TMP_65 
\def (Bind b0) in (eq K k TMP_65))) in (ex B TMP_66)))) in (let H10 \def 
(eq_ind C c2 TMP_67 H2 c H9) in (let TMP_68 \def (\lambda (c0: C).(wf3 g c1 
c0)) in (let H11 \def (eq_ind C c2 TMP_68 H1 c H9) in (let TMP_71 \def 
(\lambda (k0: K).((eq C c (CHead c k0 v)) \to (let TMP_70 \def (\lambda (b0: 
B).(let TMP_69 \def (Bind b0) in (eq K k0 TMP_69))) in (ex B TMP_70)))) in 
(let TMP_72 \def (Bind Void) in (let H12 \def (eq_ind_r K k TMP_71 H10 TMP_72 
H8) in (let TMP_73 \def (Bind Void) in (let TMP_76 \def (\lambda (k0: K).(let 
TMP_75 \def (\lambda (b0: B).(let TMP_74 \def (Bind b0) in (eq K k0 TMP_74))) 
in (ex B TMP_75))) in (let TMP_80 \def (\lambda (t: T).((eq C c (CHead c 
(Bind Void) t)) \to (let TMP_79 \def (\lambda (b0: B).(let TMP_77 \def (Bind 
Void) in (let TMP_78 \def (Bind b0) in (eq K TMP_77 TMP_78)))) in (ex B 
TMP_79)))) in (let TMP_81 \def (TSort O) in (let H13 \def (eq_ind_r T v 
TMP_80 H12 TMP_81 H7) in (let TMP_84 \def (\lambda (b0: B).(let TMP_82 \def 
(Bind Void) in (let TMP_83 \def (Bind b0) in (eq K TMP_82 TMP_83)))) in (let 
TMP_85 \def (Bind Void) in (let TMP_86 \def (refl_equal K TMP_85) in (let 
TMP_87 \def (ex_intro B TMP_84 Void TMP_86) in (eq_ind K TMP_73 TMP_76 TMP_87 
k H8))))))))))))))))))) in (let TMP_89 \def (TMP_88 H6) in (TMP_89 
H5))))))))))))))))))))))))))))) in (let TMP_101 \def (\lambda (c1: 
C).(\lambda (c2: C).(\lambda (H1: (wf3 g c1 c2)).(\lambda (H2: (((eq C c2 
(CHead c k v)) \to (ex B (\lambda (b: B).(eq K k (Bind b))))))).(\lambda (_: 
T).(\lambda (_: F).(\lambda (H3: (eq C c2 (CHead c k v))).(let TMP_91 \def 
(\lambda (e: C).e) in (let TMP_92 \def (CHead c k v) in (let H4 \def (f_equal 
C C TMP_91 c2 TMP_92 H3) in (let TMP_95 \def (\lambda (c0: C).((eq C c0 
(CHead c k v)) \to (let TMP_94 \def (\lambda (b: B).(let TMP_93 \def (Bind b) 
in (eq K k TMP_93))) in (ex B TMP_94)))) in (let TMP_96 \def (CHead c k v) in 
(let H5 \def (eq_ind C c2 TMP_95 H2 TMP_96 H4) in (let TMP_97 \def (\lambda 
(c0: C).(wf3 g c1 c0)) in (let TMP_98 \def (CHead c k v) in (let H6 \def 
(eq_ind C c2 TMP_97 H1 TMP_98 H4) in (let TMP_99 \def (CHead c k v) in (let 
TMP_100 \def (refl_equal C TMP_99) in (H5 TMP_100))))))))))))))))))) in 
(wf3_ind g TMP_8 TMP_15 TMP_49 TMP_90 TMP_101 x y H0)))))))) in (insert_eq C 
TMP_1 TMP_2 TMP_5 TMP_102 H)))))))))).

theorem wf3_mono:
 \forall (g: G).(\forall (c: C).(\forall (c1: C).((wf3 g c c1) \to (\forall 
(c2: C).((wf3 g c c2) \to (eq C c1 c2))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (c1: C).(\lambda (H: (wf3 g c 
c1)).(let TMP_1 \def (\lambda (c0: C).(\lambda (c2: C).(\forall (c3: C).((wf3 
g c0 c3) \to (eq C c2 c3))))) in (let TMP_7 \def (\lambda (m: nat).(\lambda 
(c2: C).(\lambda (H0: (wf3 g (CSort m) c2)).(let H_y \def (wf3_gen_sort1 g c2 
m H0) in (let TMP_2 \def (CSort m) in (let TMP_4 \def (\lambda (c0: C).(let 
TMP_3 \def (CSort m) in (eq C TMP_3 c0))) in (let TMP_5 \def (CSort m) in 
(let TMP_6 \def (refl_equal C TMP_5) in (eq_ind_r C TMP_2 TMP_4 TMP_6 c2 
H_y))))))))) in (let TMP_70 \def (\lambda (c2: C).(\lambda (c3: C).(\lambda 
(_: (wf3 g c2 c3)).(\lambda (H1: ((\forall (c4: C).((wf3 g c2 c4) \to (eq C 
c3 c4))))).(\lambda (u: T).(\lambda (t: T).(\lambda (H2: (ty3 g c2 u 
t)).(\lambda (b: B).(\lambda (c0: C).(\lambda (H3: (wf3 g (CHead c2 (Bind b) 
u) c0)).(let H_x \def (wf3_gen_bind1 g c2 c0 u b H3) in (let H4 \def H_x in 
(let TMP_10 \def (\lambda (c4: C).(\lambda (_: T).(let TMP_8 \def (Bind b) in 
(let TMP_9 \def (CHead c4 TMP_8 u) in (eq C c0 TMP_9))))) in (let TMP_11 \def 
(\lambda (c4: C).(\lambda (_: T).(wf3 g c2 c4))) in (let TMP_12 \def (\lambda 
(_: C).(\lambda (w: T).(ty3 g c2 u w))) in (let TMP_13 \def (ex3_2 C T TMP_10 
TMP_11 TMP_12) in (let TMP_17 \def (\lambda (c4: C).(let TMP_14 \def (Bind 
Void) in (let TMP_15 \def (TSort O) in (let TMP_16 \def (CHead c4 TMP_14 
TMP_15) in (eq C c0 TMP_16))))) in (let TMP_18 \def (\lambda (c4: C).(wf3 g 
c2 c4)) in (let TMP_19 \def (\lambda (_: C).(\forall (w: T).((ty3 g c2 u w) 
\to False))) in (let TMP_20 \def (ex3 C TMP_17 TMP_18 TMP_19) in (let TMP_21 
\def (Bind b) in (let TMP_22 \def (CHead c3 TMP_21 u) in (let TMP_23 \def (eq 
C TMP_22 c0) in (let TMP_45 \def (\lambda (H5: (ex3_2 C T (\lambda (c4: 
C).(\lambda (_: T).(eq C c0 (CHead c4 (Bind b) u)))) (\lambda (c4: 
C).(\lambda (_: T).(wf3 g c2 c4))) (\lambda (_: C).(\lambda (w: T).(ty3 g c2 
u w))))).(let TMP_26 \def (\lambda (c4: C).(\lambda (_: T).(let TMP_24 \def 
(Bind b) in (let TMP_25 \def (CHead c4 TMP_24 u) in (eq C c0 TMP_25))))) in 
(let TMP_27 \def (\lambda (c4: C).(\lambda (_: T).(wf3 g c2 c4))) in (let 
TMP_28 \def (\lambda (_: C).(\lambda (w: T).(ty3 g c2 u w))) in (let TMP_29 
\def (Bind b) in (let TMP_30 \def (CHead c3 TMP_29 u) in (let TMP_31 \def (eq 
C TMP_30 c0) in (let TMP_44 \def (\lambda (x0: C).(\lambda (x1: T).(\lambda 
(H6: (eq C c0 (CHead x0 (Bind b) u))).(\lambda (H7: (wf3 g c2 x0)).(\lambda 
(_: (ty3 g c2 u x1)).(let TMP_32 \def (Bind b) in (let TMP_33 \def (CHead x0 
TMP_32 u) in (let TMP_36 \def (\lambda (c4: C).(let TMP_34 \def (Bind b) in 
(let TMP_35 \def (CHead c3 TMP_34 u) in (eq C TMP_35 c4)))) in (let TMP_37 
\def (Bind b) in (let TMP_38 \def (Bind b) in (let TMP_39 \def (H1 x0 H7) in 
(let TMP_40 \def (Bind b) in (let TMP_41 \def (refl_equal K TMP_40) in (let 
TMP_42 \def (refl_equal T u) in (let TMP_43 \def (f_equal3 C K T C CHead c3 
x0 TMP_37 TMP_38 u u TMP_39 TMP_41 TMP_42) in (eq_ind_r C TMP_33 TMP_36 
TMP_43 c0 H6)))))))))))))))) in (ex3_2_ind C T TMP_26 TMP_27 TMP_28 TMP_31 
TMP_44 H5))))))))) in (let TMP_69 \def (\lambda (H5: (ex3 C (\lambda (c4: 
C).(eq C c0 (CHead c4 (Bind Void) (TSort O)))) (\lambda (c4: C).(wf3 g c2 
c4)) (\lambda (_: C).(\forall (w: T).((ty3 g c2 u w) \to False))))).(let 
TMP_49 \def (\lambda (c4: C).(let TMP_46 \def (Bind Void) in (let TMP_47 \def 
(TSort O) in (let TMP_48 \def (CHead c4 TMP_46 TMP_47) in (eq C c0 
TMP_48))))) in (let TMP_50 \def (\lambda (c4: C).(wf3 g c2 c4)) in (let 
TMP_51 \def (\lambda (_: C).(\forall (w: T).((ty3 g c2 u w) \to False))) in 
(let TMP_52 \def (Bind b) in (let TMP_53 \def (CHead c3 TMP_52 u) in (let 
TMP_54 \def (eq C TMP_53 c0) in (let TMP_68 \def (\lambda (x0: C).(\lambda 
(H6: (eq C c0 (CHead x0 (Bind Void) (TSort O)))).(\lambda (_: (wf3 g c2 
x0)).(\lambda (H8: ((\forall (w: T).((ty3 g c2 u w) \to False)))).(let TMP_55 
\def (Bind Void) in (let TMP_56 \def (TSort O) in (let TMP_57 \def (CHead x0 
TMP_55 TMP_56) in (let TMP_60 \def (\lambda (c4: C).(let TMP_58 \def (Bind b) 
in (let TMP_59 \def (CHead c3 TMP_58 u) in (eq C TMP_59 c4)))) in (let H_x0 
\def (H8 t H2) in (let H9 \def H_x0 in (let TMP_61 \def (Bind b) in (let 
TMP_62 \def (CHead c3 TMP_61 u) in (let TMP_63 \def (Bind Void) in (let 
TMP_64 \def (TSort O) in (let TMP_65 \def (CHead x0 TMP_63 TMP_64) in (let 
TMP_66 \def (eq C TMP_62 TMP_65) in (let TMP_67 \def (False_ind TMP_66 H9) in 
(eq_ind_r C TMP_57 TMP_60 TMP_67 c0 H6)))))))))))))))))) in (ex3_ind C TMP_49 
TMP_50 TMP_51 TMP_54 TMP_68 H5))))))))) in (or_ind TMP_13 TMP_20 TMP_23 
TMP_45 TMP_69 H4)))))))))))))))))))))))))) in (let TMP_141 \def (\lambda (c2: 
C).(\lambda (c3: C).(\lambda (_: (wf3 g c2 c3)).(\lambda (H1: ((\forall (c4: 
C).((wf3 g c2 c4) \to (eq C c3 c4))))).(\lambda (u: T).(\lambda (H2: 
((\forall (t: T).((ty3 g c2 u t) \to False)))).(\lambda (b: B).(\lambda (c0: 
C).(\lambda (H3: (wf3 g (CHead c2 (Bind b) u) c0)).(let H_x \def 
(wf3_gen_bind1 g c2 c0 u b H3) in (let H4 \def H_x in (let TMP_73 \def 
(\lambda (c4: C).(\lambda (_: T).(let TMP_71 \def (Bind b) in (let TMP_72 
\def (CHead c4 TMP_71 u) in (eq C c0 TMP_72))))) in (let TMP_74 \def (\lambda 
(c4: C).(\lambda (_: T).(wf3 g c2 c4))) in (let TMP_75 \def (\lambda (_: 
C).(\lambda (w: T).(ty3 g c2 u w))) in (let TMP_76 \def (ex3_2 C T TMP_73 
TMP_74 TMP_75) in (let TMP_80 \def (\lambda (c4: C).(let TMP_77 \def (Bind 
Void) in (let TMP_78 \def (TSort O) in (let TMP_79 \def (CHead c4 TMP_77 
TMP_78) in (eq C c0 TMP_79))))) in (let TMP_81 \def (\lambda (c4: C).(wf3 g 
c2 c4)) in (let TMP_82 \def (\lambda (_: C).(\forall (w: T).((ty3 g c2 u w) 
\to False))) in (let TMP_83 \def (ex3 C TMP_80 TMP_81 TMP_82) in (let TMP_84 
\def (Bind Void) in (let TMP_85 \def (TSort O) in (let TMP_86 \def (CHead c3 
TMP_84 TMP_85) in (let TMP_87 \def (eq C TMP_86 c0) in (let TMP_111 \def 
(\lambda (H5: (ex3_2 C T (\lambda (c4: C).(\lambda (_: T).(eq C c0 (CHead c4 
(Bind b) u)))) (\lambda (c4: C).(\lambda (_: T).(wf3 g c2 c4))) (\lambda (_: 
C).(\lambda (w: T).(ty3 g c2 u w))))).(let TMP_90 \def (\lambda (c4: 
C).(\lambda (_: T).(let TMP_88 \def (Bind b) in (let TMP_89 \def (CHead c4 
TMP_88 u) in (eq C c0 TMP_89))))) in (let TMP_91 \def (\lambda (c4: 
C).(\lambda (_: T).(wf3 g c2 c4))) in (let TMP_92 \def (\lambda (_: 
C).(\lambda (w: T).(ty3 g c2 u w))) in (let TMP_93 \def (Bind Void) in (let 
TMP_94 \def (TSort O) in (let TMP_95 \def (CHead c3 TMP_93 TMP_94) in (let 
TMP_96 \def (eq C TMP_95 c0) in (let TMP_110 \def (\lambda (x0: C).(\lambda 
(x1: T).(\lambda (H6: (eq C c0 (CHead x0 (Bind b) u))).(\lambda (_: (wf3 g c2 
x0)).(\lambda (H8: (ty3 g c2 u x1)).(let TMP_97 \def (Bind b) in (let TMP_98 
\def (CHead x0 TMP_97 u) in (let TMP_102 \def (\lambda (c4: C).(let TMP_99 
\def (Bind Void) in (let TMP_100 \def (TSort O) in (let TMP_101 \def (CHead 
c3 TMP_99 TMP_100) in (eq C TMP_101 c4))))) in (let H_x0 \def (H2 x1 H8) in 
(let H9 \def H_x0 in (let TMP_103 \def (Bind Void) in (let TMP_104 \def 
(TSort O) in (let TMP_105 \def (CHead c3 TMP_103 TMP_104) in (let TMP_106 
\def (Bind b) in (let TMP_107 \def (CHead x0 TMP_106 u) in (let TMP_108 \def 
(eq C TMP_105 TMP_107) in (let TMP_109 \def (False_ind TMP_108 H9) in 
(eq_ind_r C TMP_98 TMP_102 TMP_109 c0 H6)))))))))))))))))) in (ex3_2_ind C T 
TMP_90 TMP_91 TMP_92 TMP_96 TMP_110 H5)))))))))) in (let TMP_140 \def 
(\lambda (H5: (ex3 C (\lambda (c4: C).(eq C c0 (CHead c4 (Bind Void) (TSort 
O)))) (\lambda (c4: C).(wf3 g c2 c4)) (\lambda (_: C).(\forall (w: T).((ty3 g 
c2 u w) \to False))))).(let TMP_115 \def (\lambda (c4: C).(let TMP_112 \def 
(Bind Void) in (let TMP_113 \def (TSort O) in (let TMP_114 \def (CHead c4 
TMP_112 TMP_113) in (eq C c0 TMP_114))))) in (let TMP_116 \def (\lambda (c4: 
C).(wf3 g c2 c4)) in (let TMP_117 \def (\lambda (_: C).(\forall (w: T).((ty3 
g c2 u w) \to False))) in (let TMP_118 \def (Bind Void) in (let TMP_119 \def 
(TSort O) in (let TMP_120 \def (CHead c3 TMP_118 TMP_119) in (let TMP_121 
\def (eq C TMP_120 c0) in (let TMP_139 \def (\lambda (x0: C).(\lambda (H6: 
(eq C c0 (CHead x0 (Bind Void) (TSort O)))).(\lambda (H7: (wf3 g c2 
x0)).(\lambda (_: ((\forall (w: T).((ty3 g c2 u w) \to False)))).(let TMP_122 
\def (Bind Void) in (let TMP_123 \def (TSort O) in (let TMP_124 \def (CHead 
x0 TMP_122 TMP_123) in (let TMP_128 \def (\lambda (c4: C).(let TMP_125 \def 
(Bind Void) in (let TMP_126 \def (TSort O) in (let TMP_127 \def (CHead c3 
TMP_125 TMP_126) in (eq C TMP_127 c4))))) in (let TMP_129 \def (Bind Void) in 
(let TMP_130 \def (Bind Void) in (let TMP_131 \def (TSort O) in (let TMP_132 
\def (TSort O) in (let TMP_133 \def (H1 x0 H7) in (let TMP_134 \def (Bind 
Void) in (let TMP_135 \def (refl_equal K TMP_134) in (let TMP_136 \def (TSort 
O) in (let TMP_137 \def (refl_equal T TMP_136) in (let TMP_138 \def (f_equal3 
C K T C CHead c3 x0 TMP_129 TMP_130 TMP_131 TMP_132 TMP_133 TMP_135 TMP_137) 
in (eq_ind_r C TMP_124 TMP_128 TMP_138 c0 H6))))))))))))))))))) in (ex3_ind C 
TMP_115 TMP_116 TMP_117 TMP_121 TMP_139 H5)))))))))) in (or_ind TMP_76 TMP_83 
TMP_87 TMP_111 TMP_140 H4)))))))))))))))))))))))))) in (let TMP_142 \def 
(\lambda (c2: C).(\lambda (c3: C).(\lambda (_: (wf3 g c2 c3)).(\lambda (H1: 
((\forall (c4: C).((wf3 g c2 c4) \to (eq C c3 c4))))).(\lambda (u: 
T).(\lambda (f: F).(\lambda (c0: C).(\lambda (H2: (wf3 g (CHead c2 (Flat f) 
u) c0)).(let H_y \def (wf3_gen_flat1 g c2 c0 u f H2) in (H1 c0 H_y)))))))))) 
in (wf3_ind g TMP_1 TMP_7 TMP_70 TMP_141 TMP_142 c c1 H))))))))).

