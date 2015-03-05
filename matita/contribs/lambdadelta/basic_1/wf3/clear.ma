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

include "basic_1/wf3/fwd.ma".

include "basic_1/clear/fwd.ma".

theorem wf3_clear_conf:
 \forall (c1: C).(\forall (c: C).((clear c1 c) \to (\forall (g: G).(\forall 
(c2: C).((wf3 g c1 c2) \to (wf3 g c c2))))))
\def
 \lambda (c1: C).(\lambda (c: C).(\lambda (H: (clear c1 c)).(let TMP_1 \def 
(\lambda (c0: C).(\lambda (c2: C).(\forall (g: G).(\forall (c3: C).((wf3 g c0 
c3) \to (wf3 g c2 c3)))))) in (let TMP_2 \def (\lambda (b: B).(\lambda (e: 
C).(\lambda (u: T).(\lambda (g: G).(\lambda (c2: C).(\lambda (H0: (wf3 g 
(CHead e (Bind b) u) c2)).H0)))))) in (let TMP_3 \def (\lambda (e: 
C).(\lambda (c0: C).(\lambda (_: (clear e c0)).(\lambda (H1: ((\forall (g: 
G).(\forall (c2: C).((wf3 g e c2) \to (wf3 g c0 c2)))))).(\lambda (f: 
F).(\lambda (u: T).(\lambda (g: G).(\lambda (c2: C).(\lambda (H2: (wf3 g 
(CHead e (Flat f) u) c2)).(let H_y \def (wf3_gen_flat1 g e c2 u f H2) in (H1 
g c2 H_y))))))))))) in (clear_ind TMP_1 TMP_2 TMP_3 c1 c H)))))).

theorem clear_wf3_trans:
 \forall (c1: C).(\forall (d1: C).((clear c1 d1) \to (\forall (g: G).(\forall 
(d2: C).((wf3 g d1 d2) \to (ex2 C (\lambda (c2: C).(wf3 g c1 c2)) (\lambda 
(c2: C).(clear c2 d2))))))))
\def
 \lambda (c1: C).(\lambda (d1: C).(\lambda (H: (clear c1 d1)).(let TMP_3 \def 
(\lambda (c: C).(\lambda (c0: C).(\forall (g: G).(\forall (d2: C).((wf3 g c0 
d2) \to (let TMP_1 \def (\lambda (c2: C).(wf3 g c c2)) in (let TMP_2 \def 
(\lambda (c2: C).(clear c2 d2)) in (ex2 C TMP_1 TMP_2)))))))) in (let TMP_87 
\def (\lambda (b: B).(\lambda (e: C).(\lambda (u: T).(\lambda (g: G).(\lambda 
(d2: C).(\lambda (H0: (wf3 g (CHead e (Bind b) u) d2)).(let H_x \def 
(wf3_gen_bind1 g e d2 u b H0) in (let H1 \def H_x in (let TMP_6 \def (\lambda 
(c2: C).(\lambda (_: T).(let TMP_4 \def (Bind b) in (let TMP_5 \def (CHead c2 
TMP_4 u) in (eq C d2 TMP_5))))) in (let TMP_7 \def (\lambda (c2: C).(\lambda 
(_: T).(wf3 g e c2))) in (let TMP_8 \def (\lambda (_: C).(\lambda (w: T).(ty3 
g e u w))) in (let TMP_9 \def (ex3_2 C T TMP_6 TMP_7 TMP_8) in (let TMP_13 
\def (\lambda (c2: C).(let TMP_10 \def (Bind Void) in (let TMP_11 \def (TSort 
O) in (let TMP_12 \def (CHead c2 TMP_10 TMP_11) in (eq C d2 TMP_12))))) in 
(let TMP_14 \def (\lambda (c2: C).(wf3 g e c2)) in (let TMP_15 \def (\lambda 
(_: C).(\forall (w: T).((ty3 g e u w) \to False))) in (let TMP_16 \def (ex3 C 
TMP_13 TMP_14 TMP_15) in (let TMP_19 \def (\lambda (c2: C).(let TMP_17 \def 
(Bind b) in (let TMP_18 \def (CHead e TMP_17 u) in (wf3 g TMP_18 c2)))) in 
(let TMP_20 \def (\lambda (c2: C).(clear c2 d2)) in (let TMP_21 \def (ex2 C 
TMP_19 TMP_20) in (let TMP_51 \def (\lambda (H2: (ex3_2 C T (\lambda (c2: 
C).(\lambda (_: T).(eq C d2 (CHead c2 (Bind b) u)))) (\lambda (c2: 
C).(\lambda (_: T).(wf3 g e c2))) (\lambda (_: C).(\lambda (w: T).(ty3 g e u 
w))))).(let TMP_24 \def (\lambda (c2: C).(\lambda (_: T).(let TMP_22 \def 
(Bind b) in (let TMP_23 \def (CHead c2 TMP_22 u) in (eq C d2 TMP_23))))) in 
(let TMP_25 \def (\lambda (c2: C).(\lambda (_: T).(wf3 g e c2))) in (let 
TMP_26 \def (\lambda (_: C).(\lambda (w: T).(ty3 g e u w))) in (let TMP_29 
\def (\lambda (c2: C).(let TMP_27 \def (Bind b) in (let TMP_28 \def (CHead e 
TMP_27 u) in (wf3 g TMP_28 c2)))) in (let TMP_30 \def (\lambda (c2: C).(clear 
c2 d2)) in (let TMP_31 \def (ex2 C TMP_29 TMP_30) in (let TMP_50 \def 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (H3: (eq C d2 (CHead x0 (Bind b) 
u))).(\lambda (H4: (wf3 g e x0)).(\lambda (H5: (ty3 g e u x1)).(let TMP_32 
\def (Bind b) in (let TMP_33 \def (CHead x0 TMP_32 u) in (let TMP_38 \def 
(\lambda (c: C).(let TMP_36 \def (\lambda (c2: C).(let TMP_34 \def (Bind b) 
in (let TMP_35 \def (CHead e TMP_34 u) in (wf3 g TMP_35 c2)))) in (let TMP_37 
\def (\lambda (c2: C).(clear c2 c)) in (ex2 C TMP_36 TMP_37)))) in (let 
TMP_41 \def (\lambda (c2: C).(let TMP_39 \def (Bind b) in (let TMP_40 \def 
(CHead e TMP_39 u) in (wf3 g TMP_40 c2)))) in (let TMP_44 \def (\lambda (c2: 
C).(let TMP_42 \def (Bind b) in (let TMP_43 \def (CHead x0 TMP_42 u) in 
(clear c2 TMP_43)))) in (let TMP_45 \def (Bind b) in (let TMP_46 \def (CHead 
x0 TMP_45 u) in (let TMP_47 \def (wf3_bind g e x0 H4 u x1 H5 b) in (let 
TMP_48 \def (clear_bind b x0 u) in (let TMP_49 \def (ex_intro2 C TMP_41 
TMP_44 TMP_46 TMP_47 TMP_48) in (eq_ind_r C TMP_33 TMP_38 TMP_49 d2 
H3)))))))))))))))) in (ex3_2_ind C T TMP_24 TMP_25 TMP_26 TMP_31 TMP_50 
H2))))))))) in (let TMP_86 \def (\lambda (H2: (ex3 C (\lambda (c2: C).(eq C 
d2 (CHead c2 (Bind Void) (TSort O)))) (\lambda (c2: C).(wf3 g e c2)) (\lambda 
(_: C).(\forall (w: T).((ty3 g e u w) \to False))))).(let TMP_55 \def 
(\lambda (c2: C).(let TMP_52 \def (Bind Void) in (let TMP_53 \def (TSort O) 
in (let TMP_54 \def (CHead c2 TMP_52 TMP_53) in (eq C d2 TMP_54))))) in (let 
TMP_56 \def (\lambda (c2: C).(wf3 g e c2)) in (let TMP_57 \def (\lambda (_: 
C).(\forall (w: T).((ty3 g e u w) \to False))) in (let TMP_60 \def (\lambda 
(c2: C).(let TMP_58 \def (Bind b) in (let TMP_59 \def (CHead e TMP_58 u) in 
(wf3 g TMP_59 c2)))) in (let TMP_61 \def (\lambda (c2: C).(clear c2 d2)) in 
(let TMP_62 \def (ex2 C TMP_60 TMP_61) in (let TMP_85 \def (\lambda (x0: 
C).(\lambda (H3: (eq C d2 (CHead x0 (Bind Void) (TSort O)))).(\lambda (H4: 
(wf3 g e x0)).(\lambda (H5: ((\forall (w: T).((ty3 g e u w) \to 
False)))).(let TMP_63 \def (Bind Void) in (let TMP_64 \def (TSort O) in (let 
TMP_65 \def (CHead x0 TMP_63 TMP_64) in (let TMP_70 \def (\lambda (c: C).(let 
TMP_68 \def (\lambda (c2: C).(let TMP_66 \def (Bind b) in (let TMP_67 \def 
(CHead e TMP_66 u) in (wf3 g TMP_67 c2)))) in (let TMP_69 \def (\lambda (c2: 
C).(clear c2 c)) in (ex2 C TMP_68 TMP_69)))) in (let TMP_73 \def (\lambda 
(c2: C).(let TMP_71 \def (Bind b) in (let TMP_72 \def (CHead e TMP_71 u) in 
(wf3 g TMP_72 c2)))) in (let TMP_77 \def (\lambda (c2: C).(let TMP_74 \def 
(Bind Void) in (let TMP_75 \def (TSort O) in (let TMP_76 \def (CHead x0 
TMP_74 TMP_75) in (clear c2 TMP_76))))) in (let TMP_78 \def (Bind Void) in 
(let TMP_79 \def (TSort O) in (let TMP_80 \def (CHead x0 TMP_78 TMP_79) in 
(let TMP_81 \def (wf3_void g e x0 H4 u H5 b) in (let TMP_82 \def (TSort O) in 
(let TMP_83 \def (clear_bind Void x0 TMP_82) in (let TMP_84 \def (ex_intro2 C 
TMP_73 TMP_77 TMP_80 TMP_81 TMP_83) in (eq_ind_r C TMP_65 TMP_70 TMP_84 d2 
H3)))))))))))))))))) in (ex3_ind C TMP_55 TMP_56 TMP_57 TMP_62 TMP_85 
H2))))))))) in (or_ind TMP_9 TMP_16 TMP_21 TMP_51 TMP_86 
H1)))))))))))))))))))))) in (let TMP_101 \def (\lambda (e: C).(\lambda (c: 
C).(\lambda (_: (clear e c)).(\lambda (H1: ((\forall (g: G).(\forall (d2: 
C).((wf3 g c d2) \to (ex2 C (\lambda (c2: C).(wf3 g e c2)) (\lambda (c2: 
C).(clear c2 d2)))))))).(\lambda (f: F).(\lambda (u: T).(\lambda (g: 
G).(\lambda (d2: C).(\lambda (H2: (wf3 g c d2)).(let H_x \def (H1 g d2 H2) in 
(let H3 \def H_x in (let TMP_88 \def (\lambda (c2: C).(wf3 g e c2)) in (let 
TMP_89 \def (\lambda (c2: C).(clear c2 d2)) in (let TMP_92 \def (\lambda (c2: 
C).(let TMP_90 \def (Flat f) in (let TMP_91 \def (CHead e TMP_90 u) in (wf3 g 
TMP_91 c2)))) in (let TMP_93 \def (\lambda (c2: C).(clear c2 d2)) in (let 
TMP_94 \def (ex2 C TMP_92 TMP_93) in (let TMP_100 \def (\lambda (x: 
C).(\lambda (H4: (wf3 g e x)).(\lambda (H5: (clear x d2)).(let TMP_97 \def 
(\lambda (c2: C).(let TMP_95 \def (Flat f) in (let TMP_96 \def (CHead e 
TMP_95 u) in (wf3 g TMP_96 c2)))) in (let TMP_98 \def (\lambda (c2: C).(clear 
c2 d2)) in (let TMP_99 \def (wf3_flat g e x H4 u f) in (ex_intro2 C TMP_97 
TMP_98 x TMP_99 H5))))))) in (ex2_ind C TMP_88 TMP_89 TMP_94 TMP_100 
H3)))))))))))))))))) in (clear_ind TMP_3 TMP_87 TMP_101 c1 d1 H)))))).

