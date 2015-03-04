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

include "basic_1/csuba/fwd.ma".

include "basic_1/clear/fwd.ma".

theorem csuba_clear_conf:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((csuba g c1 c2) \to 
(\forall (e1: C).((clear c1 e1) \to (ex2 C (\lambda (e2: C).(csuba g e1 e2)) 
(\lambda (e2: C).(clear c2 e2))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csuba g c1 
c2)).(let TMP_3 \def (\lambda (c: C).(\lambda (c0: C).(\forall (e1: 
C).((clear c e1) \to (let TMP_1 \def (\lambda (e2: C).(csuba g e1 e2)) in 
(let TMP_2 \def (\lambda (e2: C).(clear c0 e2)) in (ex2 C TMP_1 TMP_2))))))) 
in (let TMP_8 \def (\lambda (n: nat).(\lambda (e1: C).(\lambda (H0: (clear 
(CSort n) e1)).(let TMP_4 \def (\lambda (e2: C).(csuba g e1 e2)) in (let 
TMP_6 \def (\lambda (e2: C).(let TMP_5 \def (CSort n) in (clear TMP_5 e2))) 
in (let TMP_7 \def (ex2 C TMP_4 TMP_6) in (clear_gen_sort e1 n H0 
TMP_7))))))) in (let TMP_49 \def (\lambda (c3: C).(\lambda (c4: C).(\lambda 
(H0: (csuba g c3 c4)).(\lambda (H1: ((\forall (e1: C).((clear c3 e1) \to (ex2 
C (\lambda (e2: C).(csuba g e1 e2)) (\lambda (e2: C).(clear c4 
e2))))))).(\lambda (k: K).(\lambda (u: T).(\lambda (e1: C).(\lambda (H2: 
(clear (CHead c3 k u) e1)).(let TMP_12 \def (\lambda (k0: K).((clear (CHead 
c3 k0 u) e1) \to (let TMP_9 \def (\lambda (e2: C).(csuba g e1 e2)) in (let 
TMP_11 \def (\lambda (e2: C).(let TMP_10 \def (CHead c4 k0 u) in (clear 
TMP_10 e2))) in (ex2 C TMP_9 TMP_11))))) in (let TMP_33 \def (\lambda (b: 
B).(\lambda (H3: (clear (CHead c3 (Bind b) u) e1)).(let TMP_13 \def (Bind b) 
in (let TMP_14 \def (CHead c3 TMP_13 u) in (let TMP_19 \def (\lambda (c: 
C).(let TMP_15 \def (\lambda (e2: C).(csuba g c e2)) in (let TMP_18 \def 
(\lambda (e2: C).(let TMP_16 \def (Bind b) in (let TMP_17 \def (CHead c4 
TMP_16 u) in (clear TMP_17 e2)))) in (ex2 C TMP_15 TMP_18)))) in (let TMP_22 
\def (\lambda (e2: C).(let TMP_20 \def (Bind b) in (let TMP_21 \def (CHead c3 
TMP_20 u) in (csuba g TMP_21 e2)))) in (let TMP_25 \def (\lambda (e2: C).(let 
TMP_23 \def (Bind b) in (let TMP_24 \def (CHead c4 TMP_23 u) in (clear TMP_24 
e2)))) in (let TMP_26 \def (Bind b) in (let TMP_27 \def (CHead c4 TMP_26 u) 
in (let TMP_28 \def (Bind b) in (let TMP_29 \def (csuba_head g c3 c4 H0 
TMP_28 u) in (let TMP_30 \def (clear_bind b c4 u) in (let TMP_31 \def 
(ex_intro2 C TMP_22 TMP_25 TMP_27 TMP_29 TMP_30) in (let TMP_32 \def 
(clear_gen_bind b c3 e1 u H3) in (eq_ind_r C TMP_14 TMP_19 TMP_31 e1 
TMP_32))))))))))))))) in (let TMP_48 \def (\lambda (f: F).(\lambda (H3: 
(clear (CHead c3 (Flat f) u) e1)).(let TMP_34 \def (clear_gen_flat f c3 e1 u 
H3) in (let H4 \def (H1 e1 TMP_34) in (let TMP_35 \def (\lambda (e2: 
C).(csuba g e1 e2)) in (let TMP_36 \def (\lambda (e2: C).(clear c4 e2)) in 
(let TMP_37 \def (\lambda (e2: C).(csuba g e1 e2)) in (let TMP_40 \def 
(\lambda (e2: C).(let TMP_38 \def (Flat f) in (let TMP_39 \def (CHead c4 
TMP_38 u) in (clear TMP_39 e2)))) in (let TMP_41 \def (ex2 C TMP_37 TMP_40) 
in (let TMP_47 \def (\lambda (x: C).(\lambda (H5: (csuba g e1 x)).(\lambda 
(H6: (clear c4 x)).(let TMP_42 \def (\lambda (e2: C).(csuba g e1 e2)) in (let 
TMP_45 \def (\lambda (e2: C).(let TMP_43 \def (Flat f) in (let TMP_44 \def 
(CHead c4 TMP_43 u) in (clear TMP_44 e2)))) in (let TMP_46 \def (clear_flat 
c4 x H6 f u) in (ex_intro2 C TMP_42 TMP_45 x H5 TMP_46))))))) in (ex2_ind C 
TMP_35 TMP_36 TMP_41 TMP_47 H4))))))))))) in (K_ind TMP_12 TMP_33 TMP_48 k 
H2)))))))))))) in (let TMP_69 \def (\lambda (c3: C).(\lambda (c4: C).(\lambda 
(H0: (csuba g c3 c4)).(\lambda (_: ((\forall (e1: C).((clear c3 e1) \to (ex2 
C (\lambda (e2: C).(csuba g e1 e2)) (\lambda (e2: C).(clear c4 
e2))))))).(\lambda (b: B).(\lambda (H2: (not (eq B b Void))).(\lambda (u1: 
T).(\lambda (u2: T).(\lambda (e1: C).(\lambda (H3: (clear (CHead c3 (Bind 
Void) u1) e1)).(let TMP_50 \def (Bind Void) in (let TMP_51 \def (CHead c3 
TMP_50 u1) in (let TMP_56 \def (\lambda (c: C).(let TMP_52 \def (\lambda (e2: 
C).(csuba g c e2)) in (let TMP_55 \def (\lambda (e2: C).(let TMP_53 \def 
(Bind b) in (let TMP_54 \def (CHead c4 TMP_53 u2) in (clear TMP_54 e2)))) in 
(ex2 C TMP_52 TMP_55)))) in (let TMP_59 \def (\lambda (e2: C).(let TMP_57 
\def (Bind Void) in (let TMP_58 \def (CHead c3 TMP_57 u1) in (csuba g TMP_58 
e2)))) in (let TMP_62 \def (\lambda (e2: C).(let TMP_60 \def (Bind b) in (let 
TMP_61 \def (CHead c4 TMP_60 u2) in (clear TMP_61 e2)))) in (let TMP_63 \def 
(Bind b) in (let TMP_64 \def (CHead c4 TMP_63 u2) in (let TMP_65 \def 
(csuba_void g c3 c4 H0 b H2 u1 u2) in (let TMP_66 \def (clear_bind b c4 u2) 
in (let TMP_67 \def (ex_intro2 C TMP_59 TMP_62 TMP_64 TMP_65 TMP_66) in (let 
TMP_68 \def (clear_gen_bind Void c3 e1 u1 H3) in (eq_ind_r C TMP_51 TMP_56 
TMP_67 e1 TMP_68)))))))))))))))))))))) in (let TMP_89 \def (\lambda (c3: 
C).(\lambda (c4: C).(\lambda (H0: (csuba g c3 c4)).(\lambda (_: ((\forall 
(e1: C).((clear c3 e1) \to (ex2 C (\lambda (e2: C).(csuba g e1 e2)) (\lambda 
(e2: C).(clear c4 e2))))))).(\lambda (t: T).(\lambda (a: A).(\lambda (H2: 
(arity g c3 t (asucc g a))).(\lambda (u: T).(\lambda (H3: (arity g c4 u 
a)).(\lambda (e1: C).(\lambda (H4: (clear (CHead c3 (Bind Abst) t) e1)).(let 
TMP_70 \def (Bind Abst) in (let TMP_71 \def (CHead c3 TMP_70 t) in (let 
TMP_76 \def (\lambda (c: C).(let TMP_72 \def (\lambda (e2: C).(csuba g c e2)) 
in (let TMP_75 \def (\lambda (e2: C).(let TMP_73 \def (Bind Abbr) in (let 
TMP_74 \def (CHead c4 TMP_73 u) in (clear TMP_74 e2)))) in (ex2 C TMP_72 
TMP_75)))) in (let TMP_79 \def (\lambda (e2: C).(let TMP_77 \def (Bind Abst) 
in (let TMP_78 \def (CHead c3 TMP_77 t) in (csuba g TMP_78 e2)))) in (let 
TMP_82 \def (\lambda (e2: C).(let TMP_80 \def (Bind Abbr) in (let TMP_81 \def 
(CHead c4 TMP_80 u) in (clear TMP_81 e2)))) in (let TMP_83 \def (Bind Abbr) 
in (let TMP_84 \def (CHead c4 TMP_83 u) in (let TMP_85 \def (csuba_abst g c3 
c4 H0 t a H2 u H3) in (let TMP_86 \def (clear_bind Abbr c4 u) in (let TMP_87 
\def (ex_intro2 C TMP_79 TMP_82 TMP_84 TMP_85 TMP_86) in (let TMP_88 \def 
(clear_gen_bind Abst c3 e1 t H4) in (eq_ind_r C TMP_71 TMP_76 TMP_87 e1 
TMP_88))))))))))))))))))))))) in (csuba_ind g TMP_3 TMP_8 TMP_49 TMP_69 
TMP_89 c1 c2 H))))))))).

theorem csuba_clear_trans:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((csuba g c2 c1) \to 
(\forall (e1: C).((clear c1 e1) \to (ex2 C (\lambda (e2: C).(csuba g e2 e1)) 
(\lambda (e2: C).(clear c2 e2))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csuba g c2 
c1)).(let TMP_3 \def (\lambda (c: C).(\lambda (c0: C).(\forall (e1: 
C).((clear c0 e1) \to (let TMP_1 \def (\lambda (e2: C).(csuba g e2 e1)) in 
(let TMP_2 \def (\lambda (e2: C).(clear c e2)) in (ex2 C TMP_1 TMP_2))))))) 
in (let TMP_8 \def (\lambda (n: nat).(\lambda (e1: C).(\lambda (H0: (clear 
(CSort n) e1)).(let TMP_4 \def (\lambda (e2: C).(csuba g e2 e1)) in (let 
TMP_6 \def (\lambda (e2: C).(let TMP_5 \def (CSort n) in (clear TMP_5 e2))) 
in (let TMP_7 \def (ex2 C TMP_4 TMP_6) in (clear_gen_sort e1 n H0 
TMP_7))))))) in (let TMP_49 \def (\lambda (c3: C).(\lambda (c4: C).(\lambda 
(H0: (csuba g c3 c4)).(\lambda (H1: ((\forall (e1: C).((clear c4 e1) \to (ex2 
C (\lambda (e2: C).(csuba g e2 e1)) (\lambda (e2: C).(clear c3 
e2))))))).(\lambda (k: K).(\lambda (u: T).(\lambda (e1: C).(\lambda (H2: 
(clear (CHead c4 k u) e1)).(let TMP_12 \def (\lambda (k0: K).((clear (CHead 
c4 k0 u) e1) \to (let TMP_9 \def (\lambda (e2: C).(csuba g e2 e1)) in (let 
TMP_11 \def (\lambda (e2: C).(let TMP_10 \def (CHead c3 k0 u) in (clear 
TMP_10 e2))) in (ex2 C TMP_9 TMP_11))))) in (let TMP_33 \def (\lambda (b: 
B).(\lambda (H3: (clear (CHead c4 (Bind b) u) e1)).(let TMP_13 \def (Bind b) 
in (let TMP_14 \def (CHead c4 TMP_13 u) in (let TMP_19 \def (\lambda (c: 
C).(let TMP_15 \def (\lambda (e2: C).(csuba g e2 c)) in (let TMP_18 \def 
(\lambda (e2: C).(let TMP_16 \def (Bind b) in (let TMP_17 \def (CHead c3 
TMP_16 u) in (clear TMP_17 e2)))) in (ex2 C TMP_15 TMP_18)))) in (let TMP_22 
\def (\lambda (e2: C).(let TMP_20 \def (Bind b) in (let TMP_21 \def (CHead c4 
TMP_20 u) in (csuba g e2 TMP_21)))) in (let TMP_25 \def (\lambda (e2: C).(let 
TMP_23 \def (Bind b) in (let TMP_24 \def (CHead c3 TMP_23 u) in (clear TMP_24 
e2)))) in (let TMP_26 \def (Bind b) in (let TMP_27 \def (CHead c3 TMP_26 u) 
in (let TMP_28 \def (Bind b) in (let TMP_29 \def (csuba_head g c3 c4 H0 
TMP_28 u) in (let TMP_30 \def (clear_bind b c3 u) in (let TMP_31 \def 
(ex_intro2 C TMP_22 TMP_25 TMP_27 TMP_29 TMP_30) in (let TMP_32 \def 
(clear_gen_bind b c4 e1 u H3) in (eq_ind_r C TMP_14 TMP_19 TMP_31 e1 
TMP_32))))))))))))))) in (let TMP_48 \def (\lambda (f: F).(\lambda (H3: 
(clear (CHead c4 (Flat f) u) e1)).(let TMP_34 \def (clear_gen_flat f c4 e1 u 
H3) in (let H4 \def (H1 e1 TMP_34) in (let TMP_35 \def (\lambda (e2: 
C).(csuba g e2 e1)) in (let TMP_36 \def (\lambda (e2: C).(clear c3 e2)) in 
(let TMP_37 \def (\lambda (e2: C).(csuba g e2 e1)) in (let TMP_40 \def 
(\lambda (e2: C).(let TMP_38 \def (Flat f) in (let TMP_39 \def (CHead c3 
TMP_38 u) in (clear TMP_39 e2)))) in (let TMP_41 \def (ex2 C TMP_37 TMP_40) 
in (let TMP_47 \def (\lambda (x: C).(\lambda (H5: (csuba g x e1)).(\lambda 
(H6: (clear c3 x)).(let TMP_42 \def (\lambda (e2: C).(csuba g e2 e1)) in (let 
TMP_45 \def (\lambda (e2: C).(let TMP_43 \def (Flat f) in (let TMP_44 \def 
(CHead c3 TMP_43 u) in (clear TMP_44 e2)))) in (let TMP_46 \def (clear_flat 
c3 x H6 f u) in (ex_intro2 C TMP_42 TMP_45 x H5 TMP_46))))))) in (ex2_ind C 
TMP_35 TMP_36 TMP_41 TMP_47 H4))))))))))) in (K_ind TMP_12 TMP_33 TMP_48 k 
H2)))))))))))) in (let TMP_69 \def (\lambda (c3: C).(\lambda (c4: C).(\lambda 
(H0: (csuba g c3 c4)).(\lambda (_: ((\forall (e1: C).((clear c4 e1) \to (ex2 
C (\lambda (e2: C).(csuba g e2 e1)) (\lambda (e2: C).(clear c3 
e2))))))).(\lambda (b: B).(\lambda (H2: (not (eq B b Void))).(\lambda (u1: 
T).(\lambda (u2: T).(\lambda (e1: C).(\lambda (H3: (clear (CHead c4 (Bind b) 
u2) e1)).(let TMP_50 \def (Bind b) in (let TMP_51 \def (CHead c4 TMP_50 u2) 
in (let TMP_56 \def (\lambda (c: C).(let TMP_52 \def (\lambda (e2: C).(csuba 
g e2 c)) in (let TMP_55 \def (\lambda (e2: C).(let TMP_53 \def (Bind Void) in 
(let TMP_54 \def (CHead c3 TMP_53 u1) in (clear TMP_54 e2)))) in (ex2 C 
TMP_52 TMP_55)))) in (let TMP_59 \def (\lambda (e2: C).(let TMP_57 \def (Bind 
b) in (let TMP_58 \def (CHead c4 TMP_57 u2) in (csuba g e2 TMP_58)))) in (let 
TMP_62 \def (\lambda (e2: C).(let TMP_60 \def (Bind Void) in (let TMP_61 \def 
(CHead c3 TMP_60 u1) in (clear TMP_61 e2)))) in (let TMP_63 \def (Bind Void) 
in (let TMP_64 \def (CHead c3 TMP_63 u1) in (let TMP_65 \def (csuba_void g c3 
c4 H0 b H2 u1 u2) in (let TMP_66 \def (clear_bind Void c3 u1) in (let TMP_67 
\def (ex_intro2 C TMP_59 TMP_62 TMP_64 TMP_65 TMP_66) in (let TMP_68 \def 
(clear_gen_bind b c4 e1 u2 H3) in (eq_ind_r C TMP_51 TMP_56 TMP_67 e1 
TMP_68)))))))))))))))))))))) in (let TMP_89 \def (\lambda (c3: C).(\lambda 
(c4: C).(\lambda (H0: (csuba g c3 c4)).(\lambda (_: ((\forall (e1: C).((clear 
c4 e1) \to (ex2 C (\lambda (e2: C).(csuba g e2 e1)) (\lambda (e2: C).(clear 
c3 e2))))))).(\lambda (t: T).(\lambda (a: A).(\lambda (H2: (arity g c3 t 
(asucc g a))).(\lambda (u: T).(\lambda (H3: (arity g c4 u a)).(\lambda (e1: 
C).(\lambda (H4: (clear (CHead c4 (Bind Abbr) u) e1)).(let TMP_70 \def (Bind 
Abbr) in (let TMP_71 \def (CHead c4 TMP_70 u) in (let TMP_76 \def (\lambda 
(c: C).(let TMP_72 \def (\lambda (e2: C).(csuba g e2 c)) in (let TMP_75 \def 
(\lambda (e2: C).(let TMP_73 \def (Bind Abst) in (let TMP_74 \def (CHead c3 
TMP_73 t) in (clear TMP_74 e2)))) in (ex2 C TMP_72 TMP_75)))) in (let TMP_79 
\def (\lambda (e2: C).(let TMP_77 \def (Bind Abbr) in (let TMP_78 \def (CHead 
c4 TMP_77 u) in (csuba g e2 TMP_78)))) in (let TMP_82 \def (\lambda (e2: 
C).(let TMP_80 \def (Bind Abst) in (let TMP_81 \def (CHead c3 TMP_80 t) in 
(clear TMP_81 e2)))) in (let TMP_83 \def (Bind Abst) in (let TMP_84 \def 
(CHead c3 TMP_83 t) in (let TMP_85 \def (csuba_abst g c3 c4 H0 t a H2 u H3) 
in (let TMP_86 \def (clear_bind Abst c3 t) in (let TMP_87 \def (ex_intro2 C 
TMP_79 TMP_82 TMP_84 TMP_85 TMP_86) in (let TMP_88 \def (clear_gen_bind Abbr 
c4 e1 u H4) in (eq_ind_r C TMP_71 TMP_76 TMP_87 e1 
TMP_88))))))))))))))))))))))) in (csuba_ind g TMP_3 TMP_8 TMP_49 TMP_69 
TMP_89 c2 c1 H))))))))).

