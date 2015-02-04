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

include "basic_1/T/fwd.ma".

theorem terms_props__bind_dec:
 \forall (b1: B).(\forall (b2: B).(or (eq B b1 b2) ((eq B b1 b2) \to (\forall 
(P: Prop).P))))
\def
 \lambda (b1: B).(let TMP_3 \def (\lambda (b: B).(\forall (b2: B).(let TMP_1 
\def (eq B b b2) in (let TMP_2 \def ((eq B b b2) \to (\forall (P: Prop).P)) 
in (or TMP_1 TMP_2))))) in (let TMP_21 \def (\lambda (b2: B).(let TMP_6 \def 
(\lambda (b: B).(let TMP_4 \def (eq B Abbr b) in (let TMP_5 \def ((eq B Abbr 
b) \to (\forall (P: Prop).P)) in (or TMP_4 TMP_5)))) in (let TMP_7 \def (eq B 
Abbr Abbr) in (let TMP_8 \def ((eq B Abbr Abbr) \to (\forall (P: Prop).P)) in 
(let TMP_9 \def (refl_equal B Abbr) in (let TMP_10 \def (or_introl TMP_7 
TMP_8 TMP_9) in (let TMP_11 \def (eq B Abbr Abst) in (let TMP_12 \def ((eq B 
Abbr Abst) \to (\forall (P: Prop).P)) in (let TMP_14 \def (\lambda (H: (eq B 
Abbr Abst)).(\lambda (P: Prop).(let TMP_13 \def (\lambda (ee: B).(match ee 
with [Abbr \Rightarrow True | Abst \Rightarrow False | Void \Rightarrow 
False])) in (let H0 \def (eq_ind B Abbr TMP_13 I Abst H) in (False_ind P 
H0))))) in (let TMP_15 \def (or_intror TMP_11 TMP_12 TMP_14) in (let TMP_16 
\def (eq B Abbr Void) in (let TMP_17 \def ((eq B Abbr Void) \to (\forall (P: 
Prop).P)) in (let TMP_19 \def (\lambda (H: (eq B Abbr Void)).(\lambda (P: 
Prop).(let TMP_18 \def (\lambda (ee: B).(match ee with [Abbr \Rightarrow True 
| Abst \Rightarrow False | Void \Rightarrow False])) in (let H0 \def (eq_ind 
B Abbr TMP_18 I Void H) in (False_ind P H0))))) in (let TMP_20 \def 
(or_intror TMP_16 TMP_17 TMP_19) in (B_ind TMP_6 TMP_10 TMP_15 TMP_20 
b2))))))))))))))) in (let TMP_39 \def (\lambda (b2: B).(let TMP_24 \def 
(\lambda (b: B).(let TMP_22 \def (eq B Abst b) in (let TMP_23 \def ((eq B 
Abst b) \to (\forall (P: Prop).P)) in (or TMP_22 TMP_23)))) in (let TMP_25 
\def (eq B Abst Abbr) in (let TMP_26 \def ((eq B Abst Abbr) \to (\forall (P: 
Prop).P)) in (let TMP_28 \def (\lambda (H: (eq B Abst Abbr)).(\lambda (P: 
Prop).(let TMP_27 \def (\lambda (ee: B).(match ee with [Abbr \Rightarrow 
False | Abst \Rightarrow True | Void \Rightarrow False])) in (let H0 \def 
(eq_ind B Abst TMP_27 I Abbr H) in (False_ind P H0))))) in (let TMP_29 \def 
(or_intror TMP_25 TMP_26 TMP_28) in (let TMP_30 \def (eq B Abst Abst) in (let 
TMP_31 \def ((eq B Abst Abst) \to (\forall (P: Prop).P)) in (let TMP_32 \def 
(refl_equal B Abst) in (let TMP_33 \def (or_introl TMP_30 TMP_31 TMP_32) in 
(let TMP_34 \def (eq B Abst Void) in (let TMP_35 \def ((eq B Abst Void) \to 
(\forall (P: Prop).P)) in (let TMP_37 \def (\lambda (H: (eq B Abst 
Void)).(\lambda (P: Prop).(let TMP_36 \def (\lambda (ee: B).(match ee with 
[Abbr \Rightarrow False | Abst \Rightarrow True | Void \Rightarrow False])) 
in (let H0 \def (eq_ind B Abst TMP_36 I Void H) in (False_ind P H0))))) in 
(let TMP_38 \def (or_intror TMP_34 TMP_35 TMP_37) in (B_ind TMP_24 TMP_29 
TMP_33 TMP_38 b2))))))))))))))) in (let TMP_57 \def (\lambda (b2: B).(let 
TMP_42 \def (\lambda (b: B).(let TMP_40 \def (eq B Void b) in (let TMP_41 
\def ((eq B Void b) \to (\forall (P: Prop).P)) in (or TMP_40 TMP_41)))) in 
(let TMP_43 \def (eq B Void Abbr) in (let TMP_44 \def ((eq B Void Abbr) \to 
(\forall (P: Prop).P)) in (let TMP_46 \def (\lambda (H: (eq B Void 
Abbr)).(\lambda (P: Prop).(let TMP_45 \def (\lambda (ee: B).(match ee with 
[Abbr \Rightarrow False | Abst \Rightarrow False | Void \Rightarrow True])) 
in (let H0 \def (eq_ind B Void TMP_45 I Abbr H) in (False_ind P H0))))) in 
(let TMP_47 \def (or_intror TMP_43 TMP_44 TMP_46) in (let TMP_48 \def (eq B 
Void Abst) in (let TMP_49 \def ((eq B Void Abst) \to (\forall (P: Prop).P)) 
in (let TMP_51 \def (\lambda (H: (eq B Void Abst)).(\lambda (P: Prop).(let 
TMP_50 \def (\lambda (ee: B).(match ee with [Abbr \Rightarrow False | Abst 
\Rightarrow False | Void \Rightarrow True])) in (let H0 \def (eq_ind B Void 
TMP_50 I Abst H) in (False_ind P H0))))) in (let TMP_52 \def (or_intror 
TMP_48 TMP_49 TMP_51) in (let TMP_53 \def (eq B Void Void) in (let TMP_54 
\def ((eq B Void Void) \to (\forall (P: Prop).P)) in (let TMP_55 \def 
(refl_equal B Void) in (let TMP_56 \def (or_introl TMP_53 TMP_54 TMP_55) in 
(B_ind TMP_42 TMP_47 TMP_52 TMP_56 b2))))))))))))))) in (B_ind TMP_3 TMP_21 
TMP_39 TMP_57 b1))))).

theorem bind_dec_not:
 \forall (b1: B).(\forall (b2: B).(or (eq B b1 b2) (not (eq B b1 b2))))
\def
 \lambda (b1: B).(\lambda (b2: B).(let H_x \def (terms_props__bind_dec b1 b2) 
in (let H \def H_x in (let TMP_1 \def (eq B b1 b2) in (let TMP_2 \def ((eq B 
b1 b2) \to (\forall (P: Prop).P)) in (let TMP_3 \def (eq B b1 b2) in (let 
TMP_4 \def ((eq B b1 b2) \to False) in (let TMP_5 \def (or TMP_3 TMP_4) in 
(let TMP_8 \def (\lambda (H0: (eq B b1 b2)).(let TMP_6 \def (eq B b1 b2) in 
(let TMP_7 \def ((eq B b1 b2) \to False) in (or_introl TMP_6 TMP_7 H0)))) in 
(let TMP_12 \def (\lambda (H0: (((eq B b1 b2) \to (\forall (P: 
Prop).P)))).(let TMP_9 \def (eq B b1 b2) in (let TMP_10 \def ((eq B b1 b2) 
\to False) in (let TMP_11 \def (\lambda (H1: (eq B b1 b2)).(H0 H1 False)) in 
(or_intror TMP_9 TMP_10 TMP_11))))) in (or_ind TMP_1 TMP_2 TMP_5 TMP_8 TMP_12 
H))))))))))).

theorem terms_props__flat_dec:
 \forall (f1: F).(\forall (f2: F).(or (eq F f1 f2) ((eq F f1 f2) \to (\forall 
(P: Prop).P))))
\def
 \lambda (f1: F).(let TMP_3 \def (\lambda (f: F).(\forall (f2: F).(let TMP_1 
\def (eq F f f2) in (let TMP_2 \def ((eq F f f2) \to (\forall (P: Prop).P)) 
in (or TMP_1 TMP_2))))) in (let TMP_16 \def (\lambda (f2: F).(let TMP_6 \def 
(\lambda (f: F).(let TMP_4 \def (eq F Appl f) in (let TMP_5 \def ((eq F Appl 
f) \to (\forall (P: Prop).P)) in (or TMP_4 TMP_5)))) in (let TMP_7 \def (eq F 
Appl Appl) in (let TMP_8 \def ((eq F Appl Appl) \to (\forall (P: Prop).P)) in 
(let TMP_9 \def (refl_equal F Appl) in (let TMP_10 \def (or_introl TMP_7 
TMP_8 TMP_9) in (let TMP_11 \def (eq F Appl Cast) in (let TMP_12 \def ((eq F 
Appl Cast) \to (\forall (P: Prop).P)) in (let TMP_14 \def (\lambda (H: (eq F 
Appl Cast)).(\lambda (P: Prop).(let TMP_13 \def (\lambda (ee: F).(match ee 
with [Appl \Rightarrow True | Cast \Rightarrow False])) in (let H0 \def 
(eq_ind F Appl TMP_13 I Cast H) in (False_ind P H0))))) in (let TMP_15 \def 
(or_intror TMP_11 TMP_12 TMP_14) in (F_ind TMP_6 TMP_10 TMP_15 f2))))))))))) 
in (let TMP_29 \def (\lambda (f2: F).(let TMP_19 \def (\lambda (f: F).(let 
TMP_17 \def (eq F Cast f) in (let TMP_18 \def ((eq F Cast f) \to (\forall (P: 
Prop).P)) in (or TMP_17 TMP_18)))) in (let TMP_20 \def (eq F Cast Appl) in 
(let TMP_21 \def ((eq F Cast Appl) \to (\forall (P: Prop).P)) in (let TMP_23 
\def (\lambda (H: (eq F Cast Appl)).(\lambda (P: Prop).(let TMP_22 \def 
(\lambda (ee: F).(match ee with [Appl \Rightarrow False | Cast \Rightarrow 
True])) in (let H0 \def (eq_ind F Cast TMP_22 I Appl H) in (False_ind P 
H0))))) in (let TMP_24 \def (or_intror TMP_20 TMP_21 TMP_23) in (let TMP_25 
\def (eq F Cast Cast) in (let TMP_26 \def ((eq F Cast Cast) \to (\forall (P: 
Prop).P)) in (let TMP_27 \def (refl_equal F Cast) in (let TMP_28 \def 
(or_introl TMP_25 TMP_26 TMP_27) in (F_ind TMP_19 TMP_24 TMP_28 f2))))))))))) 
in (F_ind TMP_3 TMP_16 TMP_29 f1)))).

theorem terms_props__kind_dec:
 \forall (k1: K).(\forall (k2: K).(or (eq K k1 k2) ((eq K k1 k2) \to (\forall 
(P: Prop).P))))
\def
 \lambda (k1: K).(let TMP_3 \def (\lambda (k: K).(\forall (k2: K).(let TMP_1 
\def (eq K k k2) in (let TMP_2 \def ((eq K k k2) \to (\forall (P: Prop).P)) 
in (or TMP_1 TMP_2))))) in (let TMP_49 \def (\lambda (b: B).(\lambda (k2: 
K).(let TMP_7 \def (\lambda (k: K).(let TMP_4 \def (Bind b) in (let TMP_5 
\def (eq K TMP_4 k) in (let TMP_6 \def ((eq K (Bind b) k) \to (\forall (P: 
Prop).P)) in (or TMP_5 TMP_6))))) in (let TMP_39 \def (\lambda (b0: B).(let 
H_x \def (terms_props__bind_dec b b0) in (let H \def H_x in (let TMP_8 \def 
(eq B b b0) in (let TMP_9 \def ((eq B b b0) \to (\forall (P: Prop).P)) in 
(let TMP_10 \def (Bind b) in (let TMP_11 \def (Bind b0) in (let TMP_12 \def 
(eq K TMP_10 TMP_11) in (let TMP_13 \def ((eq K (Bind b) (Bind b0)) \to 
(\forall (P: Prop).P)) in (let TMP_14 \def (or TMP_12 TMP_13) in (let TMP_27 
\def (\lambda (H0: (eq B b b0)).(let TMP_19 \def (\lambda (b1: B).(let TMP_15 
\def (Bind b) in (let TMP_16 \def (Bind b1) in (let TMP_17 \def (eq K TMP_15 
TMP_16) in (let TMP_18 \def ((eq K (Bind b) (Bind b1)) \to (\forall (P: 
Prop).P)) in (or TMP_17 TMP_18)))))) in (let TMP_20 \def (Bind b) in (let 
TMP_21 \def (Bind b) in (let TMP_22 \def (eq K TMP_20 TMP_21) in (let TMP_23 
\def ((eq K (Bind b) (Bind b)) \to (\forall (P: Prop).P)) in (let TMP_24 \def 
(Bind b) in (let TMP_25 \def (refl_equal K TMP_24) in (let TMP_26 \def 
(or_introl TMP_22 TMP_23 TMP_25) in (eq_ind B b TMP_19 TMP_26 b0 H0)))))))))) 
in (let TMP_38 \def (\lambda (H0: (((eq B b b0) \to (\forall (P: 
Prop).P)))).(let TMP_28 \def (Bind b) in (let TMP_29 \def (Bind b0) in (let 
TMP_30 \def (eq K TMP_28 TMP_29) in (let TMP_31 \def ((eq K (Bind b) (Bind 
b0)) \to (\forall (P: Prop).P)) in (let TMP_37 \def (\lambda (H1: (eq K (Bind 
b) (Bind b0))).(\lambda (P: Prop).(let TMP_32 \def (\lambda (e: K).(match e 
with [(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow b])) in (let TMP_33 
\def (Bind b) in (let TMP_34 \def (Bind b0) in (let H2 \def (f_equal K B 
TMP_32 TMP_33 TMP_34 H1) in (let TMP_35 \def (\lambda (b1: B).((eq B b b1) 
\to (\forall (P0: Prop).P0))) in (let H3 \def (eq_ind_r B b0 TMP_35 H0 b H2) 
in (let TMP_36 \def (refl_equal B b) in (H3 TMP_36 P)))))))))) in (or_intror 
TMP_30 TMP_31 TMP_37))))))) in (or_ind TMP_8 TMP_9 TMP_14 TMP_27 TMP_38 
H))))))))))))) in (let TMP_48 \def (\lambda (f: F).(let TMP_40 \def (Bind b) 
in (let TMP_41 \def (Flat f) in (let TMP_42 \def (eq K TMP_40 TMP_41) in (let 
TMP_43 \def ((eq K (Bind b) (Flat f)) \to (\forall (P: Prop).P)) in (let 
TMP_47 \def (\lambda (H: (eq K (Bind b) (Flat f))).(\lambda (P: Prop).(let 
TMP_44 \def (Bind b) in (let TMP_45 \def (\lambda (ee: K).(match ee with 
[(Bind _) \Rightarrow True | (Flat _) \Rightarrow False])) in (let TMP_46 
\def (Flat f) in (let H0 \def (eq_ind K TMP_44 TMP_45 I TMP_46 H) in 
(False_ind P H0))))))) in (or_intror TMP_42 TMP_43 TMP_47))))))) in (K_ind 
TMP_7 TMP_39 TMP_48 k2)))))) in (let TMP_95 \def (\lambda (f: F).(\lambda 
(k2: K).(let TMP_53 \def (\lambda (k: K).(let TMP_50 \def (Flat f) in (let 
TMP_51 \def (eq K TMP_50 k) in (let TMP_52 \def ((eq K (Flat f) k) \to 
(\forall (P: Prop).P)) in (or TMP_51 TMP_52))))) in (let TMP_62 \def (\lambda 
(b: B).(let TMP_54 \def (Flat f) in (let TMP_55 \def (Bind b) in (let TMP_56 
\def (eq K TMP_54 TMP_55) in (let TMP_57 \def ((eq K (Flat f) (Bind b)) \to 
(\forall (P: Prop).P)) in (let TMP_61 \def (\lambda (H: (eq K (Flat f) (Bind 
b))).(\lambda (P: Prop).(let TMP_58 \def (Flat f) in (let TMP_59 \def 
(\lambda (ee: K).(match ee with [(Bind _) \Rightarrow False | (Flat _) 
\Rightarrow True])) in (let TMP_60 \def (Bind b) in (let H0 \def (eq_ind K 
TMP_58 TMP_59 I TMP_60 H) in (False_ind P H0))))))) in (or_intror TMP_56 
TMP_57 TMP_61))))))) in (let TMP_94 \def (\lambda (f0: F).(let H_x \def 
(terms_props__flat_dec f f0) in (let H \def H_x in (let TMP_63 \def (eq F f 
f0) in (let TMP_64 \def ((eq F f f0) \to (\forall (P: Prop).P)) in (let 
TMP_65 \def (Flat f) in (let TMP_66 \def (Flat f0) in (let TMP_67 \def (eq K 
TMP_65 TMP_66) in (let TMP_68 \def ((eq K (Flat f) (Flat f0)) \to (\forall 
(P: Prop).P)) in (let TMP_69 \def (or TMP_67 TMP_68) in (let TMP_82 \def 
(\lambda (H0: (eq F f f0)).(let TMP_74 \def (\lambda (f1: F).(let TMP_70 \def 
(Flat f) in (let TMP_71 \def (Flat f1) in (let TMP_72 \def (eq K TMP_70 
TMP_71) in (let TMP_73 \def ((eq K (Flat f) (Flat f1)) \to (\forall (P: 
Prop).P)) in (or TMP_72 TMP_73)))))) in (let TMP_75 \def (Flat f) in (let 
TMP_76 \def (Flat f) in (let TMP_77 \def (eq K TMP_75 TMP_76) in (let TMP_78 
\def ((eq K (Flat f) (Flat f)) \to (\forall (P: Prop).P)) in (let TMP_79 \def 
(Flat f) in (let TMP_80 \def (refl_equal K TMP_79) in (let TMP_81 \def 
(or_introl TMP_77 TMP_78 TMP_80) in (eq_ind F f TMP_74 TMP_81 f0 H0)))))))))) 
in (let TMP_93 \def (\lambda (H0: (((eq F f f0) \to (\forall (P: 
Prop).P)))).(let TMP_83 \def (Flat f) in (let TMP_84 \def (Flat f0) in (let 
TMP_85 \def (eq K TMP_83 TMP_84) in (let TMP_86 \def ((eq K (Flat f) (Flat 
f0)) \to (\forall (P: Prop).P)) in (let TMP_92 \def (\lambda (H1: (eq K (Flat 
f) (Flat f0))).(\lambda (P: Prop).(let TMP_87 \def (\lambda (e: K).(match e 
with [(Bind _) \Rightarrow f | (Flat f1) \Rightarrow f1])) in (let TMP_88 
\def (Flat f) in (let TMP_89 \def (Flat f0) in (let H2 \def (f_equal K F 
TMP_87 TMP_88 TMP_89 H1) in (let TMP_90 \def (\lambda (f1: F).((eq F f f1) 
\to (\forall (P0: Prop).P0))) in (let H3 \def (eq_ind_r F f0 TMP_90 H0 f H2) 
in (let TMP_91 \def (refl_equal F f) in (H3 TMP_91 P)))))))))) in (or_intror 
TMP_85 TMP_86 TMP_92))))))) in (or_ind TMP_63 TMP_64 TMP_69 TMP_82 TMP_93 
H))))))))))))) in (K_ind TMP_53 TMP_62 TMP_94 k2)))))) in (K_ind TMP_3 TMP_49 
TMP_95 k1)))).

theorem term_dec:
 \forall (t1: T).(\forall (t2: T).(or (eq T t1 t2) ((eq T t1 t2) \to (\forall 
(P: Prop).P))))
\def
 \lambda (t1: T).(let TMP_3 \def (\lambda (t: T).(\forall (t2: T).(let TMP_1 
\def (eq T t t2) in (let TMP_2 \def ((eq T t t2) \to (\forall (P: Prop).P)) 
in (or TMP_1 TMP_2))))) in (let TMP_58 \def (\lambda (n: nat).(\lambda (t2: 
T).(let TMP_7 \def (\lambda (t: T).(let TMP_4 \def (TSort n) in (let TMP_5 
\def (eq T TMP_4 t) in (let TMP_6 \def ((eq T (TSort n) t) \to (\forall (P: 
Prop).P)) in (or TMP_5 TMP_6))))) in (let TMP_39 \def (\lambda (n0: nat).(let 
H_x \def (nat_dec n n0) in (let H \def H_x in (let TMP_8 \def (eq nat n n0) 
in (let TMP_9 \def ((eq nat n n0) \to (\forall (P: Prop).P)) in (let TMP_10 
\def (TSort n) in (let TMP_11 \def (TSort n0) in (let TMP_12 \def (eq T 
TMP_10 TMP_11) in (let TMP_13 \def ((eq T (TSort n) (TSort n0)) \to (\forall 
(P: Prop).P)) in (let TMP_14 \def (or TMP_12 TMP_13) in (let TMP_27 \def 
(\lambda (H0: (eq nat n n0)).(let TMP_19 \def (\lambda (n1: nat).(let TMP_15 
\def (TSort n) in (let TMP_16 \def (TSort n1) in (let TMP_17 \def (eq T 
TMP_15 TMP_16) in (let TMP_18 \def ((eq T (TSort n) (TSort n1)) \to (\forall 
(P: Prop).P)) in (or TMP_17 TMP_18)))))) in (let TMP_20 \def (TSort n) in 
(let TMP_21 \def (TSort n) in (let TMP_22 \def (eq T TMP_20 TMP_21) in (let 
TMP_23 \def ((eq T (TSort n) (TSort n)) \to (\forall (P: Prop).P)) in (let 
TMP_24 \def (TSort n) in (let TMP_25 \def (refl_equal T TMP_24) in (let 
TMP_26 \def (or_introl TMP_22 TMP_23 TMP_25) in (eq_ind nat n TMP_19 TMP_26 
n0 H0)))))))))) in (let TMP_38 \def (\lambda (H0: (((eq nat n n0) \to 
(\forall (P: Prop).P)))).(let TMP_28 \def (TSort n) in (let TMP_29 \def 
(TSort n0) in (let TMP_30 \def (eq T TMP_28 TMP_29) in (let TMP_31 \def ((eq 
T (TSort n) (TSort n0)) \to (\forall (P: Prop).P)) in (let TMP_37 \def 
(\lambda (H1: (eq T (TSort n) (TSort n0))).(\lambda (P: Prop).(let TMP_32 
\def (\lambda (e: T).(match e with [(TSort n1) \Rightarrow n1 | (TLRef _) 
\Rightarrow n | (THead _ _ _) \Rightarrow n])) in (let TMP_33 \def (TSort n) 
in (let TMP_34 \def (TSort n0) in (let H2 \def (f_equal T nat TMP_32 TMP_33 
TMP_34 H1) in (let TMP_35 \def (\lambda (n1: nat).((eq nat n n1) \to (\forall 
(P0: Prop).P0))) in (let H3 \def (eq_ind_r nat n0 TMP_35 H0 n H2) in (let 
TMP_36 \def (refl_equal nat n) in (H3 TMP_36 P)))))))))) in (or_intror TMP_30 
TMP_31 TMP_37))))))) in (or_ind TMP_8 TMP_9 TMP_14 TMP_27 TMP_38 
H))))))))))))) in (let TMP_48 \def (\lambda (n0: nat).(let TMP_40 \def (TSort 
n) in (let TMP_41 \def (TLRef n0) in (let TMP_42 \def (eq T TMP_40 TMP_41) in 
(let TMP_43 \def ((eq T (TSort n) (TLRef n0)) \to (\forall (P: Prop).P)) in 
(let TMP_47 \def (\lambda (H: (eq T (TSort n) (TLRef n0))).(\lambda (P: 
Prop).(let TMP_44 \def (TSort n) in (let TMP_45 \def (\lambda (ee: T).(match 
ee with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | (THead _ 
_ _) \Rightarrow False])) in (let TMP_46 \def (TLRef n0) in (let H0 \def 
(eq_ind T TMP_44 TMP_45 I TMP_46 H) in (False_ind P H0))))))) in (or_intror 
TMP_42 TMP_43 TMP_47))))))) in (let TMP_57 \def (\lambda (k: K).(\lambda (t: 
T).(\lambda (_: (or (eq T (TSort n) t) ((eq T (TSort n) t) \to (\forall (P: 
Prop).P)))).(\lambda (t0: T).(\lambda (_: (or (eq T (TSort n) t0) ((eq T 
(TSort n) t0) \to (\forall (P: Prop).P)))).(let TMP_49 \def (TSort n) in (let 
TMP_50 \def (THead k t t0) in (let TMP_51 \def (eq T TMP_49 TMP_50) in (let 
TMP_52 \def ((eq T (TSort n) (THead k t t0)) \to (\forall (P: Prop).P)) in 
(let TMP_56 \def (\lambda (H1: (eq T (TSort n) (THead k t t0))).(\lambda (P: 
Prop).(let TMP_53 \def (TSort n) in (let TMP_54 \def (\lambda (ee: T).(match 
ee with [(TSort _) \Rightarrow True | (TLRef _) \Rightarrow False | (THead _ 
_ _) \Rightarrow False])) in (let TMP_55 \def (THead k t t0) in (let H2 \def 
(eq_ind T TMP_53 TMP_54 I TMP_55 H1) in (False_ind P H2))))))) in (or_intror 
TMP_51 TMP_52 TMP_56))))))))))) in (T_ind TMP_7 TMP_39 TMP_48 TMP_57 
t2))))))) in (let TMP_113 \def (\lambda (n: nat).(\lambda (t2: T).(let TMP_62 
\def (\lambda (t: T).(let TMP_59 \def (TLRef n) in (let TMP_60 \def (eq T 
TMP_59 t) in (let TMP_61 \def ((eq T (TLRef n) t) \to (\forall (P: Prop).P)) 
in (or TMP_60 TMP_61))))) in (let TMP_71 \def (\lambda (n0: nat).(let TMP_63 
\def (TLRef n) in (let TMP_64 \def (TSort n0) in (let TMP_65 \def (eq T 
TMP_63 TMP_64) in (let TMP_66 \def ((eq T (TLRef n) (TSort n0)) \to (\forall 
(P: Prop).P)) in (let TMP_70 \def (\lambda (H: (eq T (TLRef n) (TSort 
n0))).(\lambda (P: Prop).(let TMP_67 \def (TLRef n) in (let TMP_68 \def 
(\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) in (let TMP_69 \def 
(TSort n0) in (let H0 \def (eq_ind T TMP_67 TMP_68 I TMP_69 H) in (False_ind 
P H0))))))) in (or_intror TMP_65 TMP_66 TMP_70))))))) in (let TMP_103 \def 
(\lambda (n0: nat).(let H_x \def (nat_dec n n0) in (let H \def H_x in (let 
TMP_72 \def (eq nat n n0) in (let TMP_73 \def ((eq nat n n0) \to (\forall (P: 
Prop).P)) in (let TMP_74 \def (TLRef n) in (let TMP_75 \def (TLRef n0) in 
(let TMP_76 \def (eq T TMP_74 TMP_75) in (let TMP_77 \def ((eq T (TLRef n) 
(TLRef n0)) \to (\forall (P: Prop).P)) in (let TMP_78 \def (or TMP_76 TMP_77) 
in (let TMP_91 \def (\lambda (H0: (eq nat n n0)).(let TMP_83 \def (\lambda 
(n1: nat).(let TMP_79 \def (TLRef n) in (let TMP_80 \def (TLRef n1) in (let 
TMP_81 \def (eq T TMP_79 TMP_80) in (let TMP_82 \def ((eq T (TLRef n) (TLRef 
n1)) \to (\forall (P: Prop).P)) in (or TMP_81 TMP_82)))))) in (let TMP_84 
\def (TLRef n) in (let TMP_85 \def (TLRef n) in (let TMP_86 \def (eq T TMP_84 
TMP_85) in (let TMP_87 \def ((eq T (TLRef n) (TLRef n)) \to (\forall (P: 
Prop).P)) in (let TMP_88 \def (TLRef n) in (let TMP_89 \def (refl_equal T 
TMP_88) in (let TMP_90 \def (or_introl TMP_86 TMP_87 TMP_89) in (eq_ind nat n 
TMP_83 TMP_90 n0 H0)))))))))) in (let TMP_102 \def (\lambda (H0: (((eq nat n 
n0) \to (\forall (P: Prop).P)))).(let TMP_92 \def (TLRef n) in (let TMP_93 
\def (TLRef n0) in (let TMP_94 \def (eq T TMP_92 TMP_93) in (let TMP_95 \def 
((eq T (TLRef n) (TLRef n0)) \to (\forall (P: Prop).P)) in (let TMP_101 \def 
(\lambda (H1: (eq T (TLRef n) (TLRef n0))).(\lambda (P: Prop).(let TMP_96 
\def (\lambda (e: T).(match e with [(TSort _) \Rightarrow n | (TLRef n1) 
\Rightarrow n1 | (THead _ _ _) \Rightarrow n])) in (let TMP_97 \def (TLRef n) 
in (let TMP_98 \def (TLRef n0) in (let H2 \def (f_equal T nat TMP_96 TMP_97 
TMP_98 H1) in (let TMP_99 \def (\lambda (n1: nat).((eq nat n n1) \to (\forall 
(P0: Prop).P0))) in (let H3 \def (eq_ind_r nat n0 TMP_99 H0 n H2) in (let 
TMP_100 \def (refl_equal nat n) in (H3 TMP_100 P)))))))))) in (or_intror 
TMP_94 TMP_95 TMP_101))))))) in (or_ind TMP_72 TMP_73 TMP_78 TMP_91 TMP_102 
H))))))))))))) in (let TMP_112 \def (\lambda (k: K).(\lambda (t: T).(\lambda 
(_: (or (eq T (TLRef n) t) ((eq T (TLRef n) t) \to (\forall (P: 
Prop).P)))).(\lambda (t0: T).(\lambda (_: (or (eq T (TLRef n) t0) ((eq T 
(TLRef n) t0) \to (\forall (P: Prop).P)))).(let TMP_104 \def (TLRef n) in 
(let TMP_105 \def (THead k t t0) in (let TMP_106 \def (eq T TMP_104 TMP_105) 
in (let TMP_107 \def ((eq T (TLRef n) (THead k t t0)) \to (\forall (P: 
Prop).P)) in (let TMP_111 \def (\lambda (H1: (eq T (TLRef n) (THead k t 
t0))).(\lambda (P: Prop).(let TMP_108 \def (TLRef n) in (let TMP_109 \def 
(\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) in (let TMP_110 \def 
(THead k t t0) in (let H2 \def (eq_ind T TMP_108 TMP_109 I TMP_110 H1) in 
(False_ind P H2))))))) in (or_intror TMP_106 TMP_107 TMP_111))))))))))) in 
(T_ind TMP_62 TMP_71 TMP_103 TMP_112 t2))))))) in (let TMP_250 \def (\lambda 
(k: K).(\lambda (t: T).(\lambda (H: ((\forall (t2: T).(or (eq T t t2) ((eq T 
t t2) \to (\forall (P: Prop).P)))))).(\lambda (t0: T).(\lambda (H0: ((\forall 
(t2: T).(or (eq T t0 t2) ((eq T t0 t2) \to (\forall (P: 
Prop).P)))))).(\lambda (t2: T).(let TMP_117 \def (\lambda (t3: T).(let 
TMP_114 \def (THead k t t0) in (let TMP_115 \def (eq T TMP_114 t3) in (let 
TMP_116 \def ((eq T (THead k t t0) t3) \to (\forall (P: Prop).P)) in (or 
TMP_115 TMP_116))))) in (let TMP_126 \def (\lambda (n: nat).(let TMP_118 \def 
(THead k t t0) in (let TMP_119 \def (TSort n) in (let TMP_120 \def (eq T 
TMP_118 TMP_119) in (let TMP_121 \def ((eq T (THead k t t0) (TSort n)) \to 
(\forall (P: Prop).P)) in (let TMP_125 \def (\lambda (H1: (eq T (THead k t 
t0) (TSort n))).(\lambda (P: Prop).(let TMP_122 \def (THead k t t0) in (let 
TMP_123 \def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | 
(TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow True])) in (let 
TMP_124 \def (TSort n) in (let H2 \def (eq_ind T TMP_122 TMP_123 I TMP_124 
H1) in (False_ind P H2))))))) in (or_intror TMP_120 TMP_121 TMP_125))))))) in 
(let TMP_135 \def (\lambda (n: nat).(let TMP_127 \def (THead k t t0) in (let 
TMP_128 \def (TLRef n) in (let TMP_129 \def (eq T TMP_127 TMP_128) in (let 
TMP_130 \def ((eq T (THead k t t0) (TLRef n)) \to (\forall (P: Prop).P)) in 
(let TMP_134 \def (\lambda (H1: (eq T (THead k t t0) (TLRef n))).(\lambda (P: 
Prop).(let TMP_131 \def (THead k t t0) in (let TMP_132 \def (\lambda (ee: 
T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) \Rightarrow False 
| (THead _ _ _) \Rightarrow True])) in (let TMP_133 \def (TLRef n) in (let H2 
\def (eq_ind T TMP_131 TMP_132 I TMP_133 H1) in (False_ind P H2))))))) in 
(or_intror TMP_129 TMP_130 TMP_134))))))) in (let TMP_249 \def (\lambda (k0: 
K).(\lambda (t3: T).(\lambda (H1: (or (eq T (THead k t t0) t3) ((eq T (THead 
k t t0) t3) \to (\forall (P: Prop).P)))).(\lambda (t4: T).(\lambda (H2: (or 
(eq T (THead k t t0) t4) ((eq T (THead k t t0) t4) \to (\forall (P: 
Prop).P)))).(let H_x \def (H t3) in (let H3 \def H_x in (let TMP_136 \def (eq 
T t t3) in (let TMP_137 \def ((eq T t t3) \to (\forall (P: Prop).P)) in (let 
TMP_138 \def (THead k t t0) in (let TMP_139 \def (THead k0 t3 t4) in (let 
TMP_140 \def (eq T TMP_138 TMP_139) in (let TMP_141 \def ((eq T (THead k t 
t0) (THead k0 t3 t4)) \to (\forall (P: Prop).P)) in (let TMP_142 \def (or 
TMP_140 TMP_141) in (let TMP_221 \def (\lambda (H4: (eq T t t3)).(let TMP_146 
\def (\lambda (t5: T).(let TMP_143 \def (THead k t t0) in (let TMP_144 \def 
(eq T TMP_143 t5) in (let TMP_145 \def ((eq T (THead k t t0) t5) \to (\forall 
(P: Prop).P)) in (or TMP_144 TMP_145))))) in (let H5 \def (eq_ind_r T t3 
TMP_146 H1 t H4) in (let TMP_151 \def (\lambda (t5: T).(let TMP_147 \def 
(THead k t t0) in (let TMP_148 \def (THead k0 t5 t4) in (let TMP_149 \def (eq 
T TMP_147 TMP_148) in (let TMP_150 \def ((eq T (THead k t t0) (THead k0 t5 
t4)) \to (\forall (P: Prop).P)) in (or TMP_149 TMP_150)))))) in (let H_x0 
\def (H0 t4) in (let H6 \def H_x0 in (let TMP_152 \def (eq T t0 t4) in (let 
TMP_153 \def ((eq T t0 t4) \to (\forall (P: Prop).P)) in (let TMP_154 \def 
(THead k t t0) in (let TMP_155 \def (THead k0 t t4) in (let TMP_156 \def (eq 
T TMP_154 TMP_155) in (let TMP_157 \def ((eq T (THead k t t0) (THead k0 t 
t4)) \to (\forall (P: Prop).P)) in (let TMP_158 \def (or TMP_156 TMP_157) in 
(let TMP_200 \def (\lambda (H7: (eq T t0 t4)).(let TMP_162 \def (\lambda (t5: 
T).(let TMP_159 \def (THead k t t0) in (let TMP_160 \def (eq T TMP_159 t5) in 
(let TMP_161 \def ((eq T (THead k t t0) t5) \to (\forall (P: Prop).P)) in (or 
TMP_160 TMP_161))))) in (let H8 \def (eq_ind_r T t4 TMP_162 H2 t0 H7) in (let 
TMP_167 \def (\lambda (t5: T).(let TMP_163 \def (THead k t t0) in (let 
TMP_164 \def (THead k0 t t5) in (let TMP_165 \def (eq T TMP_163 TMP_164) in 
(let TMP_166 \def ((eq T (THead k t t0) (THead k0 t t5)) \to (\forall (P: 
Prop).P)) in (or TMP_165 TMP_166)))))) in (let H_x1 \def 
(terms_props__kind_dec k k0) in (let H9 \def H_x1 in (let TMP_168 \def (eq K 
k k0) in (let TMP_169 \def ((eq K k k0) \to (\forall (P: Prop).P)) in (let 
TMP_170 \def (THead k t t0) in (let TMP_171 \def (THead k0 t t0) in (let 
TMP_172 \def (eq T TMP_170 TMP_171) in (let TMP_173 \def ((eq T (THead k t 
t0) (THead k0 t t0)) \to (\forall (P: Prop).P)) in (let TMP_174 \def (or 
TMP_172 TMP_173) in (let TMP_187 \def (\lambda (H10: (eq K k k0)).(let 
TMP_179 \def (\lambda (k1: K).(let TMP_175 \def (THead k t t0) in (let 
TMP_176 \def (THead k1 t t0) in (let TMP_177 \def (eq T TMP_175 TMP_176) in 
(let TMP_178 \def ((eq T (THead k t t0) (THead k1 t t0)) \to (\forall (P: 
Prop).P)) in (or TMP_177 TMP_178)))))) in (let TMP_180 \def (THead k t t0) in 
(let TMP_181 \def (THead k t t0) in (let TMP_182 \def (eq T TMP_180 TMP_181) 
in (let TMP_183 \def ((eq T (THead k t t0) (THead k t t0)) \to (\forall (P: 
Prop).P)) in (let TMP_184 \def (THead k t t0) in (let TMP_185 \def 
(refl_equal T TMP_184) in (let TMP_186 \def (or_introl TMP_182 TMP_183 
TMP_185) in (eq_ind K k TMP_179 TMP_186 k0 H10)))))))))) in (let TMP_198 \def 
(\lambda (H10: (((eq K k k0) \to (\forall (P: Prop).P)))).(let TMP_188 \def 
(THead k t t0) in (let TMP_189 \def (THead k0 t t0) in (let TMP_190 \def (eq 
T TMP_188 TMP_189) in (let TMP_191 \def ((eq T (THead k t t0) (THead k0 t 
t0)) \to (\forall (P: Prop).P)) in (let TMP_197 \def (\lambda (H11: (eq T 
(THead k t t0) (THead k0 t t0))).(\lambda (P: Prop).(let TMP_192 \def 
(\lambda (e: T).(match e with [(TSort _) \Rightarrow k | (TLRef _) 
\Rightarrow k | (THead k1 _ _) \Rightarrow k1])) in (let TMP_193 \def (THead 
k t t0) in (let TMP_194 \def (THead k0 t t0) in (let H12 \def (f_equal T K 
TMP_192 TMP_193 TMP_194 H11) in (let TMP_195 \def (\lambda (k1: K).((eq K k 
k1) \to (\forall (P0: Prop).P0))) in (let H13 \def (eq_ind_r K k0 TMP_195 H10 
k H12) in (let TMP_196 \def (refl_equal K k) in (H13 TMP_196 P)))))))))) in 
(or_intror TMP_190 TMP_191 TMP_197))))))) in (let TMP_199 \def (or_ind 
TMP_168 TMP_169 TMP_174 TMP_187 TMP_198 H9) in (eq_ind T t0 TMP_167 TMP_199 
t4 H7))))))))))))))))) in (let TMP_219 \def (\lambda (H7: (((eq T t0 t4) \to 
(\forall (P: Prop).P)))).(let TMP_201 \def (THead k t t0) in (let TMP_202 
\def (THead k0 t t4) in (let TMP_203 \def (eq T TMP_201 TMP_202) in (let 
TMP_204 \def ((eq T (THead k t t0) (THead k0 t t4)) \to (\forall (P: 
Prop).P)) in (let TMP_218 \def (\lambda (H8: (eq T (THead k t t0) (THead k0 t 
t4))).(\lambda (P: Prop).(let TMP_205 \def (\lambda (e: T).(match e with 
[(TSort _) \Rightarrow k | (TLRef _) \Rightarrow k | (THead k1 _ _) 
\Rightarrow k1])) in (let TMP_206 \def (THead k t t0) in (let TMP_207 \def 
(THead k0 t t4) in (let H9 \def (f_equal T K TMP_205 TMP_206 TMP_207 H8) in 
(let TMP_208 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow t0 | 
(TLRef _) \Rightarrow t0 | (THead _ _ t5) \Rightarrow t5])) in (let TMP_209 
\def (THead k t t0) in (let TMP_210 \def (THead k0 t t4) in (let H10 \def 
(f_equal T T TMP_208 TMP_209 TMP_210 H8) in (let TMP_217 \def (\lambda (_: 
(eq K k k0)).(let TMP_211 \def (\lambda (t5: T).((eq T t0 t5) \to (\forall 
(P0: Prop).P0))) in (let H12 \def (eq_ind_r T t4 TMP_211 H7 t0 H10) in (let 
TMP_215 \def (\lambda (t5: T).(let TMP_212 \def (THead k t t0) in (let 
TMP_213 \def (eq T TMP_212 t5) in (let TMP_214 \def ((eq T (THead k t t0) t5) 
\to (\forall (P0: Prop).P0)) in (or TMP_213 TMP_214))))) in (let H13 \def 
(eq_ind_r T t4 TMP_215 H2 t0 H10) in (let TMP_216 \def (refl_equal T t0) in 
(H12 TMP_216 P))))))) in (TMP_217 H9)))))))))))) in (or_intror TMP_203 
TMP_204 TMP_218))))))) in (let TMP_220 \def (or_ind TMP_152 TMP_153 TMP_158 
TMP_200 TMP_219 H6) in (eq_ind T t TMP_151 TMP_220 t3 H4))))))))))))))))) in 
(let TMP_248 \def (\lambda (H4: (((eq T t t3) \to (\forall (P: 
Prop).P)))).(let TMP_222 \def (THead k t t0) in (let TMP_223 \def (THead k0 
t3 t4) in (let TMP_224 \def (eq T TMP_222 TMP_223) in (let TMP_225 \def ((eq 
T (THead k t t0) (THead k0 t3 t4)) \to (\forall (P: Prop).P)) in (let TMP_247 
\def (\lambda (H5: (eq T (THead k t t0) (THead k0 t3 t4))).(\lambda (P: 
Prop).(let TMP_226 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow 
k | (TLRef _) \Rightarrow k | (THead k1 _ _) \Rightarrow k1])) in (let 
TMP_227 \def (THead k t t0) in (let TMP_228 \def (THead k0 t3 t4) in (let H6 
\def (f_equal T K TMP_226 TMP_227 TMP_228 H5) in (let TMP_229 \def (\lambda 
(e: T).(match e with [(TSort _) \Rightarrow t | (TLRef _) \Rightarrow t | 
(THead _ t5 _) \Rightarrow t5])) in (let TMP_230 \def (THead k t t0) in (let 
TMP_231 \def (THead k0 t3 t4) in (let H7 \def (f_equal T T TMP_229 TMP_230 
TMP_231 H5) in (let TMP_232 \def (\lambda (e: T).(match e with [(TSort _) 
\Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ _ t5) \Rightarrow t5])) 
in (let TMP_233 \def (THead k t t0) in (let TMP_234 \def (THead k0 t3 t4) in 
(let H8 \def (f_equal T T TMP_232 TMP_233 TMP_234 H5) in (let TMP_245 \def 
(\lambda (H9: (eq T t t3)).(\lambda (_: (eq K k k0)).(let TMP_238 \def 
(\lambda (t5: T).(let TMP_235 \def (THead k t t0) in (let TMP_236 \def (eq T 
TMP_235 t5) in (let TMP_237 \def ((eq T (THead k t t0) t5) \to (\forall (P0: 
Prop).P0)) in (or TMP_236 TMP_237))))) in (let H11 \def (eq_ind_r T t4 
TMP_238 H2 t0 H8) in (let TMP_239 \def (\lambda (t5: T).((eq T t t5) \to 
(\forall (P0: Prop).P0))) in (let H12 \def (eq_ind_r T t3 TMP_239 H4 t H9) in 
(let TMP_243 \def (\lambda (t5: T).(let TMP_240 \def (THead k t t0) in (let 
TMP_241 \def (eq T TMP_240 t5) in (let TMP_242 \def ((eq T (THead k t t0) t5) 
\to (\forall (P0: Prop).P0)) in (or TMP_241 TMP_242))))) in (let H13 \def 
(eq_ind_r T t3 TMP_243 H1 t H9) in (let TMP_244 \def (refl_equal T t) in (H12 
TMP_244 P)))))))))) in (let TMP_246 \def (TMP_245 H7) in (TMP_246 
H6))))))))))))))))) in (or_intror TMP_224 TMP_225 TMP_247))))))) in (or_ind 
TMP_136 TMP_137 TMP_142 TMP_221 TMP_248 H3))))))))))))))))) in (T_ind TMP_117 
TMP_126 TMP_135 TMP_249 t2))))))))))) in (T_ind TMP_3 TMP_58 TMP_113 TMP_250 
t1))))).

theorem binder_dec:
 \forall (t: T).(or (ex_3 B T T (\lambda (b: B).(\lambda (w: T).(\lambda (u: 
T).(eq T t (THead (Bind b) w u)))))) (\forall (b: B).(\forall (w: T).(\forall 
(u: T).((eq T t (THead (Bind b) w u)) \to (\forall (P: Prop).P))))))
\def
 \lambda (t: T).(let TMP_6 \def (\lambda (t0: T).(let TMP_3 \def (\lambda (b: 
B).(\lambda (w: T).(\lambda (u: T).(let TMP_1 \def (Bind b) in (let TMP_2 
\def (THead TMP_1 w u) in (eq T t0 TMP_2)))))) in (let TMP_4 \def (ex_3 B T T 
TMP_3) in (let TMP_5 \def (\forall (b: B).(\forall (w: T).(\forall (u: 
T).((eq T t0 (THead (Bind b) w u)) \to (\forall (P: Prop).P))))) in (or TMP_4 
TMP_5))))) in (let TMP_18 \def (\lambda (n: nat).(let TMP_10 \def (\lambda 
(b: B).(\lambda (w: T).(\lambda (u: T).(let TMP_7 \def (TSort n) in (let 
TMP_8 \def (Bind b) in (let TMP_9 \def (THead TMP_8 w u) in (eq T TMP_7 
TMP_9))))))) in (let TMP_11 \def (ex_3 B T T TMP_10) in (let TMP_12 \def 
(\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T (TSort n) (THead (Bind 
b) w u)) \to (\forall (P: Prop).P))))) in (let TMP_17 \def (\lambda (b: 
B).(\lambda (w: T).(\lambda (u: T).(\lambda (H: (eq T (TSort n) (THead (Bind 
b) w u))).(\lambda (P: Prop).(let TMP_13 \def (TSort n) in (let TMP_14 \def 
(\lambda (ee: T).(match ee with [(TSort _) \Rightarrow True | (TLRef _) 
\Rightarrow False | (THead _ _ _) \Rightarrow False])) in (let TMP_15 \def 
(Bind b) in (let TMP_16 \def (THead TMP_15 w u) in (let H0 \def (eq_ind T 
TMP_13 TMP_14 I TMP_16 H) in (False_ind P H0))))))))))) in (or_intror TMP_11 
TMP_12 TMP_17)))))) in (let TMP_30 \def (\lambda (n: nat).(let TMP_22 \def 
(\lambda (b: B).(\lambda (w: T).(\lambda (u: T).(let TMP_19 \def (TLRef n) in 
(let TMP_20 \def (Bind b) in (let TMP_21 \def (THead TMP_20 w u) in (eq T 
TMP_19 TMP_21))))))) in (let TMP_23 \def (ex_3 B T T TMP_22) in (let TMP_24 
\def (\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T (TLRef n) (THead 
(Bind b) w u)) \to (\forall (P: Prop).P))))) in (let TMP_29 \def (\lambda (b: 
B).(\lambda (w: T).(\lambda (u: T).(\lambda (H: (eq T (TLRef n) (THead (Bind 
b) w u))).(\lambda (P: Prop).(let TMP_25 \def (TLRef n) in (let TMP_26 \def 
(\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False | (TLRef _) 
\Rightarrow True | (THead _ _ _) \Rightarrow False])) in (let TMP_27 \def 
(Bind b) in (let TMP_28 \def (THead TMP_27 w u) in (let H0 \def (eq_ind T 
TMP_25 TMP_26 I TMP_28 H) in (False_ind P H0))))))))))) in (or_intror TMP_23 
TMP_24 TMP_29)))))) in (let TMP_69 \def (\lambda (k: K).(let TMP_37 \def 
(\lambda (k0: K).(\forall (t0: T).((or (ex_3 B T T (\lambda (b: B).(\lambda 
(w: T).(\lambda (u: T).(eq T t0 (THead (Bind b) w u)))))) (\forall (b: 
B).(\forall (w: T).(\forall (u: T).((eq T t0 (THead (Bind b) w u)) \to 
(\forall (P: Prop).P)))))) \to (\forall (t1: T).((or (ex_3 B T T (\lambda (b: 
B).(\lambda (w: T).(\lambda (u: T).(eq T t1 (THead (Bind b) w u)))))) 
(\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T t1 (THead (Bind b) w 
u)) \to (\forall (P: Prop).P)))))) \to (let TMP_34 \def (\lambda (b: 
B).(\lambda (w: T).(\lambda (u: T).(let TMP_31 \def (THead k0 t0 t1) in (let 
TMP_32 \def (Bind b) in (let TMP_33 \def (THead TMP_32 w u) in (eq T TMP_31 
TMP_33))))))) in (let TMP_35 \def (ex_3 B T T TMP_34) in (let TMP_36 \def 
(\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T (THead k0 t0 t1) 
(THead (Bind b) w u)) \to (\forall (P: Prop).P))))) in (or TMP_35 
TMP_36))))))))) in (let TMP_54 \def (\lambda (b: B).(\lambda (t0: T).(\lambda 
(_: (or (ex_3 B T T (\lambda (b0: B).(\lambda (w: T).(\lambda (u: T).(eq T t0 
(THead (Bind b0) w u)))))) (\forall (b0: B).(\forall (w: T).(\forall (u: 
T).((eq T t0 (THead (Bind b0) w u)) \to (\forall (P: Prop).P))))))).(\lambda 
(t1: T).(\lambda (_: (or (ex_3 B T T (\lambda (b0: B).(\lambda (w: 
T).(\lambda (u: T).(eq T t1 (THead (Bind b0) w u)))))) (\forall (b0: 
B).(\forall (w: T).(\forall (u: T).((eq T t1 (THead (Bind b0) w u)) \to 
(\forall (P: Prop).P))))))).(let TMP_42 \def (\lambda (b0: B).(\lambda (w: 
T).(\lambda (u: T).(let TMP_38 \def (Bind b) in (let TMP_39 \def (THead 
TMP_38 t0 t1) in (let TMP_40 \def (Bind b0) in (let TMP_41 \def (THead TMP_40 
w u) in (eq T TMP_39 TMP_41)))))))) in (let TMP_43 \def (ex_3 B T T TMP_42) 
in (let TMP_44 \def (\forall (b0: B).(\forall (w: T).(\forall (u: T).((eq T 
(THead (Bind b) t0 t1) (THead (Bind b0) w u)) \to (\forall (P: Prop).P))))) 
in (let TMP_49 \def (\lambda (b0: B).(\lambda (w: T).(\lambda (u: T).(let 
TMP_45 \def (Bind b) in (let TMP_46 \def (THead TMP_45 t0 t1) in (let TMP_47 
\def (Bind b0) in (let TMP_48 \def (THead TMP_47 w u) in (eq T TMP_46 
TMP_48)))))))) in (let TMP_50 \def (Bind b) in (let TMP_51 \def (THead TMP_50 
t0 t1) in (let TMP_52 \def (refl_equal T TMP_51) in (let TMP_53 \def 
(ex_3_intro B T T TMP_49 b t0 t1 TMP_52) in (or_introl TMP_43 TMP_44 
TMP_53)))))))))))))) in (let TMP_68 \def (\lambda (f: F).(\lambda (t0: 
T).(\lambda (_: (or (ex_3 B T T (\lambda (b: B).(\lambda (w: T).(\lambda (u: 
T).(eq T t0 (THead (Bind b) w u)))))) (\forall (b: B).(\forall (w: 
T).(\forall (u: T).((eq T t0 (THead (Bind b) w u)) \to (\forall (P: 
Prop).P))))))).(\lambda (t1: T).(\lambda (_: (or (ex_3 B T T (\lambda (b: 
B).(\lambda (w: T).(\lambda (u: T).(eq T t1 (THead (Bind b) w u)))))) 
(\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T t1 (THead (Bind b) w 
u)) \to (\forall (P: Prop).P))))))).(let TMP_59 \def (\lambda (b: B).(\lambda 
(w: T).(\lambda (u: T).(let TMP_55 \def (Flat f) in (let TMP_56 \def (THead 
TMP_55 t0 t1) in (let TMP_57 \def (Bind b) in (let TMP_58 \def (THead TMP_57 
w u) in (eq T TMP_56 TMP_58)))))))) in (let TMP_60 \def (ex_3 B T T TMP_59) 
in (let TMP_61 \def (\forall (b: B).(\forall (w: T).(\forall (u: T).((eq T 
(THead (Flat f) t0 t1) (THead (Bind b) w u)) \to (\forall (P: Prop).P))))) in 
(let TMP_67 \def (\lambda (b: B).(\lambda (w: T).(\lambda (u: T).(\lambda 
(H1: (eq T (THead (Flat f) t0 t1) (THead (Bind b) w u))).(\lambda (P: 
Prop).(let TMP_62 \def (Flat f) in (let TMP_63 \def (THead TMP_62 t0 t1) in 
(let TMP_64 \def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False 
| (TLRef _) \Rightarrow False | (THead k0 _ _) \Rightarrow (match k0 with 
[(Bind _) \Rightarrow False | (Flat _) \Rightarrow True])])) in (let TMP_65 
\def (Bind b) in (let TMP_66 \def (THead TMP_65 w u) in (let H2 \def (eq_ind 
T TMP_63 TMP_64 I TMP_66 H1) in (False_ind P H2)))))))))))) in (or_intror 
TMP_60 TMP_61 TMP_67)))))))))) in (K_ind TMP_37 TMP_54 TMP_68 k))))) in 
(T_ind TMP_6 TMP_18 TMP_30 TMP_69 t))))).

theorem abst_dec:
 \forall (u: T).(\forall (v: T).(or (ex T (\lambda (t: T).(eq T u (THead 
(Bind Abst) v t)))) (\forall (t: T).((eq T u (THead (Bind Abst) v t)) \to 
(\forall (P: Prop).P)))))
\def
 \lambda (u: T).(let TMP_6 \def (\lambda (t: T).(\forall (v: T).(let TMP_3 
\def (\lambda (t0: T).(let TMP_1 \def (Bind Abst) in (let TMP_2 \def (THead 
TMP_1 v t0) in (eq T t TMP_2)))) in (let TMP_4 \def (ex T TMP_3) in (let 
TMP_5 \def (\forall (t0: T).((eq T t (THead (Bind Abst) v t0)) \to (\forall 
(P: Prop).P))) in (or TMP_4 TMP_5)))))) in (let TMP_18 \def (\lambda (n: 
nat).(\lambda (v: T).(let TMP_10 \def (\lambda (t: T).(let TMP_7 \def (TSort 
n) in (let TMP_8 \def (Bind Abst) in (let TMP_9 \def (THead TMP_8 v t) in (eq 
T TMP_7 TMP_9))))) in (let TMP_11 \def (ex T TMP_10) in (let TMP_12 \def 
(\forall (t: T).((eq T (TSort n) (THead (Bind Abst) v t)) \to (\forall (P: 
Prop).P))) in (let TMP_17 \def (\lambda (t: T).(\lambda (H: (eq T (TSort n) 
(THead (Bind Abst) v t))).(\lambda (P: Prop).(let TMP_13 \def (TSort n) in 
(let TMP_14 \def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow True 
| (TLRef _) \Rightarrow False | (THead _ _ _) \Rightarrow False])) in (let 
TMP_15 \def (Bind Abst) in (let TMP_16 \def (THead TMP_15 v t) in (let H0 
\def (eq_ind T TMP_13 TMP_14 I TMP_16 H) in (False_ind P H0))))))))) in 
(or_intror TMP_11 TMP_12 TMP_17))))))) in (let TMP_30 \def (\lambda (n: 
nat).(\lambda (v: T).(let TMP_22 \def (\lambda (t: T).(let TMP_19 \def (TLRef 
n) in (let TMP_20 \def (Bind Abst) in (let TMP_21 \def (THead TMP_20 v t) in 
(eq T TMP_19 TMP_21))))) in (let TMP_23 \def (ex T TMP_22) in (let TMP_24 
\def (\forall (t: T).((eq T (TLRef n) (THead (Bind Abst) v t)) \to (\forall 
(P: Prop).P))) in (let TMP_29 \def (\lambda (t: T).(\lambda (H: (eq T (TLRef 
n) (THead (Bind Abst) v t))).(\lambda (P: Prop).(let TMP_25 \def (TLRef n) in 
(let TMP_26 \def (\lambda (ee: T).(match ee with [(TSort _) \Rightarrow False 
| (TLRef _) \Rightarrow True | (THead _ _ _) \Rightarrow False])) in (let 
TMP_27 \def (Bind Abst) in (let TMP_28 \def (THead TMP_27 v t) in (let H0 
\def (eq_ind T TMP_25 TMP_26 I TMP_28 H) in (False_ind P H0))))))))) in 
(or_intror TMP_23 TMP_24 TMP_29))))))) in (let TMP_130 \def (\lambda (k: 
K).(\lambda (t: T).(\lambda (_: ((\forall (v: T).(or (ex T (\lambda (t0: 
T).(eq T t (THead (Bind Abst) v t0)))) (\forall (t0: T).((eq T t (THead (Bind 
Abst) v t0)) \to (\forall (P: Prop).P))))))).(\lambda (t0: T).(\lambda (_: 
((\forall (v: T).(or (ex T (\lambda (t1: T).(eq T t0 (THead (Bind Abst) v 
t1)))) (\forall (t1: T).((eq T t0 (THead (Bind Abst) v t1)) \to (\forall (P: 
Prop).P))))))).(\lambda (v: T).(let TMP_31 \def (Bind Abst) in (let H_x \def 
(terms_props__kind_dec k TMP_31) in (let H1 \def H_x in (let TMP_32 \def 
(Bind Abst) in (let TMP_33 \def (eq K k TMP_32) in (let TMP_34 \def ((eq K k 
(Bind Abst)) \to (\forall (P: Prop).P)) in (let TMP_38 \def (\lambda (t1: 
T).(let TMP_35 \def (THead k t t0) in (let TMP_36 \def (Bind Abst) in (let 
TMP_37 \def (THead TMP_36 v t1) in (eq T TMP_35 TMP_37))))) in (let TMP_39 
\def (ex T TMP_38) in (let TMP_40 \def (\forall (t1: T).((eq T (THead k t t0) 
(THead (Bind Abst) v t1)) \to (\forall (P: Prop).P))) in (let TMP_41 \def (or 
TMP_39 TMP_40) in (let TMP_107 \def (\lambda (H2: (eq K k (Bind Abst))).(let 
TMP_42 \def (Bind Abst) in (let TMP_49 \def (\lambda (k0: K).(let TMP_46 \def 
(\lambda (t1: T).(let TMP_43 \def (THead k0 t t0) in (let TMP_44 \def (Bind 
Abst) in (let TMP_45 \def (THead TMP_44 v t1) in (eq T TMP_43 TMP_45))))) in 
(let TMP_47 \def (ex T TMP_46) in (let TMP_48 \def (\forall (t1: T).((eq T 
(THead k0 t t0) (THead (Bind Abst) v t1)) \to (\forall (P: Prop).P))) in (or 
TMP_47 TMP_48))))) in (let H_x0 \def (term_dec t v) in (let H3 \def H_x0 in 
(let TMP_50 \def (eq T t v) in (let TMP_51 \def ((eq T t v) \to (\forall (P: 
Prop).P)) in (let TMP_56 \def (\lambda (t1: T).(let TMP_52 \def (Bind Abst) 
in (let TMP_53 \def (THead TMP_52 t t0) in (let TMP_54 \def (Bind Abst) in 
(let TMP_55 \def (THead TMP_54 v t1) in (eq T TMP_53 TMP_55)))))) in (let 
TMP_57 \def (ex T TMP_56) in (let TMP_58 \def (\forall (t1: T).((eq T (THead 
(Bind Abst) t t0) (THead (Bind Abst) v t1)) \to (\forall (P: Prop).P))) in 
(let TMP_59 \def (or TMP_57 TMP_58) in (let TMP_85 \def (\lambda (H4: (eq T t 
v)).(let TMP_67 \def (\lambda (t1: T).(let TMP_64 \def (\lambda (t2: T).(let 
TMP_60 \def (Bind Abst) in (let TMP_61 \def (THead TMP_60 t t0) in (let 
TMP_62 \def (Bind Abst) in (let TMP_63 \def (THead TMP_62 t1 t2) in (eq T 
TMP_61 TMP_63)))))) in (let TMP_65 \def (ex T TMP_64) in (let TMP_66 \def 
(\forall (t2: T).((eq T (THead (Bind Abst) t t0) (THead (Bind Abst) t1 t2)) 
\to (\forall (P: Prop).P))) in (or TMP_65 TMP_66))))) in (let TMP_72 \def 
(\lambda (t1: T).(let TMP_68 \def (Bind Abst) in (let TMP_69 \def (THead 
TMP_68 t t0) in (let TMP_70 \def (Bind Abst) in (let TMP_71 \def (THead 
TMP_70 t t1) in (eq T TMP_69 TMP_71)))))) in (let TMP_73 \def (ex T TMP_72) 
in (let TMP_74 \def (\forall (t1: T).((eq T (THead (Bind Abst) t t0) (THead 
(Bind Abst) t t1)) \to (\forall (P: Prop).P))) in (let TMP_79 \def (\lambda 
(t1: T).(let TMP_75 \def (Bind Abst) in (let TMP_76 \def (THead TMP_75 t t0) 
in (let TMP_77 \def (Bind Abst) in (let TMP_78 \def (THead TMP_77 t t1) in 
(eq T TMP_76 TMP_78)))))) in (let TMP_80 \def (Bind Abst) in (let TMP_81 \def 
(THead TMP_80 t t0) in (let TMP_82 \def (refl_equal T TMP_81) in (let TMP_83 
\def (ex_intro T TMP_79 t0 TMP_82) in (let TMP_84 \def (or_introl TMP_73 
TMP_74 TMP_83) in (eq_ind T t TMP_67 TMP_84 v H4)))))))))))) in (let TMP_105 
\def (\lambda (H4: (((eq T t v) \to (\forall (P: Prop).P)))).(let TMP_90 \def 
(\lambda (t1: T).(let TMP_86 \def (Bind Abst) in (let TMP_87 \def (THead 
TMP_86 t t0) in (let TMP_88 \def (Bind Abst) in (let TMP_89 \def (THead 
TMP_88 v t1) in (eq T TMP_87 TMP_89)))))) in (let TMP_91 \def (ex T TMP_90) 
in (let TMP_92 \def (\forall (t1: T).((eq T (THead (Bind Abst) t t0) (THead 
(Bind Abst) v t1)) \to (\forall (P: Prop).P))) in (let TMP_104 \def (\lambda 
(t1: T).(\lambda (H5: (eq T (THead (Bind Abst) t t0) (THead (Bind Abst) v 
t1))).(\lambda (P: Prop).(let TMP_93 \def (\lambda (e: T).(match e with 
[(TSort _) \Rightarrow t | (TLRef _) \Rightarrow t | (THead _ t2 _) 
\Rightarrow t2])) in (let TMP_94 \def (Bind Abst) in (let TMP_95 \def (THead 
TMP_94 t t0) in (let TMP_96 \def (Bind Abst) in (let TMP_97 \def (THead 
TMP_96 v t1) in (let H6 \def (f_equal T T TMP_93 TMP_95 TMP_97 H5) in (let 
TMP_98 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow t0 | (TLRef 
_) \Rightarrow t0 | (THead _ _ t2) \Rightarrow t2])) in (let TMP_99 \def 
(Bind Abst) in (let TMP_100 \def (THead TMP_99 t t0) in (let TMP_101 \def 
(Bind Abst) in (let TMP_102 \def (THead TMP_101 v t1) in (let H7 \def 
(f_equal T T TMP_98 TMP_100 TMP_102 H5) in (let TMP_103 \def (\lambda (H8: 
(eq T t v)).(H4 H8 P)) in (TMP_103 H6))))))))))))))))) in (or_intror TMP_91 
TMP_92 TMP_104)))))) in (let TMP_106 \def (or_ind TMP_50 TMP_51 TMP_59 TMP_85 
TMP_105 H3) in (eq_ind_r K TMP_42 TMP_49 TMP_106 k H2))))))))))))))) in (let 
TMP_129 \def (\lambda (H2: (((eq K k (Bind Abst)) \to (\forall (P: 
Prop).P)))).(let TMP_111 \def (\lambda (t1: T).(let TMP_108 \def (THead k t 
t0) in (let TMP_109 \def (Bind Abst) in (let TMP_110 \def (THead TMP_109 v 
t1) in (eq T TMP_108 TMP_110))))) in (let TMP_112 \def (ex T TMP_111) in (let 
TMP_113 \def (\forall (t1: T).((eq T (THead k t t0) (THead (Bind Abst) v t1)) 
\to (\forall (P: Prop).P))) in (let TMP_128 \def (\lambda (t1: T).(\lambda 
(H3: (eq T (THead k t t0) (THead (Bind Abst) v t1))).(\lambda (P: Prop).(let 
TMP_114 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow k | (TLRef 
_) \Rightarrow k | (THead k0 _ _) \Rightarrow k0])) in (let TMP_115 \def 
(THead k t t0) in (let TMP_116 \def (Bind Abst) in (let TMP_117 \def (THead 
TMP_116 v t1) in (let H4 \def (f_equal T K TMP_114 TMP_115 TMP_117 H3) in 
(let TMP_118 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow t | 
(TLRef _) \Rightarrow t | (THead _ t2 _) \Rightarrow t2])) in (let TMP_119 
\def (THead k t t0) in (let TMP_120 \def (Bind Abst) in (let TMP_121 \def 
(THead TMP_120 v t1) in (let H5 \def (f_equal T T TMP_118 TMP_119 TMP_121 H3) 
in (let TMP_122 \def (\lambda (e: T).(match e with [(TSort _) \Rightarrow t0 
| (TLRef _) \Rightarrow t0 | (THead _ _ t2) \Rightarrow t2])) in (let TMP_123 
\def (THead k t t0) in (let TMP_124 \def (Bind Abst) in (let TMP_125 \def 
(THead TMP_124 v t1) in (let H6 \def (f_equal T T TMP_122 TMP_123 TMP_125 H3) 
in (let TMP_126 \def (\lambda (_: (eq T t v)).(\lambda (H8: (eq K k (Bind 
Abst))).(H2 H8 P))) in (let TMP_127 \def (TMP_126 H5) in (TMP_127 
H4))))))))))))))))))))) in (or_intror TMP_112 TMP_113 TMP_128)))))) in 
(or_ind TMP_33 TMP_34 TMP_41 TMP_107 TMP_129 H1))))))))))))))))))) in (T_ind 
TMP_6 TMP_18 TMP_30 TMP_130 u))))).

