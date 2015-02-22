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

include "basic_1/asucc/defs.ma".

include "basic_1/A/fwd.ma".

theorem asucc_gen_sort:
 \forall (g: G).(\forall (h: nat).(\forall (n: nat).(\forall (a: A).((eq A 
(ASort h n) (asucc g a)) \to (ex_2 nat nat (\lambda (h0: nat).(\lambda (n0: 
nat).(eq A a (ASort h0 n0)))))))))
\def
 \lambda (g: G).(\lambda (h: nat).(\lambda (n: nat).(\lambda (a: A).(let 
TMP_3 \def (\lambda (a0: A).((eq A (ASort h n) (asucc g a0)) \to (let TMP_2 
\def (\lambda (h0: nat).(\lambda (n0: nat).(let TMP_1 \def (ASort h0 n0) in 
(eq A a0 TMP_1)))) in (ex_2 nat nat TMP_2)))) in (let TMP_13 \def (\lambda 
(n0: nat).(\lambda (n1: nat).(\lambda (H: (eq A (ASort h n) (asucc g (ASort 
n0 n1)))).(let TMP_4 \def (\lambda (e: A).e) in (let TMP_5 \def (ASort h n) 
in (let TMP_7 \def (match n0 with [O \Rightarrow (let TMP_6 \def (next g n1) 
in (ASort O TMP_6)) | (S h0) \Rightarrow (ASort h0 n1)]) in (let H0 \def 
(f_equal A A TMP_4 TMP_5 TMP_7 H) in (let TMP_10 \def (\lambda (h0: 
nat).(\lambda (n2: nat).(let TMP_8 \def (ASort n0 n1) in (let TMP_9 \def 
(ASort h0 n2) in (eq A TMP_8 TMP_9))))) in (let TMP_11 \def (ASort n0 n1) in 
(let TMP_12 \def (refl_equal A TMP_11) in (ex_2_intro nat nat TMP_10 n0 n1 
TMP_12))))))))))) in (let TMP_22 \def (\lambda (a0: A).(\lambda (_: (((eq A 
(ASort h n) (asucc g a0)) \to (ex_2 nat nat (\lambda (h0: nat).(\lambda (n0: 
nat).(eq A a0 (ASort h0 n0)))))))).(\lambda (a1: A).(\lambda (_: (((eq A 
(ASort h n) (asucc g a1)) \to (ex_2 nat nat (\lambda (h0: nat).(\lambda (n0: 
nat).(eq A a1 (ASort h0 n0)))))))).(\lambda (H1: (eq A (ASort h n) (asucc g 
(AHead a0 a1)))).(let TMP_14 \def (ASort h n) in (let TMP_15 \def (\lambda 
(ee: A).(match ee with [(ASort _ _) \Rightarrow True | (AHead _ _) 
\Rightarrow False])) in (let TMP_16 \def (AHead a0 a1) in (let TMP_17 \def 
(asucc g TMP_16) in (let H2 \def (eq_ind A TMP_14 TMP_15 I TMP_17 H1) in (let 
TMP_20 \def (\lambda (h0: nat).(\lambda (n0: nat).(let TMP_18 \def (AHead a0 
a1) in (let TMP_19 \def (ASort h0 n0) in (eq A TMP_18 TMP_19))))) in (let 
TMP_21 \def (ex_2 nat nat TMP_20) in (False_ind TMP_21 H2))))))))))))) in 
(A_ind TMP_3 TMP_13 TMP_22 a))))))).

theorem asucc_gen_head:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (a: A).((eq A 
(AHead a1 a2) (asucc g a)) \to (ex2 A (\lambda (a0: A).(eq A a (AHead a1 
a0))) (\lambda (a0: A).(eq A a2 (asucc g a0))))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (a: A).(let TMP_5 
\def (\lambda (a0: A).((eq A (AHead a1 a2) (asucc g a0)) \to (let TMP_2 \def 
(\lambda (a3: A).(let TMP_1 \def (AHead a1 a3) in (eq A a0 TMP_1))) in (let 
TMP_4 \def (\lambda (a3: A).(let TMP_3 \def (asucc g a3) in (eq A a2 TMP_3))) 
in (ex2 A TMP_2 TMP_4))))) in (let TMP_34 \def (\lambda (n: nat).(\lambda 
(n0: nat).(\lambda (H: (eq A (AHead a1 a2) (asucc g (ASort n n0)))).(let 
TMP_11 \def (\lambda (n1: nat).((eq A (AHead a1 a2) (asucc g (ASort n1 n0))) 
\to (let TMP_8 \def (\lambda (a0: A).(let TMP_6 \def (ASort n1 n0) in (let 
TMP_7 \def (AHead a1 a0) in (eq A TMP_6 TMP_7)))) in (let TMP_10 \def 
(\lambda (a0: A).(let TMP_9 \def (asucc g a0) in (eq A a2 TMP_9))) in (ex2 A 
TMP_8 TMP_10))))) in (let TMP_22 \def (\lambda (H0: (eq A (AHead a1 a2) 
(asucc g (ASort O n0)))).(let TMP_12 \def (AHead a1 a2) in (let TMP_13 \def 
(\lambda (ee: A).(match ee with [(ASort _ _) \Rightarrow False | (AHead _ _) 
\Rightarrow True])) in (let TMP_14 \def (next g n0) in (let TMP_15 \def 
(ASort O TMP_14) in (let H1 \def (eq_ind A TMP_12 TMP_13 I TMP_15 H0) in (let 
TMP_18 \def (\lambda (a0: A).(let TMP_16 \def (ASort O n0) in (let TMP_17 
\def (AHead a1 a0) in (eq A TMP_16 TMP_17)))) in (let TMP_20 \def (\lambda 
(a0: A).(let TMP_19 \def (asucc g a0) in (eq A a2 TMP_19))) in (let TMP_21 
\def (ex2 A TMP_18 TMP_20) in (False_ind TMP_21 H1)))))))))) in (let TMP_33 
\def (\lambda (n1: nat).(\lambda (_: (((eq A (AHead a1 a2) (asucc g (ASort n1 
n0))) \to (ex2 A (\lambda (a0: A).(eq A (ASort n1 n0) (AHead a1 a0))) 
(\lambda (a0: A).(eq A a2 (asucc g a0))))))).(\lambda (H0: (eq A (AHead a1 
a2) (asucc g (ASort (S n1) n0)))).(let TMP_23 \def (AHead a1 a2) in (let 
TMP_24 \def (\lambda (ee: A).(match ee with [(ASort _ _) \Rightarrow False | 
(AHead _ _) \Rightarrow True])) in (let TMP_25 \def (ASort n1 n0) in (let H1 
\def (eq_ind A TMP_23 TMP_24 I TMP_25 H0) in (let TMP_29 \def (\lambda (a0: 
A).(let TMP_26 \def (S n1) in (let TMP_27 \def (ASort TMP_26 n0) in (let 
TMP_28 \def (AHead a1 a0) in (eq A TMP_27 TMP_28))))) in (let TMP_31 \def 
(\lambda (a0: A).(let TMP_30 \def (asucc g a0) in (eq A a2 TMP_30))) in (let 
TMP_32 \def (ex2 A TMP_29 TMP_31) in (False_ind TMP_32 H1))))))))))) in 
(nat_ind TMP_11 TMP_22 TMP_33 n H))))))) in (let TMP_86 \def (\lambda (a0: 
A).(\lambda (H: (((eq A (AHead a1 a2) (asucc g a0)) \to (ex2 A (\lambda (a3: 
A).(eq A a0 (AHead a1 a3))) (\lambda (a3: A).(eq A a2 (asucc g 
a3))))))).(\lambda (a3: A).(\lambda (H0: (((eq A (AHead a1 a2) (asucc g a3)) 
\to (ex2 A (\lambda (a4: A).(eq A a3 (AHead a1 a4))) (\lambda (a4: A).(eq A 
a2 (asucc g a4))))))).(\lambda (H1: (eq A (AHead a1 a2) (asucc g (AHead a0 
a3)))).(let TMP_35 \def (\lambda (e: A).(match e with [(ASort _ _) 
\Rightarrow a1 | (AHead a4 _) \Rightarrow a4])) in (let TMP_36 \def (AHead a1 
a2) in (let TMP_37 \def (asucc g a3) in (let TMP_38 \def (AHead a0 TMP_37) in 
(let H2 \def (f_equal A A TMP_35 TMP_36 TMP_38 H1) in (let TMP_39 \def 
(\lambda (e: A).(match e with [(ASort _ _) \Rightarrow a2 | (AHead _ a4) 
\Rightarrow a4])) in (let TMP_40 \def (AHead a1 a2) in (let TMP_41 \def 
(asucc g a3) in (let TMP_42 \def (AHead a0 TMP_41) in (let H3 \def (f_equal A 
A TMP_39 TMP_40 TMP_42 H1) in (let TMP_85 \def (\lambda (H4: (eq A a1 
a0)).(let TMP_47 \def (\lambda (a4: A).((eq A (AHead a1 a2) (asucc g a4)) \to 
(let TMP_44 \def (\lambda (a5: A).(let TMP_43 \def (AHead a1 a5) in (eq A a4 
TMP_43))) in (let TMP_46 \def (\lambda (a5: A).(let TMP_45 \def (asucc g a5) 
in (eq A a2 TMP_45))) in (ex2 A TMP_44 TMP_46))))) in (let H5 \def (eq_ind_r 
A a0 TMP_47 H a1 H4) in (let TMP_53 \def (\lambda (a4: A).(let TMP_50 \def 
(\lambda (a5: A).(let TMP_48 \def (AHead a4 a3) in (let TMP_49 \def (AHead a1 
a5) in (eq A TMP_48 TMP_49)))) in (let TMP_52 \def (\lambda (a5: A).(let 
TMP_51 \def (asucc g a5) in (eq A a2 TMP_51))) in (ex2 A TMP_50 TMP_52)))) in 
(let TMP_58 \def (\lambda (a4: A).((eq A (AHead a1 a4) (asucc g a3)) \to (let 
TMP_55 \def (\lambda (a5: A).(let TMP_54 \def (AHead a1 a5) in (eq A a3 
TMP_54))) in (let TMP_57 \def (\lambda (a5: A).(let TMP_56 \def (asucc g a5) 
in (eq A a4 TMP_56))) in (ex2 A TMP_55 TMP_57))))) in (let TMP_59 \def (asucc 
g a3) in (let H6 \def (eq_ind A a2 TMP_58 H0 TMP_59 H3) in (let TMP_64 \def 
(\lambda (a4: A).((eq A (AHead a1 a4) (asucc g a1)) \to (let TMP_61 \def 
(\lambda (a5: A).(let TMP_60 \def (AHead a1 a5) in (eq A a1 TMP_60))) in (let 
TMP_63 \def (\lambda (a5: A).(let TMP_62 \def (asucc g a5) in (eq A a4 
TMP_62))) in (ex2 A TMP_61 TMP_63))))) in (let TMP_65 \def (asucc g a3) in 
(let H7 \def (eq_ind A a2 TMP_64 H5 TMP_65 H3) in (let TMP_66 \def (asucc g 
a3) in (let TMP_72 \def (\lambda (a4: A).(let TMP_69 \def (\lambda (a5: 
A).(let TMP_67 \def (AHead a1 a3) in (let TMP_68 \def (AHead a1 a5) in (eq A 
TMP_67 TMP_68)))) in (let TMP_71 \def (\lambda (a5: A).(let TMP_70 \def 
(asucc g a5) in (eq A a4 TMP_70))) in (ex2 A TMP_69 TMP_71)))) in (let TMP_75 
\def (\lambda (a4: A).(let TMP_73 \def (AHead a1 a3) in (let TMP_74 \def 
(AHead a1 a4) in (eq A TMP_73 TMP_74)))) in (let TMP_78 \def (\lambda (a4: 
A).(let TMP_76 \def (asucc g a3) in (let TMP_77 \def (asucc g a4) in (eq A 
TMP_76 TMP_77)))) in (let TMP_79 \def (AHead a1 a3) in (let TMP_80 \def 
(refl_equal A TMP_79) in (let TMP_81 \def (asucc g a3) in (let TMP_82 \def 
(refl_equal A TMP_81) in (let TMP_83 \def (ex_intro2 A TMP_75 TMP_78 a3 
TMP_80 TMP_82) in (let TMP_84 \def (eq_ind_r A TMP_66 TMP_72 TMP_83 a2 H3) in 
(eq_ind A a1 TMP_53 TMP_84 a0 H4))))))))))))))))))))) in (TMP_85 
H2))))))))))))))))) in (A_ind TMP_5 TMP_34 TMP_86 a))))))).

