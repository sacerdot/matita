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

include "basic_1/pr1/fwd.ma".

include "basic_1/pr0/subst1.ma".

include "basic_1/subst1/props.ma".

include "basic_1/T/props.ma".

theorem pr1_pr0:
 \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (pr1 t1 t2)))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr0 t1 t2)).(let TMP_1 \def 
(pr1_refl t2) in (pr1_sing t2 t1 H t2 TMP_1)))).

theorem pr1_t:
 \forall (t2: T).(\forall (t1: T).((pr1 t1 t2) \to (\forall (t3: T).((pr1 t2 
t3) \to (pr1 t1 t3)))))
\def
 \lambda (t2: T).(\lambda (t1: T).(\lambda (H: (pr1 t1 t2)).(let TMP_1 \def 
(\lambda (t: T).(\lambda (t0: T).(\forall (t3: T).((pr1 t0 t3) \to (pr1 t 
t3))))) in (let TMP_2 \def (\lambda (t: T).(\lambda (t3: T).(\lambda (H0: 
(pr1 t t3)).H0))) in (let TMP_4 \def (\lambda (t0: T).(\lambda (t3: 
T).(\lambda (H0: (pr0 t3 t0)).(\lambda (t4: T).(\lambda (_: (pr1 t0 
t4)).(\lambda (H2: ((\forall (t5: T).((pr1 t4 t5) \to (pr1 t0 
t5))))).(\lambda (t5: T).(\lambda (H3: (pr1 t4 t5)).(let TMP_3 \def (H2 t5 
H3) in (pr1_sing t0 t3 H0 t5 TMP_3)))))))))) in (pr1_ind TMP_1 TMP_2 TMP_4 t1 
t2 H)))))).

theorem pr1_head_1:
 \forall (u1: T).(\forall (u2: T).((pr1 u1 u2) \to (\forall (t: T).(\forall 
(k: K).(pr1 (THead k u1 t) (THead k u2 t))))))
\def
 \lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr1 u1 u2)).(\lambda (t: 
T).(\lambda (k: K).(let TMP_3 \def (\lambda (t0: T).(\lambda (t1: T).(let 
TMP_1 \def (THead k t0 t) in (let TMP_2 \def (THead k t1 t) in (pr1 TMP_1 
TMP_2))))) in (let TMP_5 \def (\lambda (t0: T).(let TMP_4 \def (THead k t0 t) 
in (pr1_refl TMP_4))) in (let TMP_11 \def (\lambda (t2: T).(\lambda (t1: 
T).(\lambda (H0: (pr0 t1 t2)).(\lambda (t3: T).(\lambda (_: (pr1 t2 
t3)).(\lambda (H2: (pr1 (THead k t2 t) (THead k t3 t))).(let TMP_6 \def 
(THead k t2 t) in (let TMP_7 \def (THead k t1 t) in (let TMP_8 \def (pr0_refl 
t) in (let TMP_9 \def (pr0_comp t1 t2 H0 t t TMP_8 k) in (let TMP_10 \def 
(THead k t3 t) in (pr1_sing TMP_6 TMP_7 TMP_9 TMP_10 H2)))))))))))) in 
(pr1_ind TMP_3 TMP_5 TMP_11 u1 u2 H)))))))).

theorem pr1_head_2:
 \forall (t1: T).(\forall (t2: T).((pr1 t1 t2) \to (\forall (u: T).(\forall 
(k: K).(pr1 (THead k u t1) (THead k u t2))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr1 t1 t2)).(\lambda (u: 
T).(\lambda (k: K).(let TMP_3 \def (\lambda (t: T).(\lambda (t0: T).(let 
TMP_1 \def (THead k u t) in (let TMP_2 \def (THead k u t0) in (pr1 TMP_1 
TMP_2))))) in (let TMP_5 \def (\lambda (t: T).(let TMP_4 \def (THead k u t) 
in (pr1_refl TMP_4))) in (let TMP_11 \def (\lambda (t0: T).(\lambda (t3: 
T).(\lambda (H0: (pr0 t3 t0)).(\lambda (t4: T).(\lambda (_: (pr1 t0 
t4)).(\lambda (H2: (pr1 (THead k u t0) (THead k u t4))).(let TMP_6 \def 
(THead k u t0) in (let TMP_7 \def (THead k u t3) in (let TMP_8 \def (pr0_refl 
u) in (let TMP_9 \def (pr0_comp u u TMP_8 t3 t0 H0 k) in (let TMP_10 \def 
(THead k u t4) in (pr1_sing TMP_6 TMP_7 TMP_9 TMP_10 H2)))))))))))) in 
(pr1_ind TMP_3 TMP_5 TMP_11 t1 t2 H)))))))).

theorem pr1_comp:
 \forall (v: T).(\forall (w: T).((pr1 v w) \to (\forall (t: T).(\forall (u: 
T).((pr1 t u) \to (\forall (k: K).(pr1 (THead k v t) (THead k w u))))))))
\def
 \lambda (v: T).(\lambda (w: T).(\lambda (H: (pr1 v w)).(let TMP_3 \def 
(\lambda (t: T).(\lambda (t0: T).(\forall (t1: T).(\forall (u: T).((pr1 t1 u) 
\to (\forall (k: K).(let TMP_1 \def (THead k t t1) in (let TMP_2 \def (THead 
k t0 u) in (pr1 TMP_1 TMP_2))))))))) in (let TMP_4 \def (\lambda (t: 
T).(\lambda (t0: T).(\lambda (u: T).(\lambda (H0: (pr1 t0 u)).(\lambda (k: 
K).(pr1_head_2 t0 u H0 t k)))))) in (let TMP_16 \def (\lambda (t2: 
T).(\lambda (t1: T).(\lambda (H0: (pr0 t1 t2)).(\lambda (t3: T).(\lambda (H1: 
(pr1 t2 t3)).(\lambda (_: ((\forall (t: T).(\forall (u: T).((pr1 t u) \to 
(\forall (k: K).(pr1 (THead k t2 t) (THead k t3 u)))))))).(\lambda (t: 
T).(\lambda (u: T).(\lambda (H3: (pr1 t u)).(\lambda (k: K).(let TMP_7 \def 
(\lambda (t0: T).(\lambda (t4: T).(let TMP_5 \def (THead k t1 t0) in (let 
TMP_6 \def (THead k t3 t4) in (pr1 TMP_5 TMP_6))))) in (let TMP_9 \def 
(\lambda (t0: T).(let TMP_8 \def (pr1_sing t2 t1 H0 t3 H1) in (pr1_head_1 t1 
t3 TMP_8 t0 k))) in (let TMP_15 \def (\lambda (t0: T).(\lambda (t4: 
T).(\lambda (H4: (pr0 t4 t0)).(\lambda (t5: T).(\lambda (_: (pr1 t0 
t5)).(\lambda (H6: (pr1 (THead k t1 t0) (THead k t3 t5))).(let TMP_10 \def 
(THead k t1 t0) in (let TMP_11 \def (THead k t1 t4) in (let TMP_12 \def 
(pr0_refl t1) in (let TMP_13 \def (pr0_comp t1 t1 TMP_12 t4 t0 H4 k) in (let 
TMP_14 \def (THead k t3 t5) in (pr1_sing TMP_10 TMP_11 TMP_13 TMP_14 
H6)))))))))))) in (pr1_ind TMP_7 TMP_9 TMP_15 t u H3)))))))))))))) in 
(pr1_ind TMP_3 TMP_4 TMP_16 v w H)))))).

theorem pr1_eta:
 \forall (w: T).(\forall (u: T).(let t \def (THead (Bind Abst) w u) in 
(\forall (v: T).((pr1 v w) \to (pr1 (THead (Bind Abst) v (THead (Flat Appl) 
(TLRef O) (lift (S O) O t))) t)))))
\def
 \lambda (w: T).(\lambda (u: T).(let TMP_1 \def (Bind Abst) in (let t \def 
(THead TMP_1 w u) in (\lambda (v: T).(\lambda (H: (pr1 v w)).(let TMP_2 \def 
(Bind Abst) in (let TMP_3 \def (S O) in (let TMP_4 \def (lift TMP_3 O w) in 
(let TMP_5 \def (S O) in (let TMP_6 \def (S O) in (let TMP_7 \def (lift TMP_5 
TMP_6 u) in (let TMP_8 \def (THead TMP_2 TMP_4 TMP_7) in (let TMP_16 \def 
(\lambda (t0: T).(let TMP_9 \def (Bind Abst) in (let TMP_10 \def (Flat Appl) 
in (let TMP_11 \def (TLRef O) in (let TMP_12 \def (THead TMP_10 TMP_11 t0) in 
(let TMP_13 \def (THead TMP_9 v TMP_12) in (let TMP_14 \def (Bind Abst) in 
(let TMP_15 \def (THead TMP_14 w u) in (pr1 TMP_13 TMP_15))))))))) in (let 
TMP_17 \def (Flat Appl) in (let TMP_18 \def (TLRef O) in (let TMP_19 \def 
(Bind Abst) in (let TMP_20 \def (S O) in (let TMP_21 \def (lift TMP_20 O w) 
in (let TMP_22 \def (S O) in (let TMP_23 \def (S O) in (let TMP_24 \def (lift 
TMP_22 TMP_23 u) in (let TMP_25 \def (THead TMP_19 TMP_21 TMP_24) in (let 
TMP_26 \def (THead TMP_17 TMP_18 TMP_25) in (let TMP_27 \def (Bind Abbr) in 
(let TMP_28 \def (TLRef O) in (let TMP_29 \def (S O) in (let TMP_30 \def (S 
O) in (let TMP_31 \def (lift TMP_29 TMP_30 u) in (let TMP_32 \def (THead 
TMP_27 TMP_28 TMP_31) in (let TMP_33 \def (Flat Appl) in (let TMP_34 \def 
(TLRef O) in (let TMP_35 \def (Bind Abst) in (let TMP_36 \def (S O) in (let 
TMP_37 \def (lift TMP_36 O w) in (let TMP_38 \def (S O) in (let TMP_39 \def 
(S O) in (let TMP_40 \def (lift TMP_38 TMP_39 u) in (let TMP_41 \def (THead 
TMP_35 TMP_37 TMP_40) in (let TMP_42 \def (THead TMP_33 TMP_34 TMP_41) in 
(let TMP_43 \def (S O) in (let TMP_44 \def (lift TMP_43 O w) in (let TMP_45 
\def (TLRef O) in (let TMP_46 \def (TLRef O) in (let TMP_47 \def (TLRef O) in 
(let TMP_48 \def (pr0_refl TMP_47) in (let TMP_49 \def (S O) in (let TMP_50 
\def (S O) in (let TMP_51 \def (lift TMP_49 TMP_50 u) in (let TMP_52 \def (S 
O) in (let TMP_53 \def (S O) in (let TMP_54 \def (lift TMP_52 TMP_53 u) in 
(let TMP_55 \def (S O) in (let TMP_56 \def (S O) in (let TMP_57 \def (lift 
TMP_55 TMP_56 u) in (let TMP_58 \def (pr0_refl TMP_57) in (let TMP_59 \def 
(pr0_beta TMP_44 TMP_45 TMP_46 TMP_48 TMP_51 TMP_54 TMP_58) in (let TMP_60 
\def (Bind Abbr) in (let TMP_61 \def (TLRef O) in (let TMP_62 \def (S O) in 
(let TMP_63 \def (lift TMP_62 O u) in (let TMP_64 \def (THead TMP_60 TMP_61 
TMP_63) in (let TMP_65 \def (Bind Abbr) in (let TMP_66 \def (TLRef O) in (let 
TMP_67 \def (S O) in (let TMP_68 \def (S O) in (let TMP_69 \def (lift TMP_67 
TMP_68 u) in (let TMP_70 \def (THead TMP_65 TMP_66 TMP_69) in (let TMP_71 
\def (TLRef O) in (let TMP_72 \def (TLRef O) in (let TMP_73 \def (TLRef O) in 
(let TMP_74 \def (pr0_refl TMP_73) in (let TMP_75 \def (S O) in (let TMP_76 
\def (S O) in (let TMP_77 \def (lift TMP_75 TMP_76 u) in (let TMP_78 \def (S 
O) in (let TMP_79 \def (S O) in (let TMP_80 \def (lift TMP_78 TMP_79 u) in 
(let TMP_81 \def (S O) in (let TMP_82 \def (S O) in (let TMP_83 \def (lift 
TMP_81 TMP_82 u) in (let TMP_84 \def (pr0_refl TMP_83) in (let TMP_85 \def (S 
O) in (let TMP_86 \def (lift TMP_85 O u) in (let TMP_87 \def (le_O_n O) in 
(let TMP_88 \def (subst1_lift_S u O O TMP_87) in (let TMP_89 \def (pr0_delta1 
TMP_71 TMP_72 TMP_74 TMP_77 TMP_80 TMP_84 TMP_86 TMP_88) in (let TMP_90 \def 
(Bind Abbr) in (let TMP_91 \def (TLRef O) in (let TMP_92 \def (S O) in (let 
TMP_93 \def (lift TMP_92 O u) in (let TMP_94 \def (THead TMP_90 TMP_91 
TMP_93) in (let TMP_95 \def (pr0_refl u) in (let TMP_96 \def (TLRef O) in 
(let TMP_97 \def (pr0_zeta Abbr not_abbr_abst u u TMP_95 TMP_96) in (let 
TMP_98 \def (pr1_pr0 TMP_94 u TMP_97) in (let TMP_99 \def (pr1_sing TMP_64 
TMP_70 TMP_89 u TMP_98) in (let TMP_100 \def (pr1_sing TMP_32 TMP_42 TMP_59 u 
TMP_99) in (let TMP_101 \def (Bind Abst) in (let TMP_102 \def (pr1_comp v w H 
TMP_26 u TMP_100 TMP_101) in (let TMP_103 \def (S O) in (let TMP_104 \def 
(Bind Abst) in (let TMP_105 \def (THead TMP_104 w u) in (let TMP_106 \def 
(lift TMP_103 O TMP_105) in (let TMP_107 \def (S O) in (let TMP_108 \def 
(lift_bind Abst w u TMP_107 O) in (eq_ind_r T TMP_8 TMP_16 TMP_102 TMP_106 
TMP_108)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))))))))))))).

