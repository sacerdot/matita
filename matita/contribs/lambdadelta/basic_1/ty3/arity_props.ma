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

include "basic_1/ty3/arity.ma".

include "basic_1/sc3/arity.ma".

theorem ty3_predicative:
 \forall (g: G).(\forall (c: C).(\forall (v: T).(\forall (t: T).(\forall (u: 
T).((ty3 g c (THead (Bind Abst) v t) u) \to ((pc3 c u v) \to (\forall (P: 
Prop).P)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (v: T).(\lambda (t: T).(\lambda (u: 
T).(\lambda (H: (ty3 g c (THead (Bind Abst) v t) u)).(\lambda (H0: (pc3 c u 
v)).(\lambda (P: Prop).(let H1 \def H in (let TMP_3 \def (\lambda (t2: 
T).(\lambda (_: T).(let TMP_1 \def (Bind Abst) in (let TMP_2 \def (THead 
TMP_1 v t2) in (pc3 c TMP_2 u))))) in (let TMP_4 \def (\lambda (_: 
T).(\lambda (t0: T).(ty3 g c v t0))) in (let TMP_7 \def (\lambda (t2: 
T).(\lambda (_: T).(let TMP_5 \def (Bind Abst) in (let TMP_6 \def (CHead c 
TMP_5 v) in (ty3 g TMP_6 t t2))))) in (let TMP_34 \def (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (_: (pc3 c (THead (Bind Abst) v x0) u)).(\lambda 
(H3: (ty3 g c v x1)).(\lambda (_: (ty3 g (CHead c (Bind Abst) v) t x0)).(let 
TMP_8 \def (Bind Abst) in (let TMP_9 \def (THead TMP_8 v t) in (let H_y \def 
(ty3_conv g c v x1 H3 TMP_9 u H H0) in (let TMP_10 \def (Bind Abst) in (let 
TMP_11 \def (THead TMP_10 v t) in (let H_x \def (ty3_arity g c TMP_11 v H_y) 
in (let H5 \def H_x in (let TMP_14 \def (\lambda (a1: A).(let TMP_12 \def 
(Bind Abst) in (let TMP_13 \def (THead TMP_12 v t) in (arity g c TMP_13 
a1)))) in (let TMP_16 \def (\lambda (a1: A).(let TMP_15 \def (asucc g a1) in 
(arity g c v TMP_15))) in (let TMP_33 \def (\lambda (x: A).(\lambda (H6: 
(arity g c (THead (Bind Abst) v t) x)).(\lambda (H7: (arity g c v (asucc g 
x))).(let H8 \def (arity_gen_abst g c v t x H6) in (let TMP_18 \def (\lambda 
(a1: A).(\lambda (a2: A).(let TMP_17 \def (AHead a1 a2) in (eq A x TMP_17)))) 
in (let TMP_20 \def (\lambda (a1: A).(\lambda (_: A).(let TMP_19 \def (asucc 
g a1) in (arity g c v TMP_19)))) in (let TMP_23 \def (\lambda (_: A).(\lambda 
(a2: A).(let TMP_21 \def (Bind Abst) in (let TMP_22 \def (CHead c TMP_21 v) 
in (arity g TMP_22 t a2))))) in (let TMP_32 \def (\lambda (x2: A).(\lambda 
(x3: A).(\lambda (H9: (eq A x (AHead x2 x3))).(\lambda (H10: (arity g c v 
(asucc g x2))).(\lambda (_: (arity g (CHead c (Bind Abst) v) t x3)).(let 
TMP_25 \def (\lambda (a: A).(let TMP_24 \def (asucc g a) in (arity g c v 
TMP_24))) in (let TMP_26 \def (AHead x2 x3) in (let H12 \def (eq_ind A x 
TMP_25 H7 TMP_26 H9) in (let TMP_27 \def (asucc g x3) in (let TMP_28 \def 
(AHead x2 x3) in (let TMP_29 \def (asucc g TMP_28) in (let TMP_30 \def (asucc 
g x2) in (let TMP_31 \def (arity_mono g c v TMP_29 H12 TMP_30 H10) in 
(leq_ahead_asucc_false g x2 TMP_27 TMP_31 P)))))))))))))) in (ex3_2_ind A A 
TMP_18 TMP_20 TMP_23 P TMP_32 H8))))))))) in (ex2_ind A TMP_14 TMP_16 P 
TMP_33 H5)))))))))))))))) in (let TMP_35 \def (ty3_gen_bind g Abst c v t u 
H1) in (ex3_2_ind T T TMP_3 TMP_4 TMP_7 P TMP_34 TMP_35)))))))))))))).

theorem ty3_repellent:
 \forall (g: G).(\forall (c: C).(\forall (w: T).(\forall (t: T).(\forall (u1: 
T).((ty3 g c (THead (Bind Abst) w t) u1) \to (\forall (u2: T).((ty3 g (CHead 
c (Bind Abst) w) t (lift (S O) O u2)) \to ((pc3 c u1 u2) \to (\forall (P: 
Prop).P)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (w: T).(\lambda (t: T).(\lambda (u1: 
T).(\lambda (H: (ty3 g c (THead (Bind Abst) w t) u1)).(\lambda (u2: 
T).(\lambda (H0: (ty3 g (CHead c (Bind Abst) w) t (lift (S O) O 
u2))).(\lambda (H1: (pc3 c u1 u2)).(\lambda (P: Prop).(let TMP_5 \def 
(\lambda (t0: T).(let TMP_1 \def (Bind Abst) in (let TMP_2 \def (CHead c 
TMP_1 w) in (let TMP_3 \def (S O) in (let TMP_4 \def (lift TMP_3 O u2) in 
(ty3 g TMP_2 TMP_4 t0)))))) in (let TMP_55 \def (\lambda (x: T).(\lambda (H2: 
(ty3 g (CHead c (Bind Abst) w) (lift (S O) O u2) x)).(let TMP_6 \def (Bind 
Abst) in (let TMP_7 \def (CHead c TMP_6 w) in (let TMP_8 \def (S O) in (let 
TMP_9 \def (Bind Abst) in (let TMP_10 \def (drop_refl c) in (let TMP_11 \def 
(drop_drop TMP_9 O c c TMP_10 w) in (let H3 \def (ty3_gen_lift g TMP_7 u2 x 
TMP_8 O H2 c TMP_11) in (let TMP_16 \def (\lambda (t2: T).(let TMP_12 \def 
(Bind Abst) in (let TMP_13 \def (CHead c TMP_12 w) in (let TMP_14 \def (S O) 
in (let TMP_15 \def (lift TMP_14 O t2) in (pc3 TMP_13 TMP_15 x)))))) in (let 
TMP_17 \def (\lambda (t2: T).(ty3 g c u2 t2)) in (let TMP_54 \def (\lambda 
(x0: T).(\lambda (_: (pc3 (CHead c (Bind Abst) w) (lift (S O) O x0) 
x)).(\lambda (H5: (ty3 g c u2 x0)).(let TMP_18 \def (Bind Abst) in (let 
TMP_19 \def (THead TMP_18 w t) in (let H_y \def (ty3_conv g c u2 x0 H5 TMP_19 
u1 H H1) in (let TMP_20 \def (Bind Abst) in (let TMP_21 \def (CHead c TMP_20 
w) in (let TMP_22 \def (S O) in (let TMP_23 \def (lift TMP_22 O u2) in (let 
H_x \def (ty3_arity g TMP_21 t TMP_23 H0) in (let H6 \def H_x in (let TMP_26 
\def (\lambda (a1: A).(let TMP_24 \def (Bind Abst) in (let TMP_25 \def (CHead 
c TMP_24 w) in (arity g TMP_25 t a1)))) in (let TMP_32 \def (\lambda (a1: 
A).(let TMP_27 \def (Bind Abst) in (let TMP_28 \def (CHead c TMP_27 w) in 
(let TMP_29 \def (S O) in (let TMP_30 \def (lift TMP_29 O u2) in (let TMP_31 
\def (asucc g a1) in (arity g TMP_28 TMP_30 TMP_31))))))) in (let TMP_53 \def 
(\lambda (x1: A).(\lambda (H7: (arity g (CHead c (Bind Abst) w) t 
x1)).(\lambda (H8: (arity g (CHead c (Bind Abst) w) (lift (S O) O u2) (asucc 
g x1))).(let TMP_33 \def (Bind Abst) in (let TMP_34 \def (THead TMP_33 w t) 
in (let H_x0 \def (ty3_arity g c TMP_34 u2 H_y) in (let H9 \def H_x0 in (let 
TMP_37 \def (\lambda (a1: A).(let TMP_35 \def (Bind Abst) in (let TMP_36 \def 
(THead TMP_35 w t) in (arity g c TMP_36 a1)))) in (let TMP_39 \def (\lambda 
(a1: A).(let TMP_38 \def (asucc g a1) in (arity g c u2 TMP_38))) in (let 
TMP_52 \def (\lambda (x2: A).(\lambda (H10: (arity g c (THead (Bind Abst) w 
t) x2)).(\lambda (H11: (arity g c u2 (asucc g x2))).(let TMP_40 \def (asucc g 
x1) in (let TMP_41 \def (Bind Abst) in (let TMP_42 \def (CHead c TMP_41 w) in 
(let TMP_43 \def (asucc g x1) in (let TMP_44 \def (S O) in (let TMP_45 \def 
(Bind Abst) in (let TMP_46 \def (drop_refl c) in (let TMP_47 \def (drop_drop 
TMP_45 O c c TMP_46 w) in (let TMP_48 \def (arity_gen_lift g TMP_42 u2 TMP_43 
TMP_44 O H8 c TMP_47) in (let TMP_49 \def (asucc g x2) in (let TMP_50 \def 
(arity_mono g c u2 TMP_40 TMP_48 TMP_49 H11) in (let TMP_51 \def (asucc_inj g 
x1 x2 TMP_50) in (arity_repellent g c w t x1 H7 x2 H10 TMP_51 
P)))))))))))))))) in (ex2_ind A TMP_37 TMP_39 P TMP_52 H9))))))))))) in 
(ex2_ind A TMP_26 TMP_32 P TMP_53 H6)))))))))))))))) in (ex2_ind T TMP_16 
TMP_17 P TMP_54 H3))))))))))))) in (let TMP_56 \def (Bind Abst) in (let 
TMP_57 \def (CHead c TMP_56 w) in (let TMP_58 \def (S O) in (let TMP_59 \def 
(lift TMP_58 O u2) in (let TMP_60 \def (ty3_correct g TMP_57 t TMP_59 H0) in 
(ex_ind T TMP_5 P TMP_55 TMP_60))))))))))))))))).

theorem ty3_acyclic:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (u: T).((ty3 g c t 
u) \to ((pc3 c u t) \to (\forall (P: Prop).P))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (u: T).(\lambda (H: 
(ty3 g c t u)).(\lambda (H0: (pc3 c u t)).(\lambda (P: Prop).(let H_y \def 
(ty3_conv g c t u H t u H H0) in (let H_x \def (ty3_arity g c t t H_y) in 
(let H1 \def H_x in (let TMP_1 \def (\lambda (a1: A).(arity g c t a1)) in 
(let TMP_3 \def (\lambda (a1: A).(let TMP_2 \def (asucc g a1) in (arity g c t 
TMP_2))) in (let TMP_6 \def (\lambda (x: A).(\lambda (H2: (arity g c t 
x)).(\lambda (H3: (arity g c t (asucc g x))).(let TMP_4 \def (asucc g x) in 
(let TMP_5 \def (arity_mono g c t TMP_4 H3 x H2) in (leq_asucc_false g x 
TMP_5 P)))))) in (ex2_ind A TMP_1 TMP_3 P TMP_6 H1))))))))))))).

theorem ty3_sn3:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (u: T).((ty3 g c t 
u) \to (sn3 c t)))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (u: T).(\lambda (H: 
(ty3 g c t u)).(let H_x \def (ty3_arity g c t u H) in (let H0 \def H_x in 
(let TMP_1 \def (\lambda (a1: A).(arity g c t a1)) in (let TMP_3 \def 
(\lambda (a1: A).(let TMP_2 \def (asucc g a1) in (arity g c u TMP_2))) in 
(let TMP_4 \def (sn3 c t) in (let TMP_6 \def (\lambda (x: A).(\lambda (H1: 
(arity g c t x)).(\lambda (_: (arity g c u (asucc g x))).(let TMP_5 \def 
(sc3_arity g c t x H1) in (sc3_sn3 g x c t TMP_5))))) in (ex2_ind A TMP_1 
TMP_3 TMP_4 TMP_6 H0))))))))))).

