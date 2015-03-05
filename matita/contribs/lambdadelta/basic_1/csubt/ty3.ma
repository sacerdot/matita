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

include "basic_1/csubt/pc3.ma".

include "basic_1/csubt/props.ma".

include "basic_1/ty3/fwd.ma".

theorem csubt_ty3:
 \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c1 
t1 t2) \to (\forall (c2: C).((csubt g c1 c2) \to (ty3 g c2 t1 t2)))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (ty3 g c1 t1 t2)).(let TMP_1 \def (\lambda (c: C).(\lambda (t: 
T).(\lambda (t0: T).(\forall (c2: C).((csubt g c c2) \to (ty3 g c2 t t0)))))) 
in (let TMP_5 \def (\lambda (c: C).(\lambda (t0: T).(\lambda (t: T).(\lambda 
(_: (ty3 g c t0 t)).(\lambda (H1: ((\forall (c2: C).((csubt g c c2) \to (ty3 
g c2 t0 t))))).(\lambda (u: T).(\lambda (t3: T).(\lambda (_: (ty3 g c u 
t3)).(\lambda (H3: ((\forall (c2: C).((csubt g c c2) \to (ty3 g c2 u 
t3))))).(\lambda (H4: (pc3 c t3 t0)).(\lambda (c2: C).(\lambda (H5: (csubt g 
c c2)).(let TMP_2 \def (H1 c2 H5) in (let TMP_3 \def (H3 c2 H5) in (let TMP_4 
\def (csubt_pc3 g c t3 t0 H4 c2 H5) in (ty3_conv g c2 t0 t TMP_2 u t3 TMP_3 
TMP_4)))))))))))))))) in (let TMP_6 \def (\lambda (c: C).(\lambda (m: 
nat).(\lambda (c2: C).(\lambda (_: (csubt g c c2)).(ty3_sort g c2 m))))) in 
(let TMP_17 \def (\lambda (n: nat).(\lambda (c: C).(\lambda (d: C).(\lambda 
(u: T).(\lambda (H0: (getl n c (CHead d (Bind Abbr) u))).(\lambda (t: 
T).(\lambda (_: (ty3 g d u t)).(\lambda (H2: ((\forall (c2: C).((csubt g d 
c2) \to (ty3 g c2 u t))))).(\lambda (c2: C).(\lambda (H3: (csubt g c 
c2)).(let H4 \def (csubt_getl_abbr g c d u n H0 c2 H3) in (let TMP_7 \def 
(\lambda (d2: C).(csubt g d d2)) in (let TMP_10 \def (\lambda (d2: C).(let 
TMP_8 \def (Bind Abbr) in (let TMP_9 \def (CHead d2 TMP_8 u) in (getl n c2 
TMP_9)))) in (let TMP_11 \def (TLRef n) in (let TMP_12 \def (S n) in (let 
TMP_13 \def (lift TMP_12 O t) in (let TMP_14 \def (ty3 g c2 TMP_11 TMP_13) in 
(let TMP_16 \def (\lambda (x: C).(\lambda (H5: (csubt g d x)).(\lambda (H6: 
(getl n c2 (CHead x (Bind Abbr) u))).(let TMP_15 \def (H2 x H5) in (ty3_abbr 
g n c2 x u H6 t TMP_15))))) in (ex2_ind C TMP_7 TMP_10 TMP_14 TMP_16 
H4))))))))))))))))))) in (let TMP_57 \def (\lambda (n: nat).(\lambda (c: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (H0: (getl n c (CHead d (Bind 
Abst) u))).(\lambda (t: T).(\lambda (_: (ty3 g d u t)).(\lambda (H2: 
((\forall (c2: C).((csubt g d c2) \to (ty3 g c2 u t))))).(\lambda (c2: 
C).(\lambda (H3: (csubt g c c2)).(let H4 \def (csubt_getl_abst g c d u n H0 
c2 H3) in (let TMP_18 \def (\lambda (d2: C).(csubt g d d2)) in (let TMP_21 
\def (\lambda (d2: C).(let TMP_19 \def (Bind Abst) in (let TMP_20 \def (CHead 
d2 TMP_19 u) in (getl n c2 TMP_20)))) in (let TMP_22 \def (ex2 C TMP_18 
TMP_21) in (let TMP_23 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d d2))) 
in (let TMP_26 \def (\lambda (d2: C).(\lambda (u0: T).(let TMP_24 \def (Bind 
Abbr) in (let TMP_25 \def (CHead d2 TMP_24 u0) in (getl n c2 TMP_25))))) in 
(let TMP_27 \def (\lambda (_: C).(\lambda (u0: T).(ty3 g d u0 u))) in (let 
TMP_28 \def (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 u))) in (let 
TMP_29 \def (ex4_2 C T TMP_23 TMP_26 TMP_27 TMP_28) in (let TMP_30 \def 
(TLRef n) in (let TMP_31 \def (S n) in (let TMP_32 \def (lift TMP_31 O u) in 
(let TMP_33 \def (ty3 g c2 TMP_30 TMP_32) in (let TMP_44 \def (\lambda (H5: 
(ex2 C (\lambda (d2: C).(csubt g d d2)) (\lambda (d2: C).(getl n c2 (CHead d2 
(Bind Abst) u))))).(let TMP_34 \def (\lambda (d2: C).(csubt g d d2)) in (let 
TMP_37 \def (\lambda (d2: C).(let TMP_35 \def (Bind Abst) in (let TMP_36 \def 
(CHead d2 TMP_35 u) in (getl n c2 TMP_36)))) in (let TMP_38 \def (TLRef n) in 
(let TMP_39 \def (S n) in (let TMP_40 \def (lift TMP_39 O u) in (let TMP_41 
\def (ty3 g c2 TMP_38 TMP_40) in (let TMP_43 \def (\lambda (x: C).(\lambda 
(H6: (csubt g d x)).(\lambda (H7: (getl n c2 (CHead x (Bind Abst) u))).(let 
TMP_42 \def (H2 x H6) in (ty3_abst g n c2 x u H7 t TMP_42))))) in (ex2_ind C 
TMP_34 TMP_37 TMP_41 TMP_43 H5))))))))) in (let TMP_56 \def (\lambda (H5: 
(ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d d2))) (\lambda (d2: 
C).(\lambda (u0: T).(getl n c2 (CHead d2 (Bind Abbr) u0)))) (\lambda (_: 
C).(\lambda (u0: T).(ty3 g d u0 u))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g 
d2 u0 u))))).(let TMP_45 \def (\lambda (d2: C).(\lambda (_: T).(csubt g d 
d2))) in (let TMP_48 \def (\lambda (d2: C).(\lambda (u0: T).(let TMP_46 \def 
(Bind Abbr) in (let TMP_47 \def (CHead d2 TMP_46 u0) in (getl n c2 
TMP_47))))) in (let TMP_49 \def (\lambda (_: C).(\lambda (u0: T).(ty3 g d u0 
u))) in (let TMP_50 \def (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 u0 u))) 
in (let TMP_51 \def (TLRef n) in (let TMP_52 \def (S n) in (let TMP_53 \def 
(lift TMP_52 O u) in (let TMP_54 \def (ty3 g c2 TMP_51 TMP_53) in (let TMP_55 
\def (\lambda (x0: C).(\lambda (x1: T).(\lambda (_: (csubt g d x0)).(\lambda 
(H7: (getl n c2 (CHead x0 (Bind Abbr) x1))).(\lambda (_: (ty3 g d x1 
u)).(\lambda (H9: (ty3 g x0 x1 u)).(ty3_abbr g n c2 x0 x1 H7 u H9))))))) in 
(ex4_2_ind C T TMP_45 TMP_48 TMP_49 TMP_50 TMP_54 TMP_55 H5))))))))))) in 
(or_ind TMP_22 TMP_29 TMP_33 TMP_44 TMP_56 H4)))))))))))))))))))))))))) in 
(let TMP_64 \def (\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (_: 
(ty3 g c u t)).(\lambda (H1: ((\forall (c2: C).((csubt g c c2) \to (ty3 g c2 
u t))))).(\lambda (b: B).(\lambda (t0: T).(\lambda (t3: T).(\lambda (_: (ty3 
g (CHead c (Bind b) u) t0 t3)).(\lambda (H3: ((\forall (c2: C).((csubt g 
(CHead c (Bind b) u) c2) \to (ty3 g c2 t0 t3))))).(\lambda (c2: C).(\lambda 
(H4: (csubt g c c2)).(let TMP_58 \def (H1 c2 H4) in (let TMP_59 \def (Bind b) 
in (let TMP_60 \def (CHead c2 TMP_59 u) in (let TMP_61 \def (Bind b) in (let 
TMP_62 \def (csubt_head g c c2 H4 TMP_61 u) in (let TMP_63 \def (H3 TMP_60 
TMP_62) in (ty3_bind g c2 u t TMP_58 b t0 t3 TMP_63))))))))))))))))))) in 
(let TMP_67 \def (\lambda (c: C).(\lambda (w: T).(\lambda (u: T).(\lambda (_: 
(ty3 g c w u)).(\lambda (H1: ((\forall (c2: C).((csubt g c c2) \to (ty3 g c2 
w u))))).(\lambda (v: T).(\lambda (t: T).(\lambda (_: (ty3 g c v (THead (Bind 
Abst) u t))).(\lambda (H3: ((\forall (c2: C).((csubt g c c2) \to (ty3 g c2 v 
(THead (Bind Abst) u t)))))).(\lambda (c2: C).(\lambda (H4: (csubt g c 
c2)).(let TMP_65 \def (H1 c2 H4) in (let TMP_66 \def (H3 c2 H4) in (ty3_appl 
g c2 w u TMP_65 v t TMP_66)))))))))))))) in (let TMP_70 \def (\lambda (c: 
C).(\lambda (t0: T).(\lambda (t3: T).(\lambda (_: (ty3 g c t0 t3)).(\lambda 
(H1: ((\forall (c2: C).((csubt g c c2) \to (ty3 g c2 t0 t3))))).(\lambda (t4: 
T).(\lambda (_: (ty3 g c t3 t4)).(\lambda (H3: ((\forall (c2: C).((csubt g c 
c2) \to (ty3 g c2 t3 t4))))).(\lambda (c2: C).(\lambda (H4: (csubt g c 
c2)).(let TMP_68 \def (H1 c2 H4) in (let TMP_69 \def (H3 c2 H4) in (ty3_cast 
g c2 t0 t3 TMP_68 t4 TMP_69))))))))))))) in (ty3_ind g TMP_1 TMP_5 TMP_6 
TMP_17 TMP_57 TMP_64 TMP_67 TMP_70 c1 t1 t2 H))))))))))))).

theorem csubt_ty3_ld:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (v: T).((ty3 g c u 
v) \to (\forall (t1: T).(\forall (t2: T).((ty3 g (CHead c (Bind Abst) v) t1 
t2) \to (ty3 g (CHead c (Bind Abbr) u) t1 t2))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (v: T).(\lambda (H: 
(ty3 g c u v)).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (ty3 g (CHead 
c (Bind Abst) v) t1 t2)).(let TMP_1 \def (Bind Abst) in (let TMP_2 \def 
(CHead c TMP_1 v) in (let TMP_3 \def (Bind Abbr) in (let TMP_4 \def (CHead c 
TMP_3 u) in (let TMP_5 \def (csubt_refl g c) in (let TMP_6 \def (csubt_abst g 
c c TMP_5 u v H H) in (csubt_ty3 g TMP_2 t1 t2 H0 TMP_4 TMP_6)))))))))))))).

