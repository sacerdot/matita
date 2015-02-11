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

include "basic_1/csubv/clear.ma".

include "basic_1/csubv/drop.ma".

include "basic_1/getl/fwd.ma".

theorem csubv_getl_conf:
 \forall (c1: C).(\forall (c2: C).((csubv c1 c2) \to (\forall (b1: 
B).(\forall (d1: C).(\forall (v1: T).(\forall (i: nat).((getl i c1 (CHead d1 
(Bind b1) v1)) \to (ex2_3 B C T (\lambda (_: B).(\lambda (d2: C).(\lambda (_: 
T).(csubv d1 d2)))) (\lambda (b2: B).(\lambda (d2: C).(\lambda (v2: T).(getl 
i c2 (CHead d2 (Bind b2) v2)))))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubv c1 c2)).(\lambda (b1: 
B).(\lambda (d1: C).(\lambda (v1: T).(\lambda (i: nat).(\lambda (H0: (getl i 
c1 (CHead d1 (Bind b1) v1))).(let TMP_1 \def (Bind b1) in (let TMP_2 \def 
(CHead d1 TMP_1 v1) in (let H1 \def (getl_gen_all c1 TMP_2 i H0) in (let 
TMP_3 \def (\lambda (e: C).(drop i O c1 e)) in (let TMP_6 \def (\lambda (e: 
C).(let TMP_4 \def (Bind b1) in (let TMP_5 \def (CHead d1 TMP_4 v1) in (clear 
e TMP_5)))) in (let TMP_7 \def (\lambda (_: B).(\lambda (d2: C).(\lambda (_: 
T).(csubv d1 d2)))) in (let TMP_10 \def (\lambda (b2: B).(\lambda (d2: 
C).(\lambda (v2: T).(let TMP_8 \def (Bind b2) in (let TMP_9 \def (CHead d2 
TMP_8 v2) in (getl i c2 TMP_9)))))) in (let TMP_11 \def (ex2_3 B C T TMP_7 
TMP_10) in (let TMP_37 \def (\lambda (x: C).(\lambda (H2: (drop i O c1 
x)).(\lambda (H3: (clear x (CHead d1 (Bind b1) v1))).(let H_x \def 
(csubv_drop_conf c1 c2 H x i H2) in (let H4 \def H_x in (let TMP_12 \def 
(\lambda (e2: C).(csubv x e2)) in (let TMP_13 \def (\lambda (e2: C).(drop i O 
c2 e2)) in (let TMP_14 \def (\lambda (_: B).(\lambda (d2: C).(\lambda (_: 
T).(csubv d1 d2)))) in (let TMP_17 \def (\lambda (b2: B).(\lambda (d2: 
C).(\lambda (v2: T).(let TMP_15 \def (Bind b2) in (let TMP_16 \def (CHead d2 
TMP_15 v2) in (getl i c2 TMP_16)))))) in (let TMP_18 \def (ex2_3 B C T TMP_14 
TMP_17) in (let TMP_36 \def (\lambda (x0: C).(\lambda (H5: (csubv x 
x0)).(\lambda (H6: (drop i O c2 x0)).(let H_x0 \def (csubv_clear_conf x x0 H5 
b1 d1 v1 H3) in (let H7 \def H_x0 in (let TMP_19 \def (\lambda (_: 
B).(\lambda (d2: C).(\lambda (_: T).(csubv d1 d2)))) in (let TMP_22 \def 
(\lambda (b2: B).(\lambda (d2: C).(\lambda (v2: T).(let TMP_20 \def (Bind b2) 
in (let TMP_21 \def (CHead d2 TMP_20 v2) in (clear x0 TMP_21)))))) in (let 
TMP_23 \def (\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csubv d1 d2)))) 
in (let TMP_26 \def (\lambda (b2: B).(\lambda (d2: C).(\lambda (v2: T).(let 
TMP_24 \def (Bind b2) in (let TMP_25 \def (CHead d2 TMP_24 v2) in (getl i c2 
TMP_25)))))) in (let TMP_27 \def (ex2_3 B C T TMP_23 TMP_26) in (let TMP_35 
\def (\lambda (x1: B).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H8: (csubv 
d1 x2)).(\lambda (H9: (clear x0 (CHead x2 (Bind x1) x3))).(let TMP_28 \def 
(\lambda (_: B).(\lambda (d2: C).(\lambda (_: T).(csubv d1 d2)))) in (let 
TMP_31 \def (\lambda (b2: B).(\lambda (d2: C).(\lambda (v2: T).(let TMP_29 
\def (Bind b2) in (let TMP_30 \def (CHead d2 TMP_29 v2) in (getl i c2 
TMP_30)))))) in (let TMP_32 \def (Bind x1) in (let TMP_33 \def (CHead x2 
TMP_32 x3) in (let TMP_34 \def (getl_intro i c2 TMP_33 x0 H6 H9) in 
(ex2_3_intro B C T TMP_28 TMP_31 x1 x2 x3 H8 TMP_34))))))))))) in (ex2_3_ind 
B C T TMP_19 TMP_22 TMP_27 TMP_35 H7)))))))))))) in (ex2_ind C TMP_12 TMP_13 
TMP_18 TMP_36 H4)))))))))))) in (ex2_ind C TMP_3 TMP_6 TMP_11 TMP_37 
H1))))))))))))))))).

theorem csubv_getl_conf_void:
 \forall (c1: C).(\forall (c2: C).((csubv c1 c2) \to (\forall (d1: 
C).(\forall (v1: T).(\forall (i: nat).((getl i c1 (CHead d1 (Bind Void) v1)) 
\to (ex2_2 C T (\lambda (d2: C).(\lambda (_: T).(csubv d1 d2))) (\lambda (d2: 
C).(\lambda (v2: T).(getl i c2 (CHead d2 (Bind Void) v2)))))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubv c1 c2)).(\lambda (d1: 
C).(\lambda (v1: T).(\lambda (i: nat).(\lambda (H0: (getl i c1 (CHead d1 
(Bind Void) v1))).(let TMP_1 \def (Bind Void) in (let TMP_2 \def (CHead d1 
TMP_1 v1) in (let H1 \def (getl_gen_all c1 TMP_2 i H0) in (let TMP_3 \def 
(\lambda (e: C).(drop i O c1 e)) in (let TMP_6 \def (\lambda (e: C).(let 
TMP_4 \def (Bind Void) in (let TMP_5 \def (CHead d1 TMP_4 v1) in (clear e 
TMP_5)))) in (let TMP_7 \def (\lambda (d2: C).(\lambda (_: T).(csubv d1 d2))) 
in (let TMP_10 \def (\lambda (d2: C).(\lambda (v2: T).(let TMP_8 \def (Bind 
Void) in (let TMP_9 \def (CHead d2 TMP_8 v2) in (getl i c2 TMP_9))))) in (let 
TMP_11 \def (ex2_2 C T TMP_7 TMP_10) in (let TMP_37 \def (\lambda (x: 
C).(\lambda (H2: (drop i O c1 x)).(\lambda (H3: (clear x (CHead d1 (Bind 
Void) v1))).(let H_x \def (csubv_drop_conf c1 c2 H x i H2) in (let H4 \def 
H_x in (let TMP_12 \def (\lambda (e2: C).(csubv x e2)) in (let TMP_13 \def 
(\lambda (e2: C).(drop i O c2 e2)) in (let TMP_14 \def (\lambda (d2: 
C).(\lambda (_: T).(csubv d1 d2))) in (let TMP_17 \def (\lambda (d2: 
C).(\lambda (v2: T).(let TMP_15 \def (Bind Void) in (let TMP_16 \def (CHead 
d2 TMP_15 v2) in (getl i c2 TMP_16))))) in (let TMP_18 \def (ex2_2 C T TMP_14 
TMP_17) in (let TMP_36 \def (\lambda (x0: C).(\lambda (H5: (csubv x 
x0)).(\lambda (H6: (drop i O c2 x0)).(let H_x0 \def (csubv_clear_conf_void x 
x0 H5 d1 v1 H3) in (let H7 \def H_x0 in (let TMP_19 \def (\lambda (d2: 
C).(\lambda (_: T).(csubv d1 d2))) in (let TMP_22 \def (\lambda (d2: 
C).(\lambda (v2: T).(let TMP_20 \def (Bind Void) in (let TMP_21 \def (CHead 
d2 TMP_20 v2) in (clear x0 TMP_21))))) in (let TMP_23 \def (\lambda (d2: 
C).(\lambda (_: T).(csubv d1 d2))) in (let TMP_26 \def (\lambda (d2: 
C).(\lambda (v2: T).(let TMP_24 \def (Bind Void) in (let TMP_25 \def (CHead 
d2 TMP_24 v2) in (getl i c2 TMP_25))))) in (let TMP_27 \def (ex2_2 C T TMP_23 
TMP_26) in (let TMP_35 \def (\lambda (x1: C).(\lambda (x2: T).(\lambda (H8: 
(csubv d1 x1)).(\lambda (H9: (clear x0 (CHead x1 (Bind Void) x2))).(let 
TMP_28 \def (\lambda (d2: C).(\lambda (_: T).(csubv d1 d2))) in (let TMP_31 
\def (\lambda (d2: C).(\lambda (v2: T).(let TMP_29 \def (Bind Void) in (let 
TMP_30 \def (CHead d2 TMP_29 v2) in (getl i c2 TMP_30))))) in (let TMP_32 
\def (Bind Void) in (let TMP_33 \def (CHead x1 TMP_32 x2) in (let TMP_34 \def 
(getl_intro i c2 TMP_33 x0 H6 H9) in (ex2_2_intro C T TMP_28 TMP_31 x1 x2 H8 
TMP_34)))))))))) in (ex2_2_ind C T TMP_19 TMP_22 TMP_27 TMP_35 H7)))))))))))) 
in (ex2_ind C TMP_12 TMP_13 TMP_18 TMP_36 H4)))))))))))) in (ex2_ind C TMP_3 
TMP_6 TMP_11 TMP_37 H1)))))))))))))))).

