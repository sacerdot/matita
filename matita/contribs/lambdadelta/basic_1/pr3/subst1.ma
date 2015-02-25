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

include "basic_1/pr3/fwd.ma".

include "basic_1/pr2/subst1.ma".

theorem pr3_subst1:
 \forall (c: C).(\forall (e: C).(\forall (v: T).(\forall (i: nat).((getl i c 
(CHead e (Bind Abbr) v)) \to (\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) 
\to (\forall (w1: T).((subst1 i v t1 w1) \to (ex2 T (\lambda (w2: T).(pr3 c 
w1 w2)) (\lambda (w2: T).(subst1 i v t2 w2))))))))))))
\def
 \lambda (c: C).(\lambda (e: C).(\lambda (v: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead e (Bind Abbr) v))).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (H0: (pr3 c t1 t2)).(let TMP_3 \def (\lambda (t: T).(\lambda (t0: 
T).(\forall (w1: T).((subst1 i v t w1) \to (let TMP_1 \def (\lambda (w2: 
T).(pr3 c w1 w2)) in (let TMP_2 \def (\lambda (w2: T).(subst1 i v t0 w2)) in 
(ex2 T TMP_1 TMP_2))))))) in (let TMP_7 \def (\lambda (t: T).(\lambda (w1: 
T).(\lambda (H1: (subst1 i v t w1)).(let TMP_4 \def (\lambda (w2: T).(pr3 c 
w1 w2)) in (let TMP_5 \def (\lambda (w2: T).(subst1 i v t w2)) in (let TMP_6 
\def (pr3_refl c w1) in (ex_intro2 T TMP_4 TMP_5 w1 TMP_6 H1))))))) in (let 
TMP_25 \def (\lambda (t3: T).(\lambda (t4: T).(\lambda (H1: (pr2 c t4 
t3)).(\lambda (t5: T).(\lambda (_: (pr3 c t3 t5)).(\lambda (H3: ((\forall 
(w1: T).((subst1 i v t3 w1) \to (ex2 T (\lambda (w2: T).(pr3 c w1 w2)) 
(\lambda (w2: T).(subst1 i v t5 w2))))))).(\lambda (w1: T).(\lambda (H4: 
(subst1 i v t4 w1)).(let TMP_8 \def (\lambda (w2: T).(pr2 c w1 w2)) in (let 
TMP_9 \def (\lambda (w2: T).(subst1 i v t3 w2)) in (let TMP_10 \def (\lambda 
(w2: T).(pr3 c w1 w2)) in (let TMP_11 \def (\lambda (w2: T).(subst1 i v t5 
w2)) in (let TMP_12 \def (ex2 T TMP_10 TMP_11) in (let TMP_23 \def (\lambda 
(x: T).(\lambda (H5: (pr2 c w1 x)).(\lambda (H6: (subst1 i v t3 x)).(let 
TMP_13 \def (\lambda (w2: T).(pr3 c x w2)) in (let TMP_14 \def (\lambda (w2: 
T).(subst1 i v t5 w2)) in (let TMP_15 \def (\lambda (w2: T).(pr3 c w1 w2)) in 
(let TMP_16 \def (\lambda (w2: T).(subst1 i v t5 w2)) in (let TMP_17 \def 
(ex2 T TMP_15 TMP_16) in (let TMP_21 \def (\lambda (x0: T).(\lambda (H7: (pr3 
c x x0)).(\lambda (H8: (subst1 i v t5 x0)).(let TMP_18 \def (\lambda (w2: 
T).(pr3 c w1 w2)) in (let TMP_19 \def (\lambda (w2: T).(subst1 i v t5 w2)) in 
(let TMP_20 \def (pr3_sing c x w1 H5 x0 H7) in (ex_intro2 T TMP_18 TMP_19 x0 
TMP_20 H8))))))) in (let TMP_22 \def (H3 x H6) in (ex2_ind T TMP_13 TMP_14 
TMP_17 TMP_21 TMP_22))))))))))) in (let TMP_24 \def (pr2_subst1 c e v i H t4 
t3 H1 w1 H4) in (ex2_ind T TMP_8 TMP_9 TMP_12 TMP_23 TMP_24)))))))))))))))) 
in (pr3_ind c TMP_3 TMP_7 TMP_25 t1 t2 H0))))))))))).

theorem pr3_gen_cabbr:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (\forall 
(e: C).(\forall (u: T).(\forall (d: nat).((getl d c (CHead e (Bind Abbr) u)) 
\to (\forall (a0: C).((csubst1 d u c a0) \to (\forall (a: C).((drop (S O) d 
a0 a) \to (\forall (x1: T).((subst1 d u t1 (lift (S O) d x1)) \to (ex2 T 
(\lambda (x2: T).(subst1 d u t2 (lift (S O) d x2))) (\lambda (x2: T).(pr3 a 
x1 x2))))))))))))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr3 c t1 
t2)).(let TMP_5 \def (\lambda (t: T).(\lambda (t0: T).(\forall (e: 
C).(\forall (u: T).(\forall (d: nat).((getl d c (CHead e (Bind Abbr) u)) \to 
(\forall (a0: C).((csubst1 d u c a0) \to (\forall (a: C).((drop (S O) d a0 a) 
\to (\forall (x1: T).((subst1 d u t (lift (S O) d x1)) \to (let TMP_3 \def 
(\lambda (x2: T).(let TMP_1 \def (S O) in (let TMP_2 \def (lift TMP_1 d x2) 
in (subst1 d u t0 TMP_2)))) in (let TMP_4 \def (\lambda (x2: T).(pr3 a x1 
x2)) in (ex2 T TMP_3 TMP_4))))))))))))))) in (let TMP_11 \def (\lambda (t: 
T).(\lambda (e: C).(\lambda (u: T).(\lambda (d: nat).(\lambda (_: (getl d c 
(CHead e (Bind Abbr) u))).(\lambda (a0: C).(\lambda (_: (csubst1 d u c 
a0)).(\lambda (a: C).(\lambda (_: (drop (S O) d a0 a)).(\lambda (x1: 
T).(\lambda (H3: (subst1 d u t (lift (S O) d x1))).(let TMP_8 \def (\lambda 
(x2: T).(let TMP_6 \def (S O) in (let TMP_7 \def (lift TMP_6 d x2) in (subst1 
d u t TMP_7)))) in (let TMP_9 \def (\lambda (x2: T).(pr3 a x1 x2)) in (let 
TMP_10 \def (pr3_refl a x1) in (ex_intro2 T TMP_8 TMP_9 x1 H3 
TMP_10))))))))))))))) in (let TMP_39 \def (\lambda (t0: T).(\lambda (t3: 
T).(\lambda (H0: (pr2 c t3 t0)).(\lambda (t4: T).(\lambda (_: (pr3 c t0 
t4)).(\lambda (H2: ((\forall (e: C).(\forall (u: T).(\forall (d: nat).((getl 
d c (CHead e (Bind Abbr) u)) \to (\forall (a0: C).((csubst1 d u c a0) \to 
(\forall (a: C).((drop (S O) d a0 a) \to (\forall (x1: T).((subst1 d u t0 
(lift (S O) d x1)) \to (ex2 T (\lambda (x2: T).(subst1 d u t4 (lift (S O) d 
x2))) (\lambda (x2: T).(pr3 a x1 x2))))))))))))))).(\lambda (e: C).(\lambda 
(u: T).(\lambda (d: nat).(\lambda (H3: (getl d c (CHead e (Bind Abbr) 
u))).(\lambda (a0: C).(\lambda (H4: (csubst1 d u c a0)).(\lambda (a: 
C).(\lambda (H5: (drop (S O) d a0 a)).(\lambda (x1: T).(\lambda (H6: (subst1 
d u t3 (lift (S O) d x1))).(let TMP_14 \def (\lambda (x2: T).(let TMP_12 \def 
(S O) in (let TMP_13 \def (lift TMP_12 d x2) in (subst1 d u t0 TMP_13)))) in 
(let TMP_15 \def (\lambda (x2: T).(pr2 a x1 x2)) in (let TMP_18 \def (\lambda 
(x2: T).(let TMP_16 \def (S O) in (let TMP_17 \def (lift TMP_16 d x2) in 
(subst1 d u t4 TMP_17)))) in (let TMP_19 \def (\lambda (x2: T).(pr3 a x1 x2)) 
in (let TMP_20 \def (ex2 T TMP_18 TMP_19) in (let TMP_37 \def (\lambda (x: 
T).(\lambda (H7: (subst1 d u t0 (lift (S O) d x))).(\lambda (H8: (pr2 a x1 
x)).(let TMP_23 \def (\lambda (x2: T).(let TMP_21 \def (S O) in (let TMP_22 
\def (lift TMP_21 d x2) in (subst1 d u t4 TMP_22)))) in (let TMP_24 \def 
(\lambda (x2: T).(pr3 a x x2)) in (let TMP_27 \def (\lambda (x2: T).(let 
TMP_25 \def (S O) in (let TMP_26 \def (lift TMP_25 d x2) in (subst1 d u t4 
TMP_26)))) in (let TMP_28 \def (\lambda (x2: T).(pr3 a x1 x2)) in (let TMP_29 
\def (ex2 T TMP_27 TMP_28) in (let TMP_35 \def (\lambda (x0: T).(\lambda (H9: 
(subst1 d u t4 (lift (S O) d x0))).(\lambda (H10: (pr3 a x x0)).(let TMP_32 
\def (\lambda (x2: T).(let TMP_30 \def (S O) in (let TMP_31 \def (lift TMP_30 
d x2) in (subst1 d u t4 TMP_31)))) in (let TMP_33 \def (\lambda (x2: T).(pr3 
a x1 x2)) in (let TMP_34 \def (pr3_sing a x x1 H8 x0 H10) in (ex_intro2 T 
TMP_32 TMP_33 x0 H9 TMP_34))))))) in (let TMP_36 \def (H2 e u d H3 a0 H4 a H5 
x H7) in (ex2_ind T TMP_23 TMP_24 TMP_29 TMP_35 TMP_36))))))))))) in (let 
TMP_38 \def (pr2_gen_cabbr c t3 t0 H0 e u d H3 a0 H4 a H5 x1 H6) in (ex2_ind 
T TMP_14 TMP_15 TMP_20 TMP_37 TMP_38)))))))))))))))))))))))) in (pr3_ind c 
TMP_5 TMP_11 TMP_39 t1 t2 H))))))).

