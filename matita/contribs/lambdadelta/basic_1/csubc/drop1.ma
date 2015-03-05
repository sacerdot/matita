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

include "basic_1/csubc/drop.ma".

theorem drop1_csubc_trans:
 \forall (g: G).(\forall (hds: PList).(\forall (c2: C).(\forall (e2: 
C).((drop1 hds c2 e2) \to (\forall (e1: C).((csubc g e2 e1) \to (ex2 C 
(\lambda (c1: C).(drop1 hds c1 e1)) (\lambda (c1: C).(csubc g c2 c1)))))))))
\def
 \lambda (g: G).(\lambda (hds: PList).(let TMP_3 \def (\lambda (p: 
PList).(\forall (c2: C).(\forall (e2: C).((drop1 p c2 e2) \to (\forall (e1: 
C).((csubc g e2 e1) \to (let TMP_1 \def (\lambda (c1: C).(drop1 p c1 e1)) in 
(let TMP_2 \def (\lambda (c1: C).(csubc g c2 c1)) in (ex2 C TMP_1 
TMP_2))))))))) in (let TMP_8 \def (\lambda (c2: C).(\lambda (e2: C).(\lambda 
(H: (drop1 PNil c2 e2)).(\lambda (e1: C).(\lambda (H0: (csubc g e2 e1)).(let 
H_y \def (drop1_gen_pnil c2 e2 H) in (let TMP_4 \def (\lambda (c: C).(csubc g 
c e1)) in (let H1 \def (eq_ind_r C e2 TMP_4 H0 c2 H_y) in (let TMP_5 \def 
(\lambda (c1: C).(drop1 PNil c1 e1)) in (let TMP_6 \def (\lambda (c1: 
C).(csubc g c2 c1)) in (let TMP_7 \def (drop1_nil e1) in (ex_intro2 C TMP_5 
TMP_6 e1 TMP_7 H1)))))))))))) in (let TMP_34 \def (\lambda (n: nat).(\lambda 
(n0: nat).(\lambda (p: PList).(\lambda (H: ((\forall (c2: C).(\forall (e2: 
C).((drop1 p c2 e2) \to (\forall (e1: C).((csubc g e2 e1) \to (ex2 C (\lambda 
(c1: C).(drop1 p c1 e1)) (\lambda (c1: C).(csubc g c2 c1)))))))))).(\lambda 
(c2: C).(\lambda (e2: C).(\lambda (H0: (drop1 (PCons n n0 p) c2 e2)).(\lambda 
(e1: C).(\lambda (H1: (csubc g e2 e1)).(let H_x \def (drop1_gen_pcons c2 e2 p 
n n0 H0) in (let H2 \def H_x in (let TMP_9 \def (\lambda (c3: C).(drop n n0 
c2 c3)) in (let TMP_10 \def (\lambda (c3: C).(drop1 p c3 e2)) in (let TMP_12 
\def (\lambda (c1: C).(let TMP_11 \def (PCons n n0 p) in (drop1 TMP_11 c1 
e1))) in (let TMP_13 \def (\lambda (c1: C).(csubc g c2 c1)) in (let TMP_14 
\def (ex2 C TMP_12 TMP_13) in (let TMP_33 \def (\lambda (x: C).(\lambda (H3: 
(drop n n0 c2 x)).(\lambda (H4: (drop1 p x e2)).(let H_x0 \def (H x e2 H4 e1 
H1) in (let H5 \def H_x0 in (let TMP_15 \def (\lambda (c1: C).(drop1 p c1 
e1)) in (let TMP_16 \def (\lambda (c1: C).(csubc g x c1)) in (let TMP_18 \def 
(\lambda (c1: C).(let TMP_17 \def (PCons n n0 p) in (drop1 TMP_17 c1 e1))) in 
(let TMP_19 \def (\lambda (c1: C).(csubc g c2 c1)) in (let TMP_20 \def (ex2 C 
TMP_18 TMP_19) in (let TMP_32 \def (\lambda (x0: C).(\lambda (H6: (drop1 p x0 
e1)).(\lambda (H7: (csubc g x x0)).(let H_x1 \def (drop_csubc_trans g c2 x n0 
n H3 x0 H7) in (let H8 \def H_x1 in (let TMP_21 \def (\lambda (c1: C).(drop n 
n0 c1 x0)) in (let TMP_22 \def (\lambda (c1: C).(csubc g c2 c1)) in (let 
TMP_24 \def (\lambda (c1: C).(let TMP_23 \def (PCons n n0 p) in (drop1 TMP_23 
c1 e1))) in (let TMP_25 \def (\lambda (c1: C).(csubc g c2 c1)) in (let TMP_26 
\def (ex2 C TMP_24 TMP_25) in (let TMP_31 \def (\lambda (x1: C).(\lambda (H9: 
(drop n n0 x1 x0)).(\lambda (H10: (csubc g c2 x1)).(let TMP_28 \def (\lambda 
(c1: C).(let TMP_27 \def (PCons n n0 p) in (drop1 TMP_27 c1 e1))) in (let 
TMP_29 \def (\lambda (c1: C).(csubc g c2 c1)) in (let TMP_30 \def (drop1_cons 
x1 x0 n n0 H9 e1 p H6) in (ex_intro2 C TMP_28 TMP_29 x1 TMP_30 H10))))))) in 
(ex2_ind C TMP_21 TMP_22 TMP_26 TMP_31 H8)))))))))))) in (ex2_ind C TMP_15 
TMP_16 TMP_20 TMP_32 H5)))))))))))) in (ex2_ind C TMP_9 TMP_10 TMP_14 TMP_33 
H2)))))))))))))))))) in (PList_ind TMP_3 TMP_8 TMP_34 hds))))).

theorem csubc_drop1_conf_rev:
 \forall (g: G).(\forall (hds: PList).(\forall (c2: C).(\forall (e2: 
C).((drop1 hds c2 e2) \to (\forall (e1: C).((csubc g e1 e2) \to (ex2 C 
(\lambda (c1: C).(drop1 hds c1 e1)) (\lambda (c1: C).(csubc g c1 c2)))))))))
\def
 \lambda (g: G).(\lambda (hds: PList).(let TMP_3 \def (\lambda (p: 
PList).(\forall (c2: C).(\forall (e2: C).((drop1 p c2 e2) \to (\forall (e1: 
C).((csubc g e1 e2) \to (let TMP_1 \def (\lambda (c1: C).(drop1 p c1 e1)) in 
(let TMP_2 \def (\lambda (c1: C).(csubc g c1 c2)) in (ex2 C TMP_1 
TMP_2))))))))) in (let TMP_8 \def (\lambda (c2: C).(\lambda (e2: C).(\lambda 
(H: (drop1 PNil c2 e2)).(\lambda (e1: C).(\lambda (H0: (csubc g e1 e2)).(let 
H_y \def (drop1_gen_pnil c2 e2 H) in (let TMP_4 \def (\lambda (c: C).(csubc g 
e1 c)) in (let H1 \def (eq_ind_r C e2 TMP_4 H0 c2 H_y) in (let TMP_5 \def 
(\lambda (c1: C).(drop1 PNil c1 e1)) in (let TMP_6 \def (\lambda (c1: 
C).(csubc g c1 c2)) in (let TMP_7 \def (drop1_nil e1) in (ex_intro2 C TMP_5 
TMP_6 e1 TMP_7 H1)))))))))))) in (let TMP_34 \def (\lambda (n: nat).(\lambda 
(n0: nat).(\lambda (p: PList).(\lambda (H: ((\forall (c2: C).(\forall (e2: 
C).((drop1 p c2 e2) \to (\forall (e1: C).((csubc g e1 e2) \to (ex2 C (\lambda 
(c1: C).(drop1 p c1 e1)) (\lambda (c1: C).(csubc g c1 c2)))))))))).(\lambda 
(c2: C).(\lambda (e2: C).(\lambda (H0: (drop1 (PCons n n0 p) c2 e2)).(\lambda 
(e1: C).(\lambda (H1: (csubc g e1 e2)).(let H_x \def (drop1_gen_pcons c2 e2 p 
n n0 H0) in (let H2 \def H_x in (let TMP_9 \def (\lambda (c3: C).(drop n n0 
c2 c3)) in (let TMP_10 \def (\lambda (c3: C).(drop1 p c3 e2)) in (let TMP_12 
\def (\lambda (c1: C).(let TMP_11 \def (PCons n n0 p) in (drop1 TMP_11 c1 
e1))) in (let TMP_13 \def (\lambda (c1: C).(csubc g c1 c2)) in (let TMP_14 
\def (ex2 C TMP_12 TMP_13) in (let TMP_33 \def (\lambda (x: C).(\lambda (H3: 
(drop n n0 c2 x)).(\lambda (H4: (drop1 p x e2)).(let H_x0 \def (H x e2 H4 e1 
H1) in (let H5 \def H_x0 in (let TMP_15 \def (\lambda (c1: C).(drop1 p c1 
e1)) in (let TMP_16 \def (\lambda (c1: C).(csubc g c1 x)) in (let TMP_18 \def 
(\lambda (c1: C).(let TMP_17 \def (PCons n n0 p) in (drop1 TMP_17 c1 e1))) in 
(let TMP_19 \def (\lambda (c1: C).(csubc g c1 c2)) in (let TMP_20 \def (ex2 C 
TMP_18 TMP_19) in (let TMP_32 \def (\lambda (x0: C).(\lambda (H6: (drop1 p x0 
e1)).(\lambda (H7: (csubc g x0 x)).(let H_x1 \def (csubc_drop_conf_rev g c2 x 
n0 n H3 x0 H7) in (let H8 \def H_x1 in (let TMP_21 \def (\lambda (c1: 
C).(drop n n0 c1 x0)) in (let TMP_22 \def (\lambda (c1: C).(csubc g c1 c2)) 
in (let TMP_24 \def (\lambda (c1: C).(let TMP_23 \def (PCons n n0 p) in 
(drop1 TMP_23 c1 e1))) in (let TMP_25 \def (\lambda (c1: C).(csubc g c1 c2)) 
in (let TMP_26 \def (ex2 C TMP_24 TMP_25) in (let TMP_31 \def (\lambda (x1: 
C).(\lambda (H9: (drop n n0 x1 x0)).(\lambda (H10: (csubc g x1 c2)).(let 
TMP_28 \def (\lambda (c1: C).(let TMP_27 \def (PCons n n0 p) in (drop1 TMP_27 
c1 e1))) in (let TMP_29 \def (\lambda (c1: C).(csubc g c1 c2)) in (let TMP_30 
\def (drop1_cons x1 x0 n n0 H9 e1 p H6) in (ex_intro2 C TMP_28 TMP_29 x1 
TMP_30 H10))))))) in (ex2_ind C TMP_21 TMP_22 TMP_26 TMP_31 H8)))))))))))) in 
(ex2_ind C TMP_15 TMP_16 TMP_20 TMP_32 H5)))))))))))) in (ex2_ind C TMP_9 
TMP_10 TMP_14 TMP_33 H2)))))))))))))))))) in (PList_ind TMP_3 TMP_8 TMP_34 
hds))))).

