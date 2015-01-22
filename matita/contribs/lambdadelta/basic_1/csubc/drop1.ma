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

include "Basic-1/csubc/drop.ma".

theorem drop1_csubc_trans:
 \forall (g: G).(\forall (hds: PList).(\forall (c2: C).(\forall (e2: 
C).((drop1 hds c2 e2) \to (\forall (e1: C).((csubc g e2 e1) \to (ex2 C 
(\lambda (c1: C).(drop1 hds c1 e1)) (\lambda (c1: C).(csubc g c2 c1)))))))))
\def
 \lambda (g: G).(\lambda (hds: PList).(PList_ind (\lambda (p: PList).(\forall 
(c2: C).(\forall (e2: C).((drop1 p c2 e2) \to (\forall (e1: C).((csubc g e2 
e1) \to (ex2 C (\lambda (c1: C).(drop1 p c1 e1)) (\lambda (c1: C).(csubc g c2 
c1))))))))) (\lambda (c2: C).(\lambda (e2: C).(\lambda (H: (drop1 PNil c2 
e2)).(\lambda (e1: C).(\lambda (H0: (csubc g e2 e1)).(let H_y \def 
(drop1_gen_pnil c2 e2 H) in (let H1 \def (eq_ind_r C e2 (\lambda (c: 
C).(csubc g c e1)) H0 c2 H_y) in (ex_intro2 C (\lambda (c1: C).(drop1 PNil c1 
e1)) (\lambda (c1: C).(csubc g c2 c1)) e1 (drop1_nil e1) H1)))))))) (\lambda 
(n: nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda (H: ((\forall (c2: 
C).(\forall (e2: C).((drop1 p c2 e2) \to (\forall (e1: C).((csubc g e2 e1) 
\to (ex2 C (\lambda (c1: C).(drop1 p c1 e1)) (\lambda (c1: C).(csubc g c2 
c1)))))))))).(\lambda (c2: C).(\lambda (e2: C).(\lambda (H0: (drop1 (PCons n 
n0 p) c2 e2)).(\lambda (e1: C).(\lambda (H1: (csubc g e2 e1)).(let H_x \def 
(drop1_gen_pcons c2 e2 p n n0 H0) in (let H2 \def H_x in (ex2_ind C (\lambda 
(c3: C).(drop n n0 c2 c3)) (\lambda (c3: C).(drop1 p c3 e2)) (ex2 C (\lambda 
(c1: C).(drop1 (PCons n n0 p) c1 e1)) (\lambda (c1: C).(csubc g c2 c1))) 
(\lambda (x: C).(\lambda (H3: (drop n n0 c2 x)).(\lambda (H4: (drop1 p x 
e2)).(let H_x0 \def (H x e2 H4 e1 H1) in (let H5 \def H_x0 in (ex2_ind C 
(\lambda (c1: C).(drop1 p c1 e1)) (\lambda (c1: C).(csubc g x c1)) (ex2 C 
(\lambda (c1: C).(drop1 (PCons n n0 p) c1 e1)) (\lambda (c1: C).(csubc g c2 
c1))) (\lambda (x0: C).(\lambda (H6: (drop1 p x0 e1)).(\lambda (H7: (csubc g 
x x0)).(let H_x1 \def (drop_csubc_trans g c2 x n0 n H3 x0 H7) in (let H8 \def 
H_x1 in (ex2_ind C (\lambda (c1: C).(drop n n0 c1 x0)) (\lambda (c1: 
C).(csubc g c2 c1)) (ex2 C (\lambda (c1: C).(drop1 (PCons n n0 p) c1 e1)) 
(\lambda (c1: C).(csubc g c2 c1))) (\lambda (x1: C).(\lambda (H9: (drop n n0 
x1 x0)).(\lambda (H10: (csubc g c2 x1)).(ex_intro2 C (\lambda (c1: C).(drop1 
(PCons n n0 p) c1 e1)) (\lambda (c1: C).(csubc g c2 c1)) x1 (drop1_cons x1 x0 
n n0 H9 e1 p H6) H10)))) H8)))))) H5)))))) H2)))))))))))) hds)).
(* COMMENTS
Initial nodes: 551
END *)

theorem csubc_drop1_conf_rev:
 \forall (g: G).(\forall (hds: PList).(\forall (c2: C).(\forall (e2: 
C).((drop1 hds c2 e2) \to (\forall (e1: C).((csubc g e1 e2) \to (ex2 C 
(\lambda (c1: C).(drop1 hds c1 e1)) (\lambda (c1: C).(csubc g c1 c2)))))))))
\def
 \lambda (g: G).(\lambda (hds: PList).(PList_ind (\lambda (p: PList).(\forall 
(c2: C).(\forall (e2: C).((drop1 p c2 e2) \to (\forall (e1: C).((csubc g e1 
e2) \to (ex2 C (\lambda (c1: C).(drop1 p c1 e1)) (\lambda (c1: C).(csubc g c1 
c2))))))))) (\lambda (c2: C).(\lambda (e2: C).(\lambda (H: (drop1 PNil c2 
e2)).(\lambda (e1: C).(\lambda (H0: (csubc g e1 e2)).(let H_y \def 
(drop1_gen_pnil c2 e2 H) in (let H1 \def (eq_ind_r C e2 (\lambda (c: 
C).(csubc g e1 c)) H0 c2 H_y) in (ex_intro2 C (\lambda (c1: C).(drop1 PNil c1 
e1)) (\lambda (c1: C).(csubc g c1 c2)) e1 (drop1_nil e1) H1)))))))) (\lambda 
(n: nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda (H: ((\forall (c2: 
C).(\forall (e2: C).((drop1 p c2 e2) \to (\forall (e1: C).((csubc g e1 e2) 
\to (ex2 C (\lambda (c1: C).(drop1 p c1 e1)) (\lambda (c1: C).(csubc g c1 
c2)))))))))).(\lambda (c2: C).(\lambda (e2: C).(\lambda (H0: (drop1 (PCons n 
n0 p) c2 e2)).(\lambda (e1: C).(\lambda (H1: (csubc g e1 e2)).(let H_x \def 
(drop1_gen_pcons c2 e2 p n n0 H0) in (let H2 \def H_x in (ex2_ind C (\lambda 
(c3: C).(drop n n0 c2 c3)) (\lambda (c3: C).(drop1 p c3 e2)) (ex2 C (\lambda 
(c1: C).(drop1 (PCons n n0 p) c1 e1)) (\lambda (c1: C).(csubc g c1 c2))) 
(\lambda (x: C).(\lambda (H3: (drop n n0 c2 x)).(\lambda (H4: (drop1 p x 
e2)).(let H_x0 \def (H x e2 H4 e1 H1) in (let H5 \def H_x0 in (ex2_ind C 
(\lambda (c1: C).(drop1 p c1 e1)) (\lambda (c1: C).(csubc g c1 x)) (ex2 C 
(\lambda (c1: C).(drop1 (PCons n n0 p) c1 e1)) (\lambda (c1: C).(csubc g c1 
c2))) (\lambda (x0: C).(\lambda (H6: (drop1 p x0 e1)).(\lambda (H7: (csubc g 
x0 x)).(let H_x1 \def (csubc_drop_conf_rev g c2 x n0 n H3 x0 H7) in (let H8 
\def H_x1 in (ex2_ind C (\lambda (c1: C).(drop n n0 c1 x0)) (\lambda (c1: 
C).(csubc g c1 c2)) (ex2 C (\lambda (c1: C).(drop1 (PCons n n0 p) c1 e1)) 
(\lambda (c1: C).(csubc g c1 c2))) (\lambda (x1: C).(\lambda (H9: (drop n n0 
x1 x0)).(\lambda (H10: (csubc g x1 c2)).(ex_intro2 C (\lambda (c1: C).(drop1 
(PCons n n0 p) c1 e1)) (\lambda (c1: C).(csubc g c1 c2)) x1 (drop1_cons x1 x0 
n n0 H9 e1 p H6) H10)))) H8)))))) H5)))))) H2)))))))))))) hds)).
(* COMMENTS
Initial nodes: 551
END *)

