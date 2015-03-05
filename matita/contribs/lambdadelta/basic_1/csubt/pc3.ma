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

include "basic_1/csubt/getl.ma".

include "basic_1/pc3/left.ma".

theorem csubt_pr2:
 \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t2: T).((pr2 c1 
t1 t2) \to (\forall (c2: C).((csubt g c1 c2) \to (pr2 c2 t1 t2)))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (pr2 c1 t1 t2)).(let TMP_1 \def (\lambda (c: C).(\lambda (t: T).(\lambda 
(t0: T).(\forall (c2: C).((csubt g c c2) \to (pr2 c2 t t0)))))) in (let TMP_2 
\def (\lambda (c: C).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H0: (pr0 t3 
t4)).(\lambda (c2: C).(\lambda (_: (csubt g c c2)).(pr2_free c2 t3 t4 
H0))))))) in (let TMP_9 \def (\lambda (c: C).(\lambda (d: C).(\lambda (u: 
T).(\lambda (i: nat).(\lambda (H0: (getl i c (CHead d (Bind Abbr) 
u))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H1: (pr0 t3 t4)).(\lambda 
(t: T).(\lambda (H2: (subst0 i u t4 t)).(\lambda (c2: C).(\lambda (H3: (csubt 
g c c2)).(let H4 \def (csubt_getl_abbr g c d u i H0 c2 H3) in (let TMP_3 \def 
(\lambda (d2: C).(csubt g d d2)) in (let TMP_6 \def (\lambda (d2: C).(let 
TMP_4 \def (Bind Abbr) in (let TMP_5 \def (CHead d2 TMP_4 u) in (getl i c2 
TMP_5)))) in (let TMP_7 \def (pr2 c2 t3 t) in (let TMP_8 \def (\lambda (x: 
C).(\lambda (_: (csubt g d x)).(\lambda (H6: (getl i c2 (CHead x (Bind Abbr) 
u))).(pr2_delta c2 x u i H6 t3 t4 H1 t H2)))) in (ex2_ind C TMP_3 TMP_6 TMP_7 
TMP_8 H4)))))))))))))))))) in (pr2_ind TMP_1 TMP_2 TMP_9 c1 t1 t2 H)))))))).

theorem csubt_pc3:
 \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t2: T).((pc3 c1 
t1 t2) \to (\forall (c2: C).((csubt g c1 c2) \to (pc3 c2 t1 t2)))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (pc3 c1 t1 t2)).(let TMP_1 \def (\lambda (t: T).(\lambda (t0: T).(\forall 
(c2: C).((csubt g c1 c2) \to (pc3 c2 t t0))))) in (let TMP_2 \def (\lambda 
(t: T).(\lambda (c2: C).(\lambda (_: (csubt g c1 c2)).(pc3_refl c2 t)))) in 
(let TMP_6 \def (\lambda (t0: T).(\lambda (t3: T).(\lambda (H0: (pr2 c1 t0 
t3)).(\lambda (t4: T).(\lambda (_: (pc3 c1 t3 t4)).(\lambda (H2: ((\forall 
(c2: C).((csubt g c1 c2) \to (pc3 c2 t3 t4))))).(\lambda (c2: C).(\lambda 
(H3: (csubt g c1 c2)).(let TMP_3 \def (csubt_pr2 g c1 t0 t3 H0 c2 H3) in (let 
TMP_4 \def (pc3_pr2_r c2 t0 t3 TMP_3) in (let TMP_5 \def (H2 c2 H3) in (pc3_t 
t3 c2 t0 TMP_4 t4 TMP_5)))))))))))) in (let TMP_10 \def (\lambda (t0: 
T).(\lambda (t3: T).(\lambda (H0: (pr2 c1 t0 t3)).(\lambda (t4: T).(\lambda 
(_: (pc3 c1 t0 t4)).(\lambda (H2: ((\forall (c2: C).((csubt g c1 c2) \to (pc3 
c2 t0 t4))))).(\lambda (c2: C).(\lambda (H3: (csubt g c1 c2)).(let TMP_7 \def 
(csubt_pr2 g c1 t0 t3 H0 c2 H3) in (let TMP_8 \def (pc3_pr2_x c2 t3 t0 TMP_7) 
in (let TMP_9 \def (H2 c2 H3) in (pc3_t t0 c2 t3 TMP_8 t4 TMP_9)))))))))))) 
in (pc3_ind_left c1 TMP_1 TMP_2 TMP_6 TMP_10 t1 t2 H))))))))).

