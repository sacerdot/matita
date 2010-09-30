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

include "Basic-1/wf3/getl.ma".

theorem wf3_pr2_conf:
 \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t2: T).((pr2 c1 
t1 t2) \to (\forall (c2: C).((wf3 g c1 c2) \to (\forall (u: T).((ty3 g c1 t1 
u) \to (pr2 c2 t1 t2)))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (pr2 c1 t1 t2)).(pr2_ind (\lambda (c: C).(\lambda (t: T).(\lambda (t0: 
T).(\forall (c2: C).((wf3 g c c2) \to (\forall (u: T).((ty3 g c t u) \to (pr2 
c2 t t0)))))))) (\lambda (c: C).(\lambda (t3: T).(\lambda (t4: T).(\lambda 
(H0: (pr0 t3 t4)).(\lambda (c2: C).(\lambda (_: (wf3 g c c2)).(\lambda (u: 
T).(\lambda (_: (ty3 g c t3 u)).(pr2_free c2 t3 t4 H0))))))))) (\lambda (c: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c 
(CHead d (Bind Abbr) u))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H1: 
(pr0 t3 t4)).(\lambda (t: T).(\lambda (H2: (subst0 i u t4 t)).(\lambda (c2: 
C).(\lambda (H3: (wf3 g c c2)).(\lambda (u0: T).(\lambda (H4: (ty3 g c t3 
u0)).(let H_y \def (ty3_sred_pr0 t3 t4 H1 g c u0 H4) in (let H_x \def 
(ty3_getl_subst0 g c t4 u0 H_y u t i H2 Abbr d u H0) in (let H5 \def H_x in 
(ex_ind T (\lambda (w: T).(ty3 g d u w)) (pr2 c2 t3 t) (\lambda (x: 
T).(\lambda (H6: (ty3 g d u x)).(let H_x0 \def (wf3_getl_conf Abbr i c d u H0 
g c2 H3 x H6) in (let H7 \def H_x0 in (ex2_ind C (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(wf3 g d d2)) (pr2 c2 t3 t) 
(\lambda (x0: C).(\lambda (H8: (getl i c2 (CHead x0 (Bind Abbr) u))).(\lambda 
(_: (wf3 g d x0)).(pr2_delta c2 x0 u i H8 t3 t4 H1 t H2)))) H7))))) 
H5)))))))))))))))))) c1 t1 t2 H))))).
(* COMMENTS
Initial nodes: 373
END *)

theorem wf3_pr3_conf:
 \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t2: T).((pr3 c1 
t1 t2) \to (\forall (c2: C).((wf3 g c1 c2) \to (\forall (u: T).((ty3 g c1 t1 
u) \to (pr3 c2 t1 t2)))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (pr3 c1 t1 t2)).(pr3_ind c1 (\lambda (t: T).(\lambda (t0: T).(\forall 
(c2: C).((wf3 g c1 c2) \to (\forall (u: T).((ty3 g c1 t u) \to (pr3 c2 t 
t0))))))) (\lambda (t: T).(\lambda (c2: C).(\lambda (_: (wf3 g c1 
c2)).(\lambda (u: T).(\lambda (_: (ty3 g c1 t u)).(pr3_refl c2 t)))))) 
(\lambda (t3: T).(\lambda (t4: T).(\lambda (H0: (pr2 c1 t4 t3)).(\lambda (t5: 
T).(\lambda (_: (pr3 c1 t3 t5)).(\lambda (H2: ((\forall (c2: C).((wf3 g c1 
c2) \to (\forall (u: T).((ty3 g c1 t3 u) \to (pr3 c2 t3 t5))))))).(\lambda 
(c2: C).(\lambda (H3: (wf3 g c1 c2)).(\lambda (u: T).(\lambda (H4: (ty3 g c1 
t4 u)).(pr3_sing c2 t3 t4 (wf3_pr2_conf g c1 t4 t3 H0 c2 H3 u H4) t5 (H2 c2 
H3 u (ty3_sred_pr2 c1 t4 t3 H0 g u H4))))))))))))) t1 t2 H))))).
(* COMMENTS
Initial nodes: 217
END *)

theorem wf3_pc3_conf:
 \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t2: T).((pc3 c1 
t1 t2) \to (\forall (c2: C).((wf3 g c1 c2) \to (\forall (u1: T).((ty3 g c1 t1 
u1) \to (\forall (u2: T).((ty3 g c1 t2 u2) \to (pc3 c2 t1 t2)))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (pc3 c1 t1 t2)).(\lambda (c2: C).(\lambda (H0: (wf3 g c1 c2)).(\lambda 
(u1: T).(\lambda (H1: (ty3 g c1 t1 u1)).(\lambda (u2: T).(\lambda (H2: (ty3 g 
c1 t2 u2)).(let H3 \def H in (ex2_ind T (\lambda (t: T).(pr3 c1 t1 t)) 
(\lambda (t: T).(pr3 c1 t2 t)) (pc3 c2 t1 t2) (\lambda (x: T).(\lambda (H4: 
(pr3 c1 t1 x)).(\lambda (H5: (pr3 c1 t2 x)).(pc3_pr3_t c2 t1 x (wf3_pr3_conf 
g c1 t1 x H4 c2 H0 u1 H1) t2 (wf3_pr3_conf g c1 t2 x H5 c2 H0 u2 H2))))) 
H3)))))))))))).
(* COMMENTS
Initial nodes: 153
END *)

theorem wf3_ty3_conf:
 \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c1 
t1 t2) \to (\forall (c2: C).((wf3 g c1 c2) \to (ty3 g c2 t1 t2)))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (ty3 g c1 t1 t2)).(ty3_ind g (\lambda (c: C).(\lambda (t: T).(\lambda 
(t0: T).(\forall (c2: C).((wf3 g c c2) \to (ty3 g c2 t t0)))))) (\lambda (c: 
C).(\lambda (t3: T).(\lambda (t: T).(\lambda (H0: (ty3 g c t3 t)).(\lambda 
(H1: ((\forall (c2: C).((wf3 g c c2) \to (ty3 g c2 t3 t))))).(\lambda (u: 
T).(\lambda (t4: T).(\lambda (H2: (ty3 g c u t4)).(\lambda (H3: ((\forall 
(c2: C).((wf3 g c c2) \to (ty3 g c2 u t4))))).(\lambda (H4: (pc3 c t4 
t3)).(\lambda (c2: C).(\lambda (H5: (wf3 g c c2)).(ex_ind T (\lambda (t0: 
T).(ty3 g c t4 t0)) (ty3 g c2 u t3) (\lambda (x: T).(\lambda (H6: (ty3 g c t4 
x)).(ty3_conv g c2 t3 t (H1 c2 H5) u t4 (H3 c2 H5) (wf3_pc3_conf g c t4 t3 H4 
c2 H5 x H6 t H0)))) (ty3_correct g c u t4 H2)))))))))))))) (\lambda (c: 
C).(\lambda (m: nat).(\lambda (c2: C).(\lambda (_: (wf3 g c c2)).(ty3_sort g 
c2 m))))) (\lambda (n: nat).(\lambda (c: C).(\lambda (d: C).(\lambda (u: 
T).(\lambda (H0: (getl n c (CHead d (Bind Abbr) u))).(\lambda (t: T).(\lambda 
(H1: (ty3 g d u t)).(\lambda (H2: ((\forall (c2: C).((wf3 g d c2) \to (ty3 g 
c2 u t))))).(\lambda (c2: C).(\lambda (H3: (wf3 g c c2)).(let H_x \def 
(wf3_getl_conf Abbr n c d u H0 g c2 H3 t H1) in (let H4 \def H_x in (ex2_ind 
C (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: 
C).(wf3 g d d2)) (ty3 g c2 (TLRef n) (lift (S n) O t)) (\lambda (x: 
C).(\lambda (H5: (getl n c2 (CHead x (Bind Abbr) u))).(\lambda (H6: (wf3 g d 
x)).(ty3_abbr g n c2 x u H5 t (H2 x H6))))) H4))))))))))))) (\lambda (n: 
nat).(\lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (H0: (getl n c 
(CHead d (Bind Abst) u))).(\lambda (t: T).(\lambda (H1: (ty3 g d u 
t)).(\lambda (H2: ((\forall (c2: C).((wf3 g d c2) \to (ty3 g c2 u 
t))))).(\lambda (c2: C).(\lambda (H3: (wf3 g c c2)).(let H_x \def 
(wf3_getl_conf Abst n c d u H0 g c2 H3 t H1) in (let H4 \def H_x in (ex2_ind 
C (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(wf3 g d d2)) (ty3 g c2 (TLRef n) (lift (S n) O u)) (\lambda (x: 
C).(\lambda (H5: (getl n c2 (CHead x (Bind Abst) u))).(\lambda (H6: (wf3 g d 
x)).(ty3_abst g n c2 x u H5 t (H2 x H6))))) H4))))))))))))) (\lambda (c: 
C).(\lambda (u: T).(\lambda (t: T).(\lambda (H0: (ty3 g c u t)).(\lambda (H1: 
((\forall (c2: C).((wf3 g c c2) \to (ty3 g c2 u t))))).(\lambda (b: 
B).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (ty3 g (CHead c (Bind b) u) 
t3 t4)).(\lambda (H3: ((\forall (c2: C).((wf3 g (CHead c (Bind b) u) c2) \to 
(ty3 g c2 t3 t4))))).(\lambda (c2: C).(\lambda (H4: (wf3 g c c2)).(ty3_bind g 
c2 u t (H1 c2 H4) b t3 t4 (H3 (CHead c2 (Bind b) u) (wf3_bind g c c2 H4 u t 
H0 b))))))))))))))) (\lambda (c: C).(\lambda (w: T).(\lambda (u: T).(\lambda 
(_: (ty3 g c w u)).(\lambda (H1: ((\forall (c2: C).((wf3 g c c2) \to (ty3 g 
c2 w u))))).(\lambda (v: T).(\lambda (t: T).(\lambda (_: (ty3 g c v (THead 
(Bind Abst) u t))).(\lambda (H3: ((\forall (c2: C).((wf3 g c c2) \to (ty3 g 
c2 v (THead (Bind Abst) u t)))))).(\lambda (c2: C).(\lambda (H4: (wf3 g c 
c2)).(ty3_appl g c2 w u (H1 c2 H4) v t (H3 c2 H4))))))))))))) (\lambda (c: 
C).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (ty3 g c t3 t4)).(\lambda 
(H1: ((\forall (c2: C).((wf3 g c c2) \to (ty3 g c2 t3 t4))))).(\lambda (t0: 
T).(\lambda (_: (ty3 g c t4 t0)).(\lambda (H3: ((\forall (c2: C).((wf3 g c 
c2) \to (ty3 g c2 t4 t0))))).(\lambda (c2: C).(\lambda (H4: (wf3 g c 
c2)).(ty3_cast g c2 t3 t4 (H1 c2 H4) t0 (H3 c2 H4)))))))))))) c1 t1 t2 H))))).
(* COMMENTS
Initial nodes: 1027
END *)

