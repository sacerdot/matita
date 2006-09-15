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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/csub3/ty3".

include "csub3/pc3.ma".

include "csub3/props.ma".

theorem csub3_ty3:
 \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c1 
t1 t2) \to (\forall (c2: C).((csub3 g c1 c2) \to (ty3 g c2 t1 t2)))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (ty3 g c1 t1 t2)).(ty3_ind g (\lambda (c: C).(\lambda (t: T).(\lambda 
(t0: T).(\forall (c2: C).((csub3 g c c2) \to (ty3 g c2 t t0)))))) (\lambda 
(c: C).(\lambda (t0: T).(\lambda (t: T).(\lambda (_: (ty3 g c t0 t)).(\lambda 
(H1: ((\forall (c2: C).((csub3 g c c2) \to (ty3 g c2 t0 t))))).(\lambda (u: 
T).(\lambda (t3: T).(\lambda (_: (ty3 g c u t3)).(\lambda (H3: ((\forall (c2: 
C).((csub3 g c c2) \to (ty3 g c2 u t3))))).(\lambda (H4: (pc3 c t3 
t0)).(\lambda (c2: C).(\lambda (H5: (csub3 g c c2)).(ty3_conv g c2 t0 t (H1 
c2 H5) u t3 (H3 c2 H5) (csub3_pc3 g c t3 t0 H4 c2 H5)))))))))))))) (\lambda 
(c: C).(\lambda (m: nat).(\lambda (c2: C).(\lambda (_: (csub3 g c 
c2)).(ty3_sort g c2 m))))) (\lambda (n: nat).(\lambda (c: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (H0: (getl n c (CHead d (Bind Abbr) u))).(\lambda 
(t: T).(\lambda (_: (ty3 g d u t)).(\lambda (H2: ((\forall (c2: C).((csub3 g 
d c2) \to (ty3 g c2 u t))))).(\lambda (c2: C).(\lambda (H3: (csub3 g c 
c2)).(let H4 \def (csub3_getl_abbr g c d u n H0 c2 H3) in (ex2_ind C (\lambda 
(d2: C).(csub3 g d d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) 
u))) (ty3 g c2 (TLRef n) (lift (S n) O t)) (\lambda (x: C).(\lambda (H5: 
(csub3 g d x)).(\lambda (H6: (getl n c2 (CHead x (Bind Abbr) u))).(ty3_abbr g 
n c2 x u H6 t (H2 x H5))))) H4)))))))))))) (\lambda (n: nat).(\lambda (c: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (H0: (getl n c (CHead d (Bind 
Abst) u))).(\lambda (t: T).(\lambda (_: (ty3 g d u t)).(\lambda (H2: 
((\forall (c2: C).((csub3 g d c2) \to (ty3 g c2 u t))))).(\lambda (c2: 
C).(\lambda (H3: (csub3 g c c2)).(let H4 \def (csub3_getl_abst g c d u n H0 
c2 H3) in (or_ind (ex2 C (\lambda (d2: C).(csub3 g d d2)) (\lambda (d2: 
C).(getl n c2 (CHead d2 (Bind Abst) u)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csub3 g d d2))) (\lambda (d2: C).(\lambda (u0: T).(getl n 
c2 (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 
u0 u)))) (ty3 g c2 (TLRef n) (lift (S n) O u)) (\lambda (H5: (ex2 C (\lambda 
(d2: C).(csub3 g d d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) 
u))))).(ex2_ind C (\lambda (d2: C).(csub3 g d d2)) (\lambda (d2: C).(getl n 
c2 (CHead d2 (Bind Abst) u))) (ty3 g c2 (TLRef n) (lift (S n) O u)) (\lambda 
(x: C).(\lambda (H6: (csub3 g d x)).(\lambda (H7: (getl n c2 (CHead x (Bind 
Abst) u))).(ty3_abst g n c2 x u H7 t (H2 x H6))))) H5)) (\lambda (H5: (ex3_2 
C T (\lambda (d2: C).(\lambda (_: T).(csub3 g d d2))) (\lambda (d2: 
C).(\lambda (u0: T).(getl n c2 (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: 
C).(\lambda (u0: T).(ty3 g d2 u0 u))))).(ex3_2_ind C T (\lambda (d2: 
C).(\lambda (_: T).(csub3 g d d2))) (\lambda (d2: C).(\lambda (u0: T).(getl n 
c2 (CHead d2 (Bind Abbr) u0)))) (\lambda (d2: C).(\lambda (u0: T).(ty3 g d2 
u0 u))) (ty3 g c2 (TLRef n) (lift (S n) O u)) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (_: (csub3 g d x0)).(\lambda (H7: (getl n c2 (CHead x0 (Bind 
Abbr) x1))).(\lambda (H8: (ty3 g x0 x1 u)).(ty3_abbr g n c2 x0 x1 H7 u 
H8)))))) H5)) H4)))))))))))) (\lambda (c: C).(\lambda (u: T).(\lambda (t: 
T).(\lambda (_: (ty3 g c u t)).(\lambda (H1: ((\forall (c2: C).((csub3 g c 
c2) \to (ty3 g c2 u t))))).(\lambda (b: B).(\lambda (t0: T).(\lambda (t3: 
T).(\lambda (_: (ty3 g (CHead c (Bind b) u) t0 t3)).(\lambda (H3: ((\forall 
(c2: C).((csub3 g (CHead c (Bind b) u) c2) \to (ty3 g c2 t0 t3))))).(\lambda 
(t4: T).(\lambda (_: (ty3 g (CHead c (Bind b) u) t3 t4)).(\lambda (H5: 
((\forall (c2: C).((csub3 g (CHead c (Bind b) u) c2) \to (ty3 g c2 t3 
t4))))).(\lambda (c2: C).(\lambda (H6: (csub3 g c c2)).(ty3_bind g c2 u t (H1 
c2 H6) b t0 t3 (H3 (CHead c2 (Bind b) u) (csub3_head g c c2 H6 (Bind b) u)) 
t4 (H5 (CHead c2 (Bind b) u) (csub3_head g c c2 H6 (Bind b) 
u)))))))))))))))))) (\lambda (c: C).(\lambda (w: T).(\lambda (u: T).(\lambda 
(_: (ty3 g c w u)).(\lambda (H1: ((\forall (c2: C).((csub3 g c c2) \to (ty3 g 
c2 w u))))).(\lambda (v: T).(\lambda (t: T).(\lambda (_: (ty3 g c v (THead 
(Bind Abst) u t))).(\lambda (H3: ((\forall (c2: C).((csub3 g c c2) \to (ty3 g 
c2 v (THead (Bind Abst) u t)))))).(\lambda (c2: C).(\lambda (H4: (csub3 g c 
c2)).(ty3_appl g c2 w u (H1 c2 H4) v t (H3 c2 H4))))))))))))) (\lambda (c: 
C).(\lambda (t0: T).(\lambda (t3: T).(\lambda (_: (ty3 g c t0 t3)).(\lambda 
(H1: ((\forall (c2: C).((csub3 g c c2) \to (ty3 g c2 t0 t3))))).(\lambda (t4: 
T).(\lambda (_: (ty3 g c t3 t4)).(\lambda (H3: ((\forall (c2: C).((csub3 g c 
c2) \to (ty3 g c2 t3 t4))))).(\lambda (c2: C).(\lambda (H4: (csub3 g c 
c2)).(ty3_cast g c2 t0 t3 (H1 c2 H4) t4 (H3 c2 H4)))))))))))) c1 t1 t2 H))))).

theorem csub3_ty3_ld:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (v: T).((ty3 g c u 
v) \to (\forall (t1: T).(\forall (t2: T).((ty3 g (CHead c (Bind Abst) v) t1 
t2) \to (ty3 g (CHead c (Bind Abbr) u) t1 t2))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (v: T).(\lambda (H: 
(ty3 g c u v)).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (ty3 g (CHead 
c (Bind Abst) v) t1 t2)).(csub3_ty3 g (CHead c (Bind Abst) v) t1 t2 H0 (CHead 
c (Bind Abbr) u) (csub3_abst g c c (csub3_refl g c) u v H))))))))).

