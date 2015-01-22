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

include "Basic-1/ty3/arity.ma".

include "Basic-1/sc3/arity.ma".

theorem ty3_predicative:
 \forall (g: G).(\forall (c: C).(\forall (v: T).(\forall (t: T).(\forall (u: 
T).((ty3 g c (THead (Bind Abst) v t) u) \to ((pc3 c u v) \to (\forall (P: 
Prop).P)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (v: T).(\lambda (t: T).(\lambda (u: 
T).(\lambda (H: (ty3 g c (THead (Bind Abst) v t) u)).(\lambda (H0: (pc3 c u 
v)).(\lambda (P: Prop).(let H1 \def H in (ex3_2_ind T T (\lambda (t2: 
T).(\lambda (_: T).(pc3 c (THead (Bind Abst) v t2) u))) (\lambda (_: 
T).(\lambda (t0: T).(ty3 g c v t0))) (\lambda (t2: T).(\lambda (_: T).(ty3 g 
(CHead c (Bind Abst) v) t t2))) P (\lambda (x0: T).(\lambda (x1: T).(\lambda 
(_: (pc3 c (THead (Bind Abst) v x0) u)).(\lambda (H3: (ty3 g c v 
x1)).(\lambda (_: (ty3 g (CHead c (Bind Abst) v) t x0)).(let H_y \def 
(ty3_conv g c v x1 H3 (THead (Bind Abst) v t) u H H0) in (let H_x \def 
(ty3_arity g c (THead (Bind Abst) v t) v H_y) in (let H5 \def H_x in (ex2_ind 
A (\lambda (a1: A).(arity g c (THead (Bind Abst) v t) a1)) (\lambda (a1: 
A).(arity g c v (asucc g a1))) P (\lambda (x: A).(\lambda (H6: (arity g c 
(THead (Bind Abst) v t) x)).(\lambda (H7: (arity g c v (asucc g x))).(let H8 
\def (arity_gen_abst g c v t x H6) in (ex3_2_ind A A (\lambda (a1: 
A).(\lambda (a2: A).(eq A x (AHead a1 a2)))) (\lambda (a1: A).(\lambda (_: 
A).(arity g c v (asucc g a1)))) (\lambda (_: A).(\lambda (a2: A).(arity g 
(CHead c (Bind Abst) v) t a2))) P (\lambda (x2: A).(\lambda (x3: A).(\lambda 
(H9: (eq A x (AHead x2 x3))).(\lambda (H10: (arity g c v (asucc g 
x2))).(\lambda (_: (arity g (CHead c (Bind Abst) v) t x3)).(let H12 \def 
(eq_ind A x (\lambda (a: A).(arity g c v (asucc g a))) H7 (AHead x2 x3) H9) 
in (leq_ahead_asucc_false g x2 (asucc g x3) (arity_mono g c v (asucc g (AHead 
x2 x3)) H12 (asucc g x2) H10) P))))))) H8))))) H5))))))))) (ty3_gen_bind g 
Abst c v t u H1)))))))))).
(* COMMENTS
Initial nodes: 497
END *)

theorem ty3_repellent:
 \forall (g: G).(\forall (c: C).(\forall (w: T).(\forall (t: T).(\forall (u1: 
T).((ty3 g c (THead (Bind Abst) w t) u1) \to (\forall (u2: T).((ty3 g (CHead 
c (Bind Abst) w) t (lift (S O) O u2)) \to ((pc3 c u1 u2) \to (\forall (P: 
Prop).P)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (w: T).(\lambda (t: T).(\lambda (u1: 
T).(\lambda (H: (ty3 g c (THead (Bind Abst) w t) u1)).(\lambda (u2: 
T).(\lambda (H0: (ty3 g (CHead c (Bind Abst) w) t (lift (S O) O 
u2))).(\lambda (H1: (pc3 c u1 u2)).(\lambda (P: Prop).(ex_ind T (\lambda (t0: 
T).(ty3 g (CHead c (Bind Abst) w) (lift (S O) O u2) t0)) P (\lambda (x: 
T).(\lambda (H2: (ty3 g (CHead c (Bind Abst) w) (lift (S O) O u2) x)).(let H3 
\def (ty3_gen_lift g (CHead c (Bind Abst) w) u2 x (S O) O H2 c (drop_drop 
(Bind Abst) O c c (drop_refl c) w)) in (ex2_ind T (\lambda (t2: T).(pc3 
(CHead c (Bind Abst) w) (lift (S O) O t2) x)) (\lambda (t2: T).(ty3 g c u2 
t2)) P (\lambda (x0: T).(\lambda (_: (pc3 (CHead c (Bind Abst) w) (lift (S O) 
O x0) x)).(\lambda (H5: (ty3 g c u2 x0)).(let H_y \def (ty3_conv g c u2 x0 H5 
(THead (Bind Abst) w t) u1 H H1) in (let H_x \def (ty3_arity g (CHead c (Bind 
Abst) w) t (lift (S O) O u2) H0) in (let H6 \def H_x in (ex2_ind A (\lambda 
(a1: A).(arity g (CHead c (Bind Abst) w) t a1)) (\lambda (a1: A).(arity g 
(CHead c (Bind Abst) w) (lift (S O) O u2) (asucc g a1))) P (\lambda (x1: 
A).(\lambda (H7: (arity g (CHead c (Bind Abst) w) t x1)).(\lambda (H8: (arity 
g (CHead c (Bind Abst) w) (lift (S O) O u2) (asucc g x1))).(let H_x0 \def 
(ty3_arity g c (THead (Bind Abst) w t) u2 H_y) in (let H9 \def H_x0 in 
(ex2_ind A (\lambda (a1: A).(arity g c (THead (Bind Abst) w t) a1)) (\lambda 
(a1: A).(arity g c u2 (asucc g a1))) P (\lambda (x2: A).(\lambda (H10: (arity 
g c (THead (Bind Abst) w t) x2)).(\lambda (H11: (arity g c u2 (asucc g 
x2))).(arity_repellent g c w t x1 H7 x2 H10 (asucc_inj g x1 x2 (arity_mono g 
c u2 (asucc g x1) (arity_gen_lift g (CHead c (Bind Abst) w) u2 (asucc g x1) 
(S O) O H8 c (drop_drop (Bind Abst) O c c (drop_refl c) w)) (asucc g x2) 
H11)) P)))) H9)))))) H6))))))) H3)))) (ty3_correct g (CHead c (Bind Abst) w) 
t (lift (S O) O u2) H0))))))))))).
(* COMMENTS
Initial nodes: 651
END *)

theorem ty3_acyclic:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (u: T).((ty3 g c t 
u) \to ((pc3 c u t) \to (\forall (P: Prop).P))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (u: T).(\lambda (H: 
(ty3 g c t u)).(\lambda (H0: (pc3 c u t)).(\lambda (P: Prop).(let H_y \def 
(ty3_conv g c t u H t u H H0) in (let H_x \def (ty3_arity g c t t H_y) in 
(let H1 \def H_x in (ex2_ind A (\lambda (a1: A).(arity g c t a1)) (\lambda 
(a1: A).(arity g c t (asucc g a1))) P (\lambda (x: A).(\lambda (H2: (arity g 
c t x)).(\lambda (H3: (arity g c t (asucc g x))).(leq_asucc_false g x 
(arity_mono g c t (asucc g x) H3 x H2) P)))) H1)))))))))).
(* COMMENTS
Initial nodes: 151
END *)

theorem ty3_sn3:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (u: T).((ty3 g c t 
u) \to (sn3 c t)))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (u: T).(\lambda (H: 
(ty3 g c t u)).(let H_x \def (ty3_arity g c t u H) in (let H0 \def H_x in 
(ex2_ind A (\lambda (a1: A).(arity g c t a1)) (\lambda (a1: A).(arity g c u 
(asucc g a1))) (sn3 c t) (\lambda (x: A).(\lambda (H1: (arity g c t 
x)).(\lambda (_: (arity g c u (asucc g x))).(sc3_sn3 g x c t (sc3_arity g c t 
x H1))))) H0))))))).
(* COMMENTS
Initial nodes: 119
END *)

