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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/ty3/arity_props".

include "ty3/arity.ma".

include "ty3/fwd.ma".

include "sc3/arity.ma".

theorem ty3_predicative:
 \forall (g: G).(\forall (c: C).(\forall (v: T).(\forall (t: T).(\forall (u: 
T).((ty3 g c (THead (Bind Abst) v t) u) \to ((pc3 c u v) \to (\forall (P: 
Prop).P)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (v: T).(\lambda (t: T).(\lambda (u: 
T).(\lambda (H: (ty3 g c (THead (Bind Abst) v t) u)).(\lambda (H0: (pc3 c u 
v)).(\lambda (P: Prop).(let H1 \def H in (ex4_3_ind T T T (\lambda (t2: 
T).(\lambda (_: T).(\lambda (_: T).(pc3 c (THead (Bind Abst) v t2) u)))) 
(\lambda (_: T).(\lambda (t0: T).(\lambda (_: T).(ty3 g c v t0)))) (\lambda 
(t2: T).(\lambda (_: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) v) t 
t2)))) (\lambda (t2: T).(\lambda (_: T).(\lambda (t1: T).(ty3 g (CHead c 
(Bind Abst) v) t2 t1)))) P (\lambda (x0: T).(\lambda (x1: T).(\lambda (x2: 
T).(\lambda (_: (pc3 c (THead (Bind Abst) v x0) u)).(\lambda (H3: (ty3 g c v 
x1)).(\lambda (_: (ty3 g (CHead c (Bind Abst) v) t x0)).(\lambda (_: (ty3 g 
(CHead c (Bind Abst) v) x0 x2)).(let H_y \def (ty3_conv g c v x1 H3 (THead 
(Bind Abst) v t) u H H0) in (let H_x \def (ty3_arity g c (THead (Bind Abst) v 
t) v H_y) in (let H6 \def H_x in (ex2_ind A (\lambda (a1: A).(arity g c 
(THead (Bind Abst) v t) a1)) (\lambda (a1: A).(arity g c v (asucc g a1))) P 
(\lambda (x: A).(\lambda (H7: (arity g c (THead (Bind Abst) v t) x)).(\lambda 
(H8: (arity g c v (asucc g x))).(let H9 \def (arity_gen_abst g c v t x H7) in 
(ex3_2_ind A A (\lambda (a1: A).(\lambda (a2: A).(eq A x (AHead a1 a2)))) 
(\lambda (a1: A).(\lambda (_: A).(arity g c v (asucc g a1)))) (\lambda (_: 
A).(\lambda (a2: A).(arity g (CHead c (Bind Abst) v) t a2))) P (\lambda (x3: 
A).(\lambda (x4: A).(\lambda (H10: (eq A x (AHead x3 x4))).(\lambda (H11: 
(arity g c v (asucc g x3))).(\lambda (_: (arity g (CHead c (Bind Abst) v) t 
x4)).(let H13 \def (eq_ind A x (\lambda (a: A).(arity g c v (asucc g a))) H8 
(AHead x3 x4) H10) in (leq_ahead_asucc_false g x3 (asucc g x4) (arity_mono g 
c v (asucc g (AHead x3 x4)) H13 (asucc g x3) H11) P))))))) H9))))) 
H6))))))))))) (ty3_gen_bind g Abst c v t u H1)))))))))).

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

