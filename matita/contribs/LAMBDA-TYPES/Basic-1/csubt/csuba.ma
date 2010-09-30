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

theorem csubt_csuba:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((csubt g c1 c2) \to (csuba 
g c1 c2))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubt g c1 
c2)).(csubt_ind g (\lambda (c: C).(\lambda (c0: C).(csuba g c c0))) (\lambda 
(n: nat).(csuba_refl g (CSort n))) (\lambda (c3: C).(\lambda (c4: C).(\lambda 
(_: (csubt g c3 c4)).(\lambda (H1: (csuba g c3 c4)).(\lambda (k: K).(\lambda 
(u: T).(csuba_head g c3 c4 H1 k u))))))) (\lambda (c3: C).(\lambda (c4: 
C).(\lambda (_: (csubt g c3 c4)).(\lambda (H1: (csuba g c3 c4)).(\lambda (b: 
B).(\lambda (H2: (not (eq B b Void))).(\lambda (u1: T).(\lambda (u2: 
T).(csuba_void g c3 c4 H1 b H2 u1 u2))))))))) (\lambda (c3: C).(\lambda (c4: 
C).(\lambda (_: (csubt g c3 c4)).(\lambda (H1: (csuba g c3 c4)).(\lambda (u: 
T).(\lambda (t: T).(\lambda (H2: (ty3 g c3 u t)).(\lambda (_: (ty3 g c4 u 
t)).(let H_x \def (ty3_arity g c3 u t H2) in (let H4 \def H_x in (ex2_ind A 
(\lambda (a1: A).(arity g c3 u a1)) (\lambda (a1: A).(arity g c3 t (asucc g 
a1))) (csuba g (CHead c3 (Bind Abst) t) (CHead c4 (Bind Abbr) u)) (\lambda 
(x: A).(\lambda (H5: (arity g c3 u x)).(\lambda (H6: (arity g c3 t (asucc g 
x))).(csuba_abst g c3 c4 H1 t x H6 u (csuba_arity g c3 u x H5 c4 H1))))) 
H4))))))))))) c1 c2 H)))).
(* COMMENTS
Initial nodes: 313
END *)

