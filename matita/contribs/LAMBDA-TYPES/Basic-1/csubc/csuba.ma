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

include "Basic-1/csubc/defs.ma".

include "Basic-1/sc3/props.ma".

theorem csubc_csuba:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((csubc g c1 c2) \to (csuba 
g c1 c2))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubc g c1 
c2)).(csubc_ind g (\lambda (c: C).(\lambda (c0: C).(csuba g c c0))) (\lambda 
(n: nat).(csuba_refl g (CSort n))) (\lambda (c3: C).(\lambda (c4: C).(\lambda 
(_: (csubc g c3 c4)).(\lambda (H1: (csuba g c3 c4)).(\lambda (k: K).(\lambda 
(v: T).(csuba_head g c3 c4 H1 k v))))))) (\lambda (c3: C).(\lambda (c4: 
C).(\lambda (_: (csubc g c3 c4)).(\lambda (H1: (csuba g c3 c4)).(\lambda (b: 
B).(\lambda (H2: (not (eq B b Void))).(\lambda (u1: T).(\lambda (u2: 
T).(csuba_void g c3 c4 H1 b H2 u1 u2))))))))) (\lambda (c3: C).(\lambda (c4: 
C).(\lambda (_: (csubc g c3 c4)).(\lambda (H1: (csuba g c3 c4)).(\lambda (v: 
T).(\lambda (a: A).(\lambda (H2: (sc3 g (asucc g a) c3 v)).(\lambda (w: 
T).(\lambda (H3: (sc3 g a c4 w)).(csuba_abst g c3 c4 H1 v a (sc3_arity_gen g 
c3 v (asucc g a) H2) w (sc3_arity_gen g c4 w a H3))))))))))) c1 c2 H)))).
(* COMMENTS
Initial nodes: 231
END *)

