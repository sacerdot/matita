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

include "basic_1/csubc/fwd.ma".

include "basic_1/sc3/props.ma".

theorem csubc_csuba:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((csubc g c1 c2) \to (csuba 
g c1 c2))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubc g c1 
c2)).(let TMP_1 \def (\lambda (c: C).(\lambda (c0: C).(csuba g c c0))) in 
(let TMP_3 \def (\lambda (n: nat).(let TMP_2 \def (CSort n) in (csuba_refl g 
TMP_2))) in (let TMP_4 \def (\lambda (c3: C).(\lambda (c4: C).(\lambda (_: 
(csubc g c3 c4)).(\lambda (H1: (csuba g c3 c4)).(\lambda (k: K).(\lambda (v: 
T).(csuba_head g c3 c4 H1 k v))))))) in (let TMP_5 \def (\lambda (c3: 
C).(\lambda (c4: C).(\lambda (_: (csubc g c3 c4)).(\lambda (H1: (csuba g c3 
c4)).(\lambda (b: B).(\lambda (H2: (not (eq B b Void))).(\lambda (u1: 
T).(\lambda (u2: T).(csuba_void g c3 c4 H1 b H2 u1 u2))))))))) in (let TMP_9 
\def (\lambda (c3: C).(\lambda (c4: C).(\lambda (_: (csubc g c3 c4)).(\lambda 
(H1: (csuba g c3 c4)).(\lambda (v: T).(\lambda (a: A).(\lambda (H2: (sc3 g 
(asucc g a) c3 v)).(\lambda (w: T).(\lambda (H3: (sc3 g a c4 w)).(let TMP_6 
\def (asucc g a) in (let TMP_7 \def (sc3_arity_gen g c3 v TMP_6 H2) in (let 
TMP_8 \def (sc3_arity_gen g c4 w a H3) in (csuba_abst g c3 c4 H1 v a TMP_7 w 
TMP_8))))))))))))) in (csubc_ind g TMP_1 TMP_3 TMP_4 TMP_5 TMP_9 c1 c2 
H))))))))).

