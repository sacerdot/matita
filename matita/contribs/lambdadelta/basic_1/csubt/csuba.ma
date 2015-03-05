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

include "basic_1/ty3/arity.ma".

theorem csubt_csuba:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((csubt g c1 c2) \to (csuba 
g c1 c2))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubt g c1 
c2)).(let TMP_1 \def (\lambda (c: C).(\lambda (c0: C).(csuba g c c0))) in 
(let TMP_3 \def (\lambda (n: nat).(let TMP_2 \def (CSort n) in (csuba_refl g 
TMP_2))) in (let TMP_4 \def (\lambda (c3: C).(\lambda (c4: C).(\lambda (_: 
(csubt g c3 c4)).(\lambda (H1: (csuba g c3 c4)).(\lambda (k: K).(\lambda (u: 
T).(csuba_head g c3 c4 H1 k u))))))) in (let TMP_5 \def (\lambda (c3: 
C).(\lambda (c4: C).(\lambda (_: (csubt g c3 c4)).(\lambda (H1: (csuba g c3 
c4)).(\lambda (b: B).(\lambda (H2: (not (eq B b Void))).(\lambda (u1: 
T).(\lambda (u2: T).(csuba_void g c3 c4 H1 b H2 u1 u2))))))))) in (let TMP_16 
\def (\lambda (c3: C).(\lambda (c4: C).(\lambda (_: (csubt g c3 c4)).(\lambda 
(H1: (csuba g c3 c4)).(\lambda (u: T).(\lambda (t: T).(\lambda (H2: (ty3 g c3 
u t)).(\lambda (_: (ty3 g c4 u t)).(let H_x \def (ty3_arity g c3 u t H2) in 
(let H4 \def H_x in (let TMP_6 \def (\lambda (a1: A).(arity g c3 u a1)) in 
(let TMP_8 \def (\lambda (a1: A).(let TMP_7 \def (asucc g a1) in (arity g c3 
t TMP_7))) in (let TMP_9 \def (Bind Abst) in (let TMP_10 \def (CHead c3 TMP_9 
t) in (let TMP_11 \def (Bind Abbr) in (let TMP_12 \def (CHead c4 TMP_11 u) in 
(let TMP_13 \def (csuba g TMP_10 TMP_12) in (let TMP_15 \def (\lambda (x: 
A).(\lambda (H5: (arity g c3 u x)).(\lambda (H6: (arity g c3 t (asucc g 
x))).(let TMP_14 \def (csuba_arity g c3 u x H5 c4 H1) in (csuba_abst g c3 c4 
H1 t x H6 u TMP_14))))) in (ex2_ind A TMP_6 TMP_8 TMP_13 TMP_15 
H4))))))))))))))))))) in (csubt_ind g TMP_1 TMP_3 TMP_4 TMP_5 TMP_16 c1 c2 
H))))))))).

