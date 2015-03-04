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

include "basic_1/arity/props.ma".

include "basic_1/drop1/fwd.ma".

theorem arity_lift1:
 \forall (g: G).(\forall (a: A).(\forall (c2: C).(\forall (hds: 
PList).(\forall (c1: C).(\forall (t: T).((drop1 hds c1 c2) \to ((arity g c2 t 
a) \to (arity g c1 (lift1 hds t) a))))))))
\def
 \lambda (g: G).(\lambda (a: A).(\lambda (c2: C).(\lambda (hds: PList).(let 
TMP_2 \def (\lambda (p: PList).(\forall (c1: C).(\forall (t: T).((drop1 p c1 
c2) \to ((arity g c2 t a) \to (let TMP_1 \def (lift1 p t) in (arity g c1 
TMP_1 a))))))) in (let TMP_4 \def (\lambda (c1: C).(\lambda (t: T).(\lambda 
(H: (drop1 PNil c1 c2)).(\lambda (H0: (arity g c2 t a)).(let H_y \def 
(drop1_gen_pnil c1 c2 H) in (let TMP_3 \def (\lambda (c: C).(arity g c t a)) 
in (eq_ind_r C c2 TMP_3 H0 c1 H_y))))))) in (let TMP_13 \def (\lambda (n: 
nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda (H: ((\forall (c1: 
C).(\forall (t: T).((drop1 p c1 c2) \to ((arity g c2 t a) \to (arity g c1 
(lift1 p t) a))))))).(\lambda (c1: C).(\lambda (t: T).(\lambda (H0: (drop1 
(PCons n n0 p) c1 c2)).(\lambda (H1: (arity g c2 t a)).(let H_x \def 
(drop1_gen_pcons c1 c2 p n n0 H0) in (let H2 \def H_x in (let TMP_5 \def 
(\lambda (c3: C).(drop n n0 c1 c3)) in (let TMP_6 \def (\lambda (c3: 
C).(drop1 p c3 c2)) in (let TMP_7 \def (lift1 p t) in (let TMP_8 \def (lift n 
n0 TMP_7) in (let TMP_9 \def (arity g c1 TMP_8 a) in (let TMP_12 \def 
(\lambda (x: C).(\lambda (H3: (drop n n0 c1 x)).(\lambda (H4: (drop1 p x 
c2)).(let TMP_10 \def (lift1 p t) in (let TMP_11 \def (H x t H4 H1) in 
(arity_lift g x TMP_10 a TMP_11 c1 n n0 H3)))))) in (ex2_ind C TMP_5 TMP_6 
TMP_9 TMP_12 H2))))))))))))))))) in (PList_ind TMP_2 TMP_4 TMP_13 hds))))))).

