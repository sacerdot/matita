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

include "basic_1/nf2/props.ma".

include "basic_1/drop1/fwd.ma".

theorem nf2_lift1:
 \forall (e: C).(\forall (hds: PList).(\forall (c: C).(\forall (t: T).((drop1 
hds c e) \to ((nf2 e t) \to (nf2 c (lift1 hds t)))))))
\def
 \lambda (e: C).(\lambda (hds: PList).(let TMP_2 \def (\lambda (p: 
PList).(\forall (c: C).(\forall (t: T).((drop1 p c e) \to ((nf2 e t) \to (let 
TMP_1 \def (lift1 p t) in (nf2 c TMP_1))))))) in (let TMP_4 \def (\lambda (c: 
C).(\lambda (t: T).(\lambda (H: (drop1 PNil c e)).(\lambda (H0: (nf2 e 
t)).(let H_y \def (drop1_gen_pnil c e H) in (let TMP_3 \def (\lambda (c0: 
C).(nf2 c0 t)) in (eq_ind_r C e TMP_3 H0 c H_y))))))) in (let TMP_13 \def 
(\lambda (n: nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda (H: 
((\forall (c: C).(\forall (t: T).((drop1 p c e) \to ((nf2 e t) \to (nf2 c 
(lift1 p t)))))))).(\lambda (c: C).(\lambda (t: T).(\lambda (H0: (drop1 
(PCons n n0 p) c e)).(\lambda (H1: (nf2 e t)).(let H_x \def (drop1_gen_pcons 
c e p n n0 H0) in (let H2 \def H_x in (let TMP_5 \def (\lambda (c2: C).(drop 
n n0 c c2)) in (let TMP_6 \def (\lambda (c2: C).(drop1 p c2 e)) in (let TMP_7 
\def (lift1 p t) in (let TMP_8 \def (lift n n0 TMP_7) in (let TMP_9 \def (nf2 
c TMP_8) in (let TMP_12 \def (\lambda (x: C).(\lambda (H3: (drop n n0 c 
x)).(\lambda (H4: (drop1 p x e)).(let TMP_10 \def (lift1 p t) in (let TMP_11 
\def (H x t H4 H1) in (nf2_lift x TMP_10 TMP_11 c n n0 H3)))))) in (ex2_ind C 
TMP_5 TMP_6 TMP_9 TMP_12 H2))))))))))))))))) in (PList_ind TMP_2 TMP_4 TMP_13 
hds))))).

