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

include "basic_1/getl/drop.ma".

include "basic_1/getl/clear.ma".

theorem getl_conf_le:
 \forall (i: nat).(\forall (a: C).(\forall (c: C).((getl i c a) \to (\forall 
(e: C).(\forall (h: nat).((getl h c e) \to ((le h i) \to (getl (minus i h) e 
a))))))))
\def
 \lambda (i: nat).(\lambda (a: C).(\lambda (c: C).(\lambda (H: (getl i c 
a)).(\lambda (e: C).(\lambda (h: nat).(\lambda (H0: (getl h c e)).(\lambda 
(H1: (le h i)).(let H2 \def (getl_gen_all c e h H0) in (let TMP_1 \def 
(\lambda (e0: C).(drop h O c e0)) in (let TMP_2 \def (\lambda (e0: C).(clear 
e0 e)) in (let TMP_3 \def (minus i h) in (let TMP_4 \def (getl TMP_3 e a) in 
(let TMP_7 \def (\lambda (x: C).(\lambda (H3: (drop h O c x)).(\lambda (H4: 
(clear x e)).(let TMP_5 \def (minus i h) in (let TMP_6 \def 
(getl_drop_conf_ge i a c H x h O H3 H1) in (getl_clear_conf TMP_5 x a TMP_6 e 
H4)))))) in (ex2_ind C TMP_1 TMP_2 TMP_4 TMP_7 H2)))))))))))))).

theorem getl_trans:
 \forall (i: nat).(\forall (c1: C).(\forall (c2: C).(\forall (h: nat).((getl 
h c1 c2) \to (\forall (e2: C).((getl i c2 e2) \to (getl (plus i h) c1 
e2)))))))
\def
 \lambda (i: nat).(\lambda (c1: C).(\lambda (c2: C).(\lambda (h: 
nat).(\lambda (H: (getl h c1 c2)).(\lambda (e2: C).(\lambda (H0: (getl i c2 
e2)).(let H1 \def (getl_gen_all c2 e2 i H0) in (let TMP_1 \def (\lambda (e: 
C).(drop i O c2 e)) in (let TMP_2 \def (\lambda (e: C).(clear e e2)) in (let 
TMP_3 \def (plus i h) in (let TMP_4 \def (getl TMP_3 c1 e2) in (let TMP_14 
\def (\lambda (x: C).(\lambda (H2: (drop i O c2 x)).(\lambda (H3: (clear x 
e2)).(let TMP_6 \def (\lambda (n: nat).((drop n O c2 x) \to (let TMP_5 \def 
(plus n h) in (getl TMP_5 c1 e2)))) in (let TMP_10 \def (\lambda (H4: (drop O 
O c2 x)).(let TMP_7 \def (\lambda (c: C).(clear c e2)) in (let TMP_8 \def 
(drop_gen_refl c2 x H4) in (let H5 \def (eq_ind_r C x TMP_7 H3 c2 TMP_8) in 
(let TMP_9 \def (plus O h) in (getl_clear_trans TMP_9 c1 c2 H e2 H5)))))) in 
(let TMP_13 \def (\lambda (i0: nat).(\lambda (_: (((drop i0 O c2 x) \to (getl 
(plus i0 h) c1 e2)))).(\lambda (H4: (drop (S i0) O c2 x)).(let H_y \def 
(getl_drop_trans c1 c2 h H x i0 H4) in (let TMP_11 \def (S i0) in (let TMP_12 
\def (plus TMP_11 h) in (getl_intro TMP_12 c1 e2 x H_y H3))))))) in (nat_ind 
TMP_6 TMP_10 TMP_13 i H2))))))) in (ex2_ind C TMP_1 TMP_2 TMP_4 TMP_14 
H1))))))))))))).

