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

include "basic_1/sn3/props.ma".

include "basic_1/drop1/fwd.ma".

include "basic_1/lift1/props.ma".

theorem sns3_lifts1:
 \forall (e: C).(\forall (hds: PList).(\forall (c: C).((drop1 hds c e) \to 
(\forall (ts: TList).((sns3 e ts) \to (sns3 c (lifts1 hds ts)))))))
\def
 \lambda (e: C).(\lambda (hds: PList).(let TMP_2 \def (\lambda (p: 
PList).(\forall (c: C).((drop1 p c e) \to (\forall (ts: TList).((sns3 e ts) 
\to (let TMP_1 \def (lifts1 p ts) in (sns3 c TMP_1))))))) in (let TMP_9 \def 
(\lambda (c: C).(\lambda (H: (drop1 PNil c e)).(\lambda (ts: TList).(\lambda 
(H0: (sns3 e ts)).(let H_y \def (drop1_gen_pnil c e H) in (let TMP_4 \def 
(\lambda (c0: C).(let TMP_3 \def (lifts1 PNil ts) in (sns3 c0 TMP_3))) in 
(let TMP_5 \def (\lambda (t: TList).(sns3 e t)) in (let TMP_6 \def (lifts1 
PNil ts) in (let TMP_7 \def (lifts1_nil ts) in (let TMP_8 \def (eq_ind_r 
TList ts TMP_5 H0 TMP_6 TMP_7) in (eq_ind_r C e TMP_4 TMP_8 c H_y))))))))))) 
in (let TMP_25 \def (\lambda (n: nat).(\lambda (n0: nat).(\lambda (p: 
PList).(\lambda (H: ((\forall (c: C).((drop1 p c e) \to (\forall (ts: 
TList).((sns3 e ts) \to (sns3 c (lifts1 p ts)))))))).(\lambda (c: C).(\lambda 
(H0: (drop1 (PCons n n0 p) c e)).(\lambda (ts: TList).(\lambda (H1: (sns3 e 
ts)).(let H_x \def (drop1_gen_pcons c e p n n0 H0) in (let H2 \def H_x in 
(let TMP_10 \def (\lambda (c2: C).(drop n n0 c c2)) in (let TMP_11 \def 
(\lambda (c2: C).(drop1 p c2 e)) in (let TMP_12 \def (PCons n n0 p) in (let 
TMP_13 \def (lifts1 TMP_12 ts) in (let TMP_14 \def (sns3 c TMP_13) in (let 
TMP_24 \def (\lambda (x: C).(\lambda (H3: (drop n n0 c x)).(\lambda (H4: 
(drop1 p x e)).(let TMP_15 \def (lifts1 p ts) in (let TMP_16 \def (lifts n n0 
TMP_15) in (let TMP_17 \def (\lambda (t: TList).(sns3 c t)) in (let TMP_18 
\def (lifts1 p ts) in (let TMP_19 \def (H x H4 ts H1) in (let TMP_20 \def 
(sns3_lifts c x n n0 H3 TMP_18 TMP_19) in (let TMP_21 \def (PCons n n0 p) in 
(let TMP_22 \def (lifts1 TMP_21 ts) in (let TMP_23 \def (lifts1_cons n n0 p 
ts) in (eq_ind_r TList TMP_16 TMP_17 TMP_20 TMP_22 TMP_23))))))))))))) in 
(ex2_ind C TMP_10 TMP_11 TMP_14 TMP_24 H2))))))))))))))))) in (PList_ind 
TMP_2 TMP_9 TMP_25 hds))))).

