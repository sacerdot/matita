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

include "basic_1/csubst1/fwd.ma".

include "basic_1/subst1/fwd.ma".

theorem csubst1_head:
 \forall (k: K).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall 
(u2: T).((subst1 i v u1 u2) \to (\forall (c1: C).(\forall (c2: C).((csubst1 i 
v c1 c2) \to (csubst1 (s k i) v (CHead c1 k u1) (CHead c2 k u2))))))))))
\def
 \lambda (k: K).(\lambda (i: nat).(\lambda (v: T).(\lambda (u1: T).(\lambda 
(u2: T).(\lambda (H: (subst1 i v u1 u2)).(let TMP_4 \def (\lambda (t: 
T).(\forall (c1: C).(\forall (c2: C).((csubst1 i v c1 c2) \to (let TMP_1 \def 
(s k i) in (let TMP_2 \def (CHead c1 k u1) in (let TMP_3 \def (CHead c2 k t) 
in (csubst1 TMP_1 v TMP_2 TMP_3)))))))) in (let TMP_17 \def (\lambda (c1: 
C).(\lambda (c2: C).(\lambda (H0: (csubst1 i v c1 c2)).(let TMP_8 \def 
(\lambda (c: C).(let TMP_5 \def (s k i) in (let TMP_6 \def (CHead c1 k u1) in 
(let TMP_7 \def (CHead c k u1) in (csubst1 TMP_5 v TMP_6 TMP_7))))) in (let 
TMP_9 \def (s k i) in (let TMP_10 \def (CHead c1 k u1) in (let TMP_11 \def 
(csubst1_refl TMP_9 v TMP_10) in (let TMP_16 \def (\lambda (c3: C).(\lambda 
(H1: (csubst0 i v c1 c3)).(let TMP_12 \def (s k i) in (let TMP_13 \def (CHead 
c1 k u1) in (let TMP_14 \def (CHead c3 k u1) in (let TMP_15 \def (csubst0_fst 
k i c1 c3 v H1 u1) in (csubst1_sing TMP_12 v TMP_13 TMP_14 TMP_15))))))) in 
(csubst1_ind i v c1 TMP_8 TMP_11 TMP_16 c2 H0))))))))) in (let TMP_32 \def 
(\lambda (t2: T).(\lambda (H0: (subst0 i v u1 t2)).(\lambda (c1: C).(\lambda 
(c2: C).(\lambda (H1: (csubst1 i v c1 c2)).(let TMP_21 \def (\lambda (c: 
C).(let TMP_18 \def (s k i) in (let TMP_19 \def (CHead c1 k u1) in (let 
TMP_20 \def (CHead c k t2) in (csubst1 TMP_18 v TMP_19 TMP_20))))) in (let 
TMP_22 \def (s k i) in (let TMP_23 \def (CHead c1 k u1) in (let TMP_24 \def 
(CHead c1 k t2) in (let TMP_25 \def (csubst0_snd k i v u1 t2 H0 c1) in (let 
TMP_26 \def (csubst1_sing TMP_22 v TMP_23 TMP_24 TMP_25) in (let TMP_31 \def 
(\lambda (c3: C).(\lambda (H2: (csubst0 i v c1 c3)).(let TMP_27 \def (s k i) 
in (let TMP_28 \def (CHead c1 k u1) in (let TMP_29 \def (CHead c3 k t2) in 
(let TMP_30 \def (csubst0_both k i v u1 t2 H0 c1 c3 H2) in (csubst1_sing 
TMP_27 v TMP_28 TMP_29 TMP_30))))))) in (csubst1_ind i v c1 TMP_21 TMP_26 
TMP_31 c2 H1))))))))))))) in (subst1_ind i v u1 TMP_4 TMP_17 TMP_32 u2 
H))))))))).

theorem csubst1_bind:
 \forall (b: B).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall 
(u2: T).((subst1 i v u1 u2) \to (\forall (c1: C).(\forall (c2: C).((csubst1 i 
v c1 c2) \to (csubst1 (S i) v (CHead c1 (Bind b) u1) (CHead c2 (Bind b) 
u2))))))))))
\def
 \lambda (b: B).(\lambda (i: nat).(\lambda (v: T).(\lambda (u1: T).(\lambda 
(u2: T).(\lambda (H: (subst1 i v u1 u2)).(\lambda (c1: C).(\lambda (c2: 
C).(\lambda (H0: (csubst1 i v c1 c2)).(let TMP_1 \def (Bind b) in (let TMP_2 
\def (s TMP_1 i) in (let TMP_7 \def (\lambda (n: nat).(let TMP_3 \def (Bind 
b) in (let TMP_4 \def (CHead c1 TMP_3 u1) in (let TMP_5 \def (Bind b) in (let 
TMP_6 \def (CHead c2 TMP_5 u2) in (csubst1 n v TMP_4 TMP_6)))))) in (let 
TMP_8 \def (Bind b) in (let TMP_9 \def (csubst1_head TMP_8 i v u1 u2 H c1 c2 
H0) in (let TMP_10 \def (S i) in (let TMP_11 \def (S i) in (let TMP_12 \def 
(refl_equal nat TMP_11) in (eq_ind nat TMP_2 TMP_7 TMP_9 TMP_10 
TMP_12))))))))))))))))).

theorem csubst1_flat:
 \forall (f: F).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall 
(u2: T).((subst1 i v u1 u2) \to (\forall (c1: C).(\forall (c2: C).((csubst1 i 
v c1 c2) \to (csubst1 i v (CHead c1 (Flat f) u1) (CHead c2 (Flat f) 
u2))))))))))
\def
 \lambda (f: F).(\lambda (i: nat).(\lambda (v: T).(\lambda (u1: T).(\lambda 
(u2: T).(\lambda (H: (subst1 i v u1 u2)).(\lambda (c1: C).(\lambda (c2: 
C).(\lambda (H0: (csubst1 i v c1 c2)).(let TMP_1 \def (Flat f) in (let TMP_2 
\def (s TMP_1 i) in (let TMP_7 \def (\lambda (n: nat).(let TMP_3 \def (Flat 
f) in (let TMP_4 \def (CHead c1 TMP_3 u1) in (let TMP_5 \def (Flat f) in (let 
TMP_6 \def (CHead c2 TMP_5 u2) in (csubst1 n v TMP_4 TMP_6)))))) in (let 
TMP_8 \def (Flat f) in (let TMP_9 \def (csubst1_head TMP_8 i v u1 u2 H c1 c2 
H0) in (let TMP_10 \def (refl_equal nat i) in (eq_ind nat TMP_2 TMP_7 TMP_9 i 
TMP_10))))))))))))))).

