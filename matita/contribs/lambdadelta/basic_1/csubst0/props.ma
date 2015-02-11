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

include "basic_1/csubst0/defs.ma".

theorem csubst0_snd_bind:
 \forall (b: B).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall 
(u2: T).((subst0 i v u1 u2) \to (\forall (c: C).(csubst0 (S i) v (CHead c 
(Bind b) u1) (CHead c (Bind b) u2))))))))
\def
 \lambda (b: B).(\lambda (i: nat).(\lambda (v: T).(\lambda (u1: T).(\lambda 
(u2: T).(\lambda (H: (subst0 i v u1 u2)).(\lambda (c: C).(let TMP_1 \def 
(Bind b) in (let TMP_2 \def (s TMP_1 i) in (let TMP_7 \def (\lambda (n: 
nat).(let TMP_3 \def (Bind b) in (let TMP_4 \def (CHead c TMP_3 u1) in (let 
TMP_5 \def (Bind b) in (let TMP_6 \def (CHead c TMP_5 u2) in (csubst0 n v 
TMP_4 TMP_6)))))) in (let TMP_8 \def (Bind b) in (let TMP_9 \def (csubst0_snd 
TMP_8 i v u1 u2 H c) in (let TMP_10 \def (S i) in (let TMP_11 \def (S i) in 
(let TMP_12 \def (refl_equal nat TMP_11) in (eq_ind nat TMP_2 TMP_7 TMP_9 
TMP_10 TMP_12))))))))))))))).

theorem csubst0_fst_bind:
 \forall (b: B).(\forall (i: nat).(\forall (c1: C).(\forall (c2: C).(\forall 
(v: T).((csubst0 i v c1 c2) \to (\forall (u: T).(csubst0 (S i) v (CHead c1 
(Bind b) u) (CHead c2 (Bind b) u))))))))
\def
 \lambda (b: B).(\lambda (i: nat).(\lambda (c1: C).(\lambda (c2: C).(\lambda 
(v: T).(\lambda (H: (csubst0 i v c1 c2)).(\lambda (u: T).(let TMP_1 \def 
(Bind b) in (let TMP_2 \def (s TMP_1 i) in (let TMP_7 \def (\lambda (n: 
nat).(let TMP_3 \def (Bind b) in (let TMP_4 \def (CHead c1 TMP_3 u) in (let 
TMP_5 \def (Bind b) in (let TMP_6 \def (CHead c2 TMP_5 u) in (csubst0 n v 
TMP_4 TMP_6)))))) in (let TMP_8 \def (Bind b) in (let TMP_9 \def (csubst0_fst 
TMP_8 i c1 c2 v H u) in (let TMP_10 \def (S i) in (let TMP_11 \def (S i) in 
(let TMP_12 \def (refl_equal nat TMP_11) in (eq_ind nat TMP_2 TMP_7 TMP_9 
TMP_10 TMP_12))))))))))))))).

theorem csubst0_both_bind:
 \forall (b: B).(\forall (i: nat).(\forall (v: T).(\forall (u1: T).(\forall 
(u2: T).((subst0 i v u1 u2) \to (\forall (c1: C).(\forall (c2: C).((csubst0 i 
v c1 c2) \to (csubst0 (S i) v (CHead c1 (Bind b) u1) (CHead c2 (Bind b) 
u2))))))))))
\def
 \lambda (b: B).(\lambda (i: nat).(\lambda (v: T).(\lambda (u1: T).(\lambda 
(u2: T).(\lambda (H: (subst0 i v u1 u2)).(\lambda (c1: C).(\lambda (c2: 
C).(\lambda (H0: (csubst0 i v c1 c2)).(let TMP_1 \def (Bind b) in (let TMP_2 
\def (s TMP_1 i) in (let TMP_7 \def (\lambda (n: nat).(let TMP_3 \def (Bind 
b) in (let TMP_4 \def (CHead c1 TMP_3 u1) in (let TMP_5 \def (Bind b) in (let 
TMP_6 \def (CHead c2 TMP_5 u2) in (csubst0 n v TMP_4 TMP_6)))))) in (let 
TMP_8 \def (Bind b) in (let TMP_9 \def (csubst0_both TMP_8 i v u1 u2 H c1 c2 
H0) in (let TMP_10 \def (S i) in (let TMP_11 \def (S i) in (let TMP_12 \def 
(refl_equal nat TMP_11) in (eq_ind nat TMP_2 TMP_7 TMP_9 TMP_10 
TMP_12))))))))))))))))).

