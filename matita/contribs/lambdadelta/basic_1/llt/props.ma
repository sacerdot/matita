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

include "basic_1/llt/defs.ma".

include "basic_1/leq/fwd.ma".

theorem lweight_repl:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (eq nat 
(lweight a1) (lweight a2)))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(let TMP_3 \def (\lambda (a: A).(\lambda (a0: A).(let TMP_1 \def 
(lweight a) in (let TMP_2 \def (lweight a0) in (eq nat TMP_1 TMP_2))))) in 
(let TMP_4 \def (\lambda (h1: nat).(\lambda (h2: nat).(\lambda (n1: 
nat).(\lambda (n2: nat).(\lambda (k: nat).(\lambda (_: (eq A (aplus g (ASort 
h1 n1) k) (aplus g (ASort h2 n2) k))).(refl_equal nat O))))))) in (let TMP_16 
\def (\lambda (a0: A).(\lambda (a3: A).(\lambda (_: (leq g a0 a3)).(\lambda 
(H1: (eq nat (lweight a0) (lweight a3))).(\lambda (a4: A).(\lambda (a5: 
A).(\lambda (_: (leq g a4 a5)).(\lambda (H3: (eq nat (lweight a4) (lweight 
a5))).(let TMP_5 \def (lweight a0) in (let TMP_6 \def (lweight a4) in (let 
TMP_7 \def (plus TMP_5 TMP_6) in (let TMP_8 \def (lweight a3) in (let TMP_9 
\def (lweight a5) in (let TMP_10 \def (plus TMP_8 TMP_9) in (let TMP_11 \def 
(lweight a0) in (let TMP_12 \def (lweight a3) in (let TMP_13 \def (lweight 
a4) in (let TMP_14 \def (lweight a5) in (let TMP_15 \def (f_equal2 nat nat 
nat plus TMP_11 TMP_12 TMP_13 TMP_14 H1 H3) in (f_equal nat nat S TMP_7 
TMP_10 TMP_15)))))))))))))))))))) in (leq_ind g TMP_3 TMP_4 TMP_16 a1 a2 
H))))))).

theorem llt_repl:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (\forall 
(a3: A).((llt a1 a3) \to (llt a2 a3))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(\lambda (a3: A).(\lambda (H0: (lt (lweight a1) (lweight a3))).(let 
TMP_1 \def (lweight a1) in (let TMP_3 \def (\lambda (n: nat).(let TMP_2 \def 
(lweight a3) in (lt n TMP_2))) in (let TMP_4 \def (lweight a2) in (let TMP_5 
\def (lweight_repl g a1 a2 H) in (let H1 \def (eq_ind nat TMP_1 TMP_3 H0 
TMP_4 TMP_5) in H1)))))))))).

theorem llt_trans:
 \forall (a1: A).(\forall (a2: A).(\forall (a3: A).((llt a1 a2) \to ((llt a2 
a3) \to (llt a1 a3)))))
\def
 \lambda (a1: A).(\lambda (a2: A).(\lambda (a3: A).(\lambda (H: (lt (lweight 
a1) (lweight a2))).(\lambda (H0: (lt (lweight a2) (lweight a3))).(let TMP_1 
\def (lweight a1) in (let TMP_2 \def (lweight a2) in (let TMP_3 \def (lweight 
a3) in (lt_trans TMP_1 TMP_2 TMP_3 H H0)))))))).

theorem llt_head_sx:
 \forall (a1: A).(\forall (a2: A).(llt a1 (AHead a1 a2)))
\def
 \lambda (a1: A).(\lambda (a2: A).(let TMP_1 \def (lweight a1) in (let TMP_2 
\def (lweight a1) in (let TMP_3 \def (lweight a2) in (let TMP_4 \def (plus 
TMP_2 TMP_3) in (let TMP_5 \def (lweight a1) in (let TMP_6 \def (lweight a2) 
in (let TMP_7 \def (le_plus_l TMP_5 TMP_6) in (le_n_S TMP_1 TMP_4 
TMP_7))))))))).

theorem llt_head_dx:
 \forall (a1: A).(\forall (a2: A).(llt a2 (AHead a1 a2)))
\def
 \lambda (a1: A).(\lambda (a2: A).(let TMP_1 \def (lweight a2) in (let TMP_2 
\def (lweight a1) in (let TMP_3 \def (lweight a2) in (let TMP_4 \def (plus 
TMP_2 TMP_3) in (let TMP_5 \def (lweight a1) in (let TMP_6 \def (lweight a2) 
in (let TMP_7 \def (le_plus_r TMP_5 TMP_6) in (le_n_S TMP_1 TMP_4 
TMP_7))))))))).

