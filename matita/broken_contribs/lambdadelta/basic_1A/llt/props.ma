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

include "basic_1A/llt/defs.ma".

include "basic_1A/leq/fwd.ma".

lemma lweight_repl:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (eq nat 
(lweight a1) (lweight a2)))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(leq_ind g (\lambda (a: A).(\lambda (a0: A).(eq nat (lweight a) (lweight 
a0)))) (\lambda (h1: nat).(\lambda (h2: nat).(\lambda (n1: nat).(\lambda (n2: 
nat).(\lambda (k: nat).(\lambda (_: (eq A (aplus g (ASort h1 n1) k) (aplus g 
(ASort h2 n2) k))).(refl_equal nat O))))))) (\lambda (a0: A).(\lambda (a3: 
A).(\lambda (_: (leq g a0 a3)).(\lambda (H1: (eq nat (lweight a0) (lweight 
a3))).(\lambda (a4: A).(\lambda (a5: A).(\lambda (_: (leq g a4 a5)).(\lambda 
(H3: (eq nat (lweight a4) (lweight a5))).(f_equal nat nat S (plus (lweight 
a0) (lweight a4)) (plus (lweight a3) (lweight a5)) (f_equal2 nat nat nat plus 
(lweight a0) (lweight a3) (lweight a4) (lweight a5) H1 H3)))))))))) a1 a2 
H)))).

lemma llt_repl:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (\forall 
(a3: A).((llt a1 a3) \to (llt a2 a3))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(\lambda (a3: A).(\lambda (H0: (lt (lweight a1) (lweight a3))).(let H1 
\def (eq_ind nat (lweight a1) (\lambda (n: nat).(lt n (lweight a3))) H0 
(lweight a2) (lweight_repl g a1 a2 H)) in H1)))))).

theorem llt_trans:
 \forall (a1: A).(\forall (a2: A).(\forall (a3: A).((llt a1 a2) \to ((llt a2 
a3) \to (llt a1 a3)))))
\def
 \lambda (a1: A).(\lambda (a2: A).(\lambda (a3: A).(\lambda (H: (lt (lweight 
a1) (lweight a2))).(\lambda (H0: (lt (lweight a2) (lweight a3))).(lt_trans 
(lweight a1) (lweight a2) (lweight a3) H H0))))).

lemma llt_head_sx:
 \forall (a1: A).(\forall (a2: A).(llt a1 (AHead a1 a2)))
\def
 \lambda (a1: A).(\lambda (a2: A).(le_n_S (lweight a1) (plus (lweight a1) 
(lweight a2)) (le_plus_l (lweight a1) (lweight a2)))).

lemma llt_head_dx:
 \forall (a1: A).(\forall (a2: A).(llt a2 (AHead a1 a2)))
\def
 \lambda (a1: A).(\lambda (a2: A).(le_n_S (lweight a2) (plus (lweight a1) 
(lweight a2)) (le_plus_r (lweight a1) (lweight a2)))).

