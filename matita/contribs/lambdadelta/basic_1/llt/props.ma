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

include "Basic-1/llt/defs.ma".

include "Basic-1/leq/defs.ma".

theorem lweight_repl:
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
(* COMMENTS
Initial nodes: 189
END *)

theorem llt_repl:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (\forall 
(a3: A).((llt a1 a3) \to (llt a2 a3))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(\lambda (a3: A).(\lambda (H0: (lt (lweight a1) (lweight a3))).(let H1 
\def (eq_ind nat (lweight a1) (\lambda (n: nat).(lt n (lweight a3))) H0 
(lweight a2) (lweight_repl g a1 a2 H)) in H1)))))).
(* COMMENTS
Initial nodes: 61
END *)

theorem llt_trans:
 \forall (a1: A).(\forall (a2: A).(\forall (a3: A).((llt a1 a2) \to ((llt a2 
a3) \to (llt a1 a3)))))
\def
 \lambda (a1: A).(\lambda (a2: A).(\lambda (a3: A).(\lambda (H: (lt (lweight 
a1) (lweight a2))).(\lambda (H0: (lt (lweight a2) (lweight a3))).(lt_trans 
(lweight a1) (lweight a2) (lweight a3) H H0))))).
(* COMMENTS
Initial nodes: 43
END *)

theorem llt_head_sx:
 \forall (a1: A).(\forall (a2: A).(llt a1 (AHead a1 a2)))
\def
 \lambda (a1: A).(\lambda (a2: A).(le_n_S (lweight a1) (plus (lweight a1) 
(lweight a2)) (le_plus_l (lweight a1) (lweight a2)))).
(* COMMENTS
Initial nodes: 29
END *)

theorem llt_head_dx:
 \forall (a1: A).(\forall (a2: A).(llt a2 (AHead a1 a2)))
\def
 \lambda (a1: A).(\lambda (a2: A).(le_n_S (lweight a2) (plus (lweight a1) 
(lweight a2)) (le_plus_r (lweight a1) (lweight a2)))).
(* COMMENTS
Initial nodes: 29
END *)

theorem llt_wf__q_ind:
 \forall (P: ((A \to Prop))).(((\forall (n: nat).((\lambda (P0: ((A \to 
Prop))).(\lambda (n0: nat).(\forall (a: A).((eq nat (lweight a) n0) \to (P0 
a))))) P n))) \to (\forall (a: A).(P a)))
\def
 let Q \def (\lambda (P: ((A \to Prop))).(\lambda (n: nat).(\forall (a: 
A).((eq nat (lweight a) n) \to (P a))))) in (\lambda (P: ((A \to 
Prop))).(\lambda (H: ((\forall (n: nat).(\forall (a: A).((eq nat (lweight a) 
n) \to (P a)))))).(\lambda (a: A).(H (lweight a) a (refl_equal nat (lweight 
a)))))).
(* COMMENTS
Initial nodes: 61
END *)

theorem llt_wf_ind:
 \forall (P: ((A \to Prop))).(((\forall (a2: A).(((\forall (a1: A).((llt a1 
a2) \to (P a1)))) \to (P a2)))) \to (\forall (a: A).(P a)))
\def
 let Q \def (\lambda (P: ((A \to Prop))).(\lambda (n: nat).(\forall (a: 
A).((eq nat (lweight a) n) \to (P a))))) in (\lambda (P: ((A \to 
Prop))).(\lambda (H: ((\forall (a2: A).(((\forall (a1: A).((lt (lweight a1) 
(lweight a2)) \to (P a1)))) \to (P a2))))).(\lambda (a: A).(llt_wf__q_ind 
(\lambda (a0: A).(P a0)) (\lambda (n: nat).(lt_wf_ind n (Q (\lambda (a0: 
A).(P a0))) (\lambda (n0: nat).(\lambda (H0: ((\forall (m: nat).((lt m n0) 
\to (Q (\lambda (a0: A).(P a0)) m))))).(\lambda (a0: A).(\lambda (H1: (eq nat 
(lweight a0) n0)).(let H2 \def (eq_ind_r nat n0 (\lambda (n1: nat).(\forall 
(m: nat).((lt m n1) \to (\forall (a1: A).((eq nat (lweight a1) m) \to (P 
a1)))))) H0 (lweight a0) H1) in (H a0 (\lambda (a1: A).(\lambda (H3: (lt 
(lweight a1) (lweight a0))).(H2 (lweight a1) H3 a1 (refl_equal nat (lweight 
a1))))))))))))) a)))).
(* COMMENTS
Initial nodes: 179
END *)

