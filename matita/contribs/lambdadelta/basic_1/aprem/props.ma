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

include "Basic-1/aprem/fwd.ma".

include "Basic-1/leq/defs.ma".

theorem aprem_repl:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (\forall 
(i: nat).(\forall (b2: A).((aprem i a2 b2) \to (ex2 A (\lambda (b1: A).(leq g 
b1 b2)) (\lambda (b1: A).(aprem i a1 b1)))))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(leq_ind g (\lambda (a: A).(\lambda (a0: A).(\forall (i: nat).(\forall 
(b2: A).((aprem i a0 b2) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda 
(b1: A).(aprem i a b1)))))))) (\lambda (h1: nat).(\lambda (h2: nat).(\lambda 
(n1: nat).(\lambda (n2: nat).(\lambda (k: nat).(\lambda (_: (eq A (aplus g 
(ASort h1 n1) k) (aplus g (ASort h2 n2) k))).(\lambda (i: nat).(\lambda (b2: 
A).(\lambda (H1: (aprem i (ASort h2 n2) b2)).(let H_x \def (aprem_gen_sort b2 
i h2 n2 H1) in (let H2 \def H_x in (False_ind (ex2 A (\lambda (b1: A).(leq g 
b1 b2)) (\lambda (b1: A).(aprem i (ASort h1 n1) b1))) H2)))))))))))) (\lambda 
(a0: A).(\lambda (a3: A).(\lambda (H0: (leq g a0 a3)).(\lambda (_: ((\forall 
(i: nat).(\forall (b2: A).((aprem i a3 b2) \to (ex2 A (\lambda (b1: A).(leq g 
b1 b2)) (\lambda (b1: A).(aprem i a0 b1)))))))).(\lambda (a4: A).(\lambda 
(a5: A).(\lambda (_: (leq g a4 a5)).(\lambda (H3: ((\forall (i: nat).(\forall 
(b2: A).((aprem i a5 b2) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda 
(b1: A).(aprem i a4 b1)))))))).(\lambda (i: nat).(\lambda (b2: A).(\lambda 
(H4: (aprem i (AHead a3 a5) b2)).(nat_ind (\lambda (n: nat).((aprem n (AHead 
a3 a5) b2) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: A).(aprem 
n (AHead a0 a4) b1))))) (\lambda (H5: (aprem O (AHead a3 a5) b2)).(let H_y 
\def (aprem_gen_head_O a3 a5 b2 H5) in (eq_ind_r A a3 (\lambda (a: A).(ex2 A 
(\lambda (b1: A).(leq g b1 a)) (\lambda (b1: A).(aprem O (AHead a0 a4) b1)))) 
(ex_intro2 A (\lambda (b1: A).(leq g b1 a3)) (\lambda (b1: A).(aprem O (AHead 
a0 a4) b1)) a0 H0 (aprem_zero a0 a4)) b2 H_y))) (\lambda (i0: nat).(\lambda 
(_: (((aprem i0 (AHead a3 a5) b2) \to (ex2 A (\lambda (b1: A).(leq g b1 b2)) 
(\lambda (b1: A).(aprem i0 (AHead a0 a4) b1)))))).(\lambda (H5: (aprem (S i0) 
(AHead a3 a5) b2)).(let H_y \def (aprem_gen_head_S a3 a5 b2 i0 H5) in (let 
H_x \def (H3 i0 b2 H_y) in (let H6 \def H_x in (ex2_ind A (\lambda (b1: 
A).(leq g b1 b2)) (\lambda (b1: A).(aprem i0 a4 b1)) (ex2 A (\lambda (b1: 
A).(leq g b1 b2)) (\lambda (b1: A).(aprem (S i0) (AHead a0 a4) b1))) (\lambda 
(x: A).(\lambda (H7: (leq g x b2)).(\lambda (H8: (aprem i0 a4 x)).(ex_intro2 
A (\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: A).(aprem (S i0) (AHead a0 
a4) b1)) x H7 (aprem_succ a4 x i0 H8 a0))))) H6))))))) i H4)))))))))))) a1 a2 
H)))).
(* COMMENTS
Initial nodes: 621
END *)

theorem aprem_asucc:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (i: nat).((aprem i 
a1 a2) \to (aprem i (asucc g a1) a2)))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (i: nat).(\lambda 
(H: (aprem i a1 a2)).(aprem_ind (\lambda (n: nat).(\lambda (a: A).(\lambda 
(a0: A).(aprem n (asucc g a) a0)))) (\lambda (a0: A).(\lambda (a3: 
A).(aprem_zero a0 (asucc g a3)))) (\lambda (a0: A).(\lambda (a: A).(\lambda 
(i0: nat).(\lambda (_: (aprem i0 a0 a)).(\lambda (H1: (aprem i0 (asucc g a0) 
a)).(\lambda (a3: A).(aprem_succ (asucc g a0) a i0 H1 a3))))))) i a1 a2 
H))))).
(* COMMENTS
Initial nodes: 101
END *)

