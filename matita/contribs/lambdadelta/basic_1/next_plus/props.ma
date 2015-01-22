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

include "Basic-1/next_plus/defs.ma".

theorem next_plus_assoc:
 \forall (g: G).(\forall (n: nat).(\forall (h1: nat).(\forall (h2: nat).(eq 
nat (next_plus g (next_plus g n h1) h2) (next_plus g n (plus h1 h2))))))
\def
 \lambda (g: G).(\lambda (n: nat).(\lambda (h1: nat).(nat_ind (\lambda (n0: 
nat).(\forall (h2: nat).(eq nat (next_plus g (next_plus g n n0) h2) 
(next_plus g n (plus n0 h2))))) (\lambda (h2: nat).(refl_equal nat (next_plus 
g n h2))) (\lambda (n0: nat).(\lambda (_: ((\forall (h2: nat).(eq nat 
(next_plus g (next_plus g n n0) h2) (next_plus g n (plus n0 h2)))))).(\lambda 
(h2: nat).(nat_ind (\lambda (n1: nat).(eq nat (next_plus g (next g (next_plus 
g n n0)) n1) (next g (next_plus g n (plus n0 n1))))) (eq_ind nat n0 (\lambda 
(n1: nat).(eq nat (next g (next_plus g n n0)) (next g (next_plus g n n1)))) 
(refl_equal nat (next g (next_plus g n n0))) (plus n0 O) (plus_n_O n0)) 
(\lambda (n1: nat).(\lambda (H0: (eq nat (next_plus g (next g (next_plus g n 
n0)) n1) (next g (next_plus g n (plus n0 n1))))).(eq_ind nat (S (plus n0 n1)) 
(\lambda (n2: nat).(eq nat (next g (next_plus g (next g (next_plus g n n0)) 
n1)) (next g (next_plus g n n2)))) (f_equal nat nat (next g) (next_plus g 
(next g (next_plus g n n0)) n1) (next g (next_plus g n (plus n0 n1))) H0) 
(plus n0 (S n1)) (plus_n_Sm n0 n1)))) h2)))) h1))).
(* COMMENTS
Initial nodes: 351
END *)

theorem next_plus_next:
 \forall (g: G).(\forall (n: nat).(\forall (h: nat).(eq nat (next_plus g 
(next g n) h) (next g (next_plus g n h)))))
\def
 \lambda (g: G).(\lambda (n: nat).(\lambda (h: nat).(eq_ind_r nat (next_plus 
g n (plus (S O) h)) (\lambda (n0: nat).(eq nat n0 (next g (next_plus g n 
h)))) (refl_equal nat (next g (next_plus g n h))) (next_plus g (next_plus g n 
(S O)) h) (next_plus_assoc g n (S O) h)))).
(* COMMENTS
Initial nodes: 87
END *)

theorem next_plus_lt:
 \forall (g: G).(\forall (h: nat).(\forall (n: nat).(lt n (next_plus g (next 
g n) h))))
\def
 \lambda (g: G).(\lambda (h: nat).(nat_ind (\lambda (n: nat).(\forall (n0: 
nat).(lt n0 (next_plus g (next g n0) n)))) (\lambda (n: nat).(next_lt g n)) 
(\lambda (n: nat).(\lambda (H: ((\forall (n0: nat).(lt n0 (next_plus g (next 
g n0) n))))).(\lambda (n0: nat).(eq_ind nat (next_plus g (next g (next g n0)) 
n) (\lambda (n1: nat).(lt n0 n1)) (lt_trans n0 (next g n0) (next_plus g (next 
g (next g n0)) n) (next_lt g n0) (H (next g n0))) (next g (next_plus g (next 
g n0) n)) (next_plus_next g (next g n0) n))))) h)).
(* COMMENTS
Initial nodes: 153
END *)

