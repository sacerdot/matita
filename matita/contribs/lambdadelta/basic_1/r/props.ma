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

include "Basic-1/r/defs.ma".

include "Basic-1/s/defs.ma".

theorem r_S:
 \forall (k: K).(\forall (i: nat).(eq nat (r k (S i)) (S (r k i))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(eq nat (r k0 (S 
i)) (S (r k0 i))))) (\lambda (b: B).(\lambda (i: nat).(refl_equal nat (S (r 
(Bind b) i))))) (\lambda (f: F).(\lambda (i: nat).(refl_equal nat (S (r (Flat 
f) i))))) k).
(* COMMENTS
Initial nodes: 65
END *)

theorem r_plus:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (r k (plus i j)) 
(plus (r k i) j))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(\forall (j: 
nat).(eq nat (r k0 (plus i j)) (plus (r k0 i) j))))) (\lambda (b: B).(\lambda 
(i: nat).(\lambda (j: nat).(refl_equal nat (plus (r (Bind b) i) j))))) 
(\lambda (f: F).(\lambda (i: nat).(\lambda (j: nat).(refl_equal nat (plus (r 
(Flat f) i) j))))) k).
(* COMMENTS
Initial nodes: 79
END *)

theorem r_plus_sym:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (r k (plus i j)) 
(plus i (r k j)))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(\forall (j: 
nat).(eq nat (r k0 (plus i j)) (plus i (r k0 j)))))) (\lambda (_: B).(\lambda 
(i: nat).(\lambda (j: nat).(refl_equal nat (plus i j))))) (\lambda (_: 
F).(\lambda (i: nat).(\lambda (j: nat).(plus_n_Sm i j)))) k).
(* COMMENTS
Initial nodes: 63
END *)

theorem r_minus:
 \forall (i: nat).(\forall (n: nat).((lt n i) \to (\forall (k: K).(eq nat 
(minus (r k i) (S n)) (r k (minus i (S n)))))))
\def
 \lambda (i: nat).(\lambda (n: nat).(\lambda (H: (lt n i)).(\lambda (k: 
K).(K_ind (\lambda (k0: K).(eq nat (minus (r k0 i) (S n)) (r k0 (minus i (S 
n))))) (\lambda (_: B).(refl_equal nat (minus i (S n)))) (\lambda (_: 
F).(minus_x_Sy i n H)) k)))).
(* COMMENTS
Initial nodes: 69
END *)

theorem r_dis:
 \forall (k: K).(\forall (P: Prop).(((((\forall (i: nat).(eq nat (r k i) i))) 
\to P)) \to (((((\forall (i: nat).(eq nat (r k i) (S i)))) \to P)) \to P)))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (P: Prop).(((((\forall (i: 
nat).(eq nat (r k0 i) i))) \to P)) \to (((((\forall (i: nat).(eq nat (r k0 i) 
(S i)))) \to P)) \to P)))) (\lambda (b: B).(\lambda (P: Prop).(\lambda (H: 
((((\forall (i: nat).(eq nat (r (Bind b) i) i))) \to P))).(\lambda (_: 
((((\forall (i: nat).(eq nat (r (Bind b) i) (S i)))) \to P))).(H (\lambda (i: 
nat).(refl_equal nat i))))))) (\lambda (f: F).(\lambda (P: Prop).(\lambda (_: 
((((\forall (i: nat).(eq nat (r (Flat f) i) i))) \to P))).(\lambda (H0: 
((((\forall (i: nat).(eq nat (r (Flat f) i) (S i)))) \to P))).(H0 (\lambda 
(i: nat).(refl_equal nat (S i)))))))) k).
(* COMMENTS
Initial nodes: 151
END *)

theorem s_r:
 \forall (k: K).(\forall (i: nat).(eq nat (s k (r k i)) (S i)))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(eq nat (s k0 (r k0 
i)) (S i)))) (\lambda (_: B).(\lambda (i: nat).(refl_equal nat (S i)))) 
(\lambda (_: F).(\lambda (i: nat).(refl_equal nat (S i)))) k).
(* COMMENTS
Initial nodes: 51
END *)

theorem r_arith0:
 \forall (k: K).(\forall (i: nat).(eq nat (minus (r k (S i)) (S O)) (r k i)))
\def
 \lambda (k: K).(\lambda (i: nat).(eq_ind_r nat (S (r k i)) (\lambda (n: 
nat).(eq nat (minus n (S O)) (r k i))) (eq_ind_r nat (r k i) (\lambda (n: 
nat).(eq nat n (r k i))) (refl_equal nat (r k i)) (minus (S (r k i)) (S O)) 
(minus_Sx_SO (r k i))) (r k (S i)) (r_S k i))).
(* COMMENTS
Initial nodes: 105
END *)

theorem r_arith1:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (minus (r k (S 
i)) (S j)) (minus (r k i) j))))
\def
 \lambda (k: K).(\lambda (i: nat).(\lambda (j: nat).(eq_ind_r nat (S (r k i)) 
(\lambda (n: nat).(eq nat (minus n (S j)) (minus (r k i) j))) (refl_equal nat 
(minus (r k i) j)) (r k (S i)) (r_S k i)))).
(* COMMENTS
Initial nodes: 69
END *)

