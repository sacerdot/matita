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

include "Basic-1/s/defs.ma".

theorem s_S:
 \forall (k: K).(\forall (i: nat).(eq nat (s k (S i)) (S (s k i))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(eq nat (s k0 (S 
i)) (S (s k0 i))))) (\lambda (b: B).(\lambda (i: nat).(refl_equal nat (S (s 
(Bind b) i))))) (\lambda (f: F).(\lambda (i: nat).(refl_equal nat (S (s (Flat 
f) i))))) k).
(* COMMENTS
Initial nodes: 65
END *)

theorem s_plus:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (s k (plus i j)) 
(plus (s k i) j))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(\forall (j: 
nat).(eq nat (s k0 (plus i j)) (plus (s k0 i) j))))) (\lambda (b: B).(\lambda 
(i: nat).(\lambda (j: nat).(refl_equal nat (plus (s (Bind b) i) j))))) 
(\lambda (f: F).(\lambda (i: nat).(\lambda (j: nat).(refl_equal nat (plus (s 
(Flat f) i) j))))) k).
(* COMMENTS
Initial nodes: 79
END *)

theorem s_plus_sym:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (s k (plus i j)) 
(plus i (s k j)))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(\forall (j: 
nat).(eq nat (s k0 (plus i j)) (plus i (s k0 j)))))) (\lambda (_: B).(\lambda 
(i: nat).(\lambda (j: nat).(eq_ind_r nat (plus i (S j)) (\lambda (n: nat).(eq 
nat n (plus i (S j)))) (refl_equal nat (plus i (S j))) (S (plus i j)) 
(plus_n_Sm i j))))) (\lambda (f: F).(\lambda (i: nat).(\lambda (j: 
nat).(refl_equal nat (plus i (s (Flat f) j)))))) k).
(* COMMENTS
Initial nodes: 117
END *)

theorem s_minus:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).((le j i) \to (eq nat (s 
k (minus i j)) (minus (s k i) j)))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(\forall (j: 
nat).((le j i) \to (eq nat (s k0 (minus i j)) (minus (s k0 i) j)))))) 
(\lambda (_: B).(\lambda (i: nat).(\lambda (j: nat).(\lambda (H: (le j 
i)).(eq_ind_r nat (minus (S i) j) (\lambda (n: nat).(eq nat n (minus (S i) 
j))) (refl_equal nat (minus (S i) j)) (S (minus i j)) (minus_Sn_m i j H)))))) 
(\lambda (f: F).(\lambda (i: nat).(\lambda (j: nat).(\lambda (_: (le j 
i)).(refl_equal nat (minus (s (Flat f) i) j)))))) k).
(* COMMENTS
Initial nodes: 137
END *)

theorem minus_s_s:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (minus (s k i) (s 
k j)) (minus i j))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(\forall (j: 
nat).(eq nat (minus (s k0 i) (s k0 j)) (minus i j))))) (\lambda (_: 
B).(\lambda (i: nat).(\lambda (j: nat).(refl_equal nat (minus i j))))) 
(\lambda (_: F).(\lambda (i: nat).(\lambda (j: nat).(refl_equal nat (minus i 
j))))) k).
(* COMMENTS
Initial nodes: 67
END *)

theorem s_le:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).((le i j) \to (le (s k i) 
(s k j)))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(\forall (j: 
nat).((le i j) \to (le (s k0 i) (s k0 j)))))) (\lambda (_: B).(\lambda (i: 
nat).(\lambda (j: nat).(\lambda (H: (le i j)).(le_n_S i j H))))) (\lambda (_: 
F).(\lambda (i: nat).(\lambda (j: nat).(\lambda (H: (le i j)).H)))) k).
(* COMMENTS
Initial nodes: 65
END *)

theorem s_lt:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).((lt i j) \to (lt (s k i) 
(s k j)))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(\forall (j: 
nat).((lt i j) \to (lt (s k0 i) (s k0 j)))))) (\lambda (_: B).(\lambda (i: 
nat).(\lambda (j: nat).(\lambda (H: (lt i j)).(le_n_S (S i) j H))))) (\lambda 
(_: F).(\lambda (i: nat).(\lambda (j: nat).(\lambda (H: (lt i j)).H)))) k).
(* COMMENTS
Initial nodes: 67
END *)

theorem s_inj:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).((eq nat (s k i) (s k j)) 
\to (eq nat i j))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(\forall (j: 
nat).((eq nat (s k0 i) (s k0 j)) \to (eq nat i j))))) (\lambda (b: 
B).(\lambda (i: nat).(\lambda (j: nat).(\lambda (H: (eq nat (s (Bind b) i) (s 
(Bind b) j))).(eq_add_S i j H))))) (\lambda (f: F).(\lambda (i: nat).(\lambda 
(j: nat).(\lambda (H: (eq nat (s (Flat f) i) (s (Flat f) j))).H)))) k).
(* COMMENTS
Initial nodes: 97
END *)

theorem s_inc:
 \forall (k: K).(\forall (i: nat).(le i (s k i)))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(le i (s k0 i)))) 
(\lambda (b: B).(\lambda (i: nat).(le_S_n i (s (Bind b) i) (le_S (S i) (s 
(Bind b) i) (le_n (s (Bind b) i)))))) (\lambda (f: F).(\lambda (i: nat).(le_n 
(s (Flat f) i)))) k).
(* COMMENTS
Initial nodes: 73
END *)

theorem s_arith0:
 \forall (k: K).(\forall (i: nat).(eq nat (minus (s k i) (s k O)) i))
\def
 \lambda (k: K).(\lambda (i: nat).(eq_ind_r nat (minus i O) (\lambda (n: 
nat).(eq nat n i)) (eq_ind nat i (\lambda (n: nat).(eq nat n i)) (refl_equal 
nat i) (minus i O) (minus_n_O i)) (minus (s k i) (s k O)) (minus_s_s k i O))).
(* COMMENTS
Initial nodes: 77
END *)

theorem s_arith1:
 \forall (b: B).(\forall (i: nat).(eq nat (minus (s (Bind b) i) (S O)) i))
\def
 \lambda (_: B).(\lambda (i: nat).(eq_ind nat i (\lambda (n: nat).(eq nat n 
i)) (refl_equal nat i) (minus i O) (minus_n_O i))).
(* COMMENTS
Initial nodes: 35
END *)

