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

include "basic_1/flt/defs.ma".

include "basic_1/C/props.ma".

lemma flt_thead_sx:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).(flt c u c 
(THead k u t)))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(lt_reg_l 
(tweight u) (S (plus (tweight u) (tweight t))) (cweight c) (le_n_S (tweight 
u) (plus (tweight u) (tweight t)) (le_plus_l (tweight u) (tweight t))))))).

lemma flt_thead_dx:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).(flt c t c 
(THead k u t)))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(lt_reg_l 
(tweight t) (S (plus (tweight u) (tweight t))) (cweight c) (le_n_S (tweight 
t) (plus (tweight u) (tweight t)) (le_plus_r (tweight u) (tweight t))))))).

lemma flt_shift:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).(flt (CHead c 
k u) t c (THead k u t)))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(eq_ind nat 
(S (plus (cweight c) (plus (tweight u) (tweight t)))) (\lambda (n: nat).(lt 
(plus (plus (cweight c) (tweight u)) (tweight t)) n)) (eq_ind_r nat (plus 
(plus (cweight c) (tweight u)) (tweight t)) (\lambda (n: nat).(lt (plus (plus 
(cweight c) (tweight u)) (tweight t)) (S n))) (le_n (S (plus (plus (cweight 
c) (tweight u)) (tweight t)))) (plus (cweight c) (plus (tweight u) (tweight 
t))) (plus_assoc_l (cweight c) (tweight u) (tweight t))) (plus (cweight c) (S 
(plus (tweight u) (tweight t)))) (plus_n_Sm (cweight c) (plus (tweight u) 
(tweight t))))))).

lemma flt_arith0:
 \forall (k: K).(\forall (c: C).(\forall (t: T).(\forall (i: nat).(flt c t 
(CHead c k t) (TLRef i)))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (t: T).(\lambda (_: 
nat).(lt_x_plus_x_Sy (plus (cweight c) (tweight t)) O)))).

lemma flt_arith1:
 \forall (k1: K).(\forall (c1: C).(\forall (c2: C).(\forall (t1: T).((cle 
(CHead c1 k1 t1) c2) \to (\forall (k2: K).(\forall (t2: T).(\forall (i: 
nat).(flt c1 t1 (CHead c2 k2 t2) (TLRef i)))))))))
\def
 \lambda (_: K).(\lambda (c1: C).(\lambda (c2: C).(\lambda (t1: T).(\lambda 
(H: (le (plus (cweight c1) (tweight t1)) (cweight c2))).(\lambda (_: 
K).(\lambda (t2: T).(\lambda (_: nat).(le_lt_trans (plus (cweight c1) 
(tweight t1)) (cweight c2) (plus (plus (cweight c2) (tweight t2)) (S O)) H 
(eq_ind_r nat (plus (S O) (plus (cweight c2) (tweight t2))) (\lambda (n: 
nat).(lt (cweight c2) n)) (le_lt_n_Sm (cweight c2) (plus (cweight c2) 
(tweight t2)) (le_plus_l (cweight c2) (tweight t2))) (plus (plus (cweight c2) 
(tweight t2)) (S O)) (plus_sym (plus (cweight c2) (tweight t2)) (S 
O))))))))))).

lemma flt_arith2:
 \forall (c1: C).(\forall (c2: C).(\forall (t1: T).(\forall (i: nat).((flt c1 
t1 c2 (TLRef i)) \to (\forall (k2: K).(\forall (t2: T).(\forall (j: nat).(flt 
c1 t1 (CHead c2 k2 t2) (TLRef j)))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (t1: T).(\lambda (_: nat).(\lambda 
(H: (lt (plus (cweight c1) (tweight t1)) (plus (cweight c2) (S O)))).(\lambda 
(_: K).(\lambda (t2: T).(\lambda (_: nat).(lt_le_trans (plus (cweight c1) 
(tweight t1)) (plus (cweight c2) (S O)) (plus (plus (cweight c2) (tweight 
t2)) (S O)) H (le_plus_plus (cweight c2) (plus (cweight c2) (tweight t2)) (S 
O) (S O) (le_plus_l (cweight c2) (tweight t2)) (le_n (S O))))))))))).

lemma cle_flt_trans:
 \forall (c1: C).(\forall (c2: C).((cle c1 c2) \to (\forall (c3: C).(\forall 
(u2: T).(\forall (u3: T).((flt c2 u2 c3 u3) \to (flt c1 u2 c3 u3)))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (le (cweight c1) (cweight 
c2))).(\lambda (c3: C).(\lambda (u2: T).(\lambda (u3: T).(\lambda (H0: (lt 
(plus (cweight c2) (tweight u2)) (plus (cweight c3) (tweight 
u3)))).(le_lt_trans (plus (cweight c1) (tweight u2)) (plus (cweight c2) 
(tweight u2)) (plus (cweight c3) (tweight u3)) (le_plus_plus (cweight c1) 
(cweight c2) (tweight u2) (tweight u2) H (le_n (tweight u2))) H0))))))).

theorem flt_trans:
 \forall (c1: C).(\forall (c2: C).(\forall (t1: T).(\forall (t2: T).((flt c1 
t1 c2 t2) \to (\forall (c3: C).(\forall (t3: T).((flt c2 t2 c3 t3) \to (flt 
c1 t1 c3 t3))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (lt (fweight c1 t1) (fweight c2 t2))).(\lambda (c3: C).(\lambda (t3: 
T).(\lambda (H0: (lt (fweight c2 t2) (fweight c3 t3))).(lt_trans (fweight c1 
t1) (fweight c2 t2) (fweight c3 t3) H H0)))))))).

