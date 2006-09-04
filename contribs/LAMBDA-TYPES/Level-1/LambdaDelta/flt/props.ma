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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/flt/props".

include "flt/defs.ma".

include "C/props.ma".

theorem flt_thead_sx:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).(flt c u c 
(THead k u t)))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(lt_le_S 
(plus (cweight c) (tweight u)) (plus (cweight c) (S (plus (tweight u) 
(tweight t)))) (plus_le_lt_compat (cweight c) (cweight c) (tweight u) (S 
(plus (tweight u) (tweight t))) (le_n (cweight c)) (le_lt_n_Sm (tweight u) 
(plus (tweight u) (tweight t)) (le_plus_l (tweight u) (tweight t)))))))).

theorem flt_thead_dx:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).(flt c t c 
(THead k u t)))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(lt_le_S 
(plus (cweight c) (tweight t)) (plus (cweight c) (S (plus (tweight u) 
(tweight t)))) (plus_le_lt_compat (cweight c) (cweight c) (tweight t) (S 
(plus (tweight u) (tweight t))) (le_n (cweight c)) (le_lt_n_Sm (tweight t) 
(plus (tweight u) (tweight t)) (le_plus_r (tweight u) (tweight t)))))))).

theorem flt_shift:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).(flt (CHead c 
k u) t c (THead k u t)))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(eq_ind nat 
(S (plus (cweight c) (plus (tweight u) (tweight t)))) (\lambda (n: nat).(lt 
(plus (plus (cweight c) (tweight u)) (tweight t)) n)) (eq_ind_r nat (plus 
(plus (cweight c) (tweight u)) (tweight t)) (\lambda (n: nat).(lt (plus (plus 
(cweight c) (tweight u)) (tweight t)) (S n))) (le_n (S (plus (plus (cweight 
c) (tweight u)) (tweight t)))) (plus (cweight c) (plus (tweight u) (tweight 
t))) (plus_assoc (cweight c) (tweight u) (tweight t))) (plus (cweight c) (S 
(plus (tweight u) (tweight t)))) (plus_n_Sm (cweight c) (plus (tweight u) 
(tweight t))))))).

theorem flt_arith0:
 \forall (k: K).(\forall (c: C).(\forall (t: T).(\forall (i: nat).(flt c t 
(CHead c k t) (TLRef i)))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (t: T).(\lambda (_: nat).(le_S_n (S 
(plus (cweight c) (tweight t))) (plus (plus (cweight c) (tweight t)) (S O)) 
(lt_le_S (S (plus (cweight c) (tweight t))) (S (plus (plus (cweight c) 
(tweight t)) (S O))) (lt_n_S (plus (cweight c) (tweight t)) (plus (plus 
(cweight c) (tweight t)) (S O)) (lt_x_plus_x_Sy (plus (cweight c) (tweight 
t)) O))))))).

theorem flt_arith1:
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
(tweight t2)) (S O)) (plus_comm (plus (cweight c2) (tweight t2)) (S 
O))))))))))).

theorem flt_arith2:
 \forall (c1: C).(\forall (c2: C).(\forall (t1: T).(\forall (i: nat).((flt c1 
t1 c2 (TLRef i)) \to (\forall (k2: K).(\forall (t2: T).(\forall (j: nat).(flt 
c1 t1 (CHead c2 k2 t2) (TLRef j)))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (t1: T).(\lambda (_: nat).(\lambda 
(H: (lt (plus (cweight c1) (tweight t1)) (plus (cweight c2) (S O)))).(\lambda 
(_: K).(\lambda (t2: T).(\lambda (_: nat).(lt_le_trans (plus (cweight c1) 
(tweight t1)) (plus (cweight c2) (S O)) (plus (plus (cweight c2) (tweight 
t2)) (S O)) H (le_S_n (plus (cweight c2) (S O)) (plus (plus (cweight c2) 
(tweight t2)) (S O)) (lt_le_S (plus (cweight c2) (S O)) (S (plus (plus 
(cweight c2) (tweight t2)) (S O))) (le_lt_n_Sm (plus (cweight c2) (S O)) 
(plus (plus (cweight c2) (tweight t2)) (S O)) (plus_le_compat (cweight c2) 
(plus (cweight c2) (tweight t2)) (S O) (S O) (le_plus_l (cweight c2) (tweight 
t2)) (le_n (S O)))))))))))))).

theorem flt_wf__q_ind:
 \forall (P: ((C \to (T \to Prop)))).(((\forall (n: nat).((\lambda (P: ((C 
\to (T \to Prop)))).(\lambda (n0: nat).(\forall (c: C).(\forall (t: T).((eq 
nat (fweight c t) n0) \to (P c t)))))) P n))) \to (\forall (c: C).(\forall 
(t: T).(P c t))))
\def
 let Q \def (\lambda (P: ((C \to (T \to Prop)))).(\lambda (n: nat).(\forall 
(c: C).(\forall (t: T).((eq nat (fweight c t) n) \to (P c t)))))) in (\lambda 
(P: ((C \to (T \to Prop)))).(\lambda (H: ((\forall (n: nat).(\forall (c: 
C).(\forall (t: T).((eq nat (fweight c t) n) \to (P c t))))))).(\lambda (c: 
C).(\lambda (t: T).(H (fweight c t) c t (refl_equal nat (fweight c t))))))).

theorem flt_wf_ind:
 \forall (P: ((C \to (T \to Prop)))).(((\forall (c2: C).(\forall (t2: 
T).(((\forall (c1: C).(\forall (t1: T).((flt c1 t1 c2 t2) \to (P c1 t1))))) 
\to (P c2 t2))))) \to (\forall (c: C).(\forall (t: T).(P c t))))
\def
 let Q \def (\lambda (P: ((C \to (T \to Prop)))).(\lambda (n: nat).(\forall 
(c: C).(\forall (t: T).((eq nat (fweight c t) n) \to (P c t)))))) in (\lambda 
(P: ((C \to (T \to Prop)))).(\lambda (H: ((\forall (c2: C).(\forall (t2: 
T).(((\forall (c1: C).(\forall (t1: T).((flt c1 t1 c2 t2) \to (P c1 t1))))) 
\to (P c2 t2)))))).(\lambda (c: C).(\lambda (t: T).(flt_wf__q_ind P (\lambda 
(n: nat).(lt_wf_ind n (Q P) (\lambda (n0: nat).(\lambda (H0: ((\forall (m: 
nat).((lt m n0) \to (Q P m))))).(\lambda (c0: C).(\lambda (t0: T).(\lambda 
(H1: (eq nat (fweight c0 t0) n0)).(let H2 \def (eq_ind_r nat n0 (\lambda (n: 
nat).(\forall (m: nat).((lt m n) \to (\forall (c: C).(\forall (t: T).((eq nat 
(fweight c t) m) \to (P c t))))))) H0 (fweight c0 t0) H1) in (H c0 t0 
(\lambda (c1: C).(\lambda (t1: T).(\lambda (H3: (flt c1 t1 c0 t0)).(H2 
(fweight c1 t1) H3 c1 t1 (refl_equal nat (fweight c1 t1))))))))))))))) c 
t))))).

