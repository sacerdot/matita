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

include "basic_1A/C/fwd.ma".

include "basic_1A/T/props.ma".

lemma cle_r:
 \forall (c: C).(cle c c)
\def
 \lambda (c: C).(C_ind (\lambda (c0: C).(le (cweight c0) (cweight c0))) 
(\lambda (_: nat).(le_O_n O)) (\lambda (c0: C).(\lambda (_: (le (cweight c0) 
(cweight c0))).(\lambda (_: K).(\lambda (t: T).(le_n (plus (cweight c0) 
(tweight t))))))) c).

lemma cle_head:
 \forall (c1: C).(\forall (c2: C).((cle c1 c2) \to (\forall (u1: T).(\forall 
(u2: T).((tle u1 u2) \to (\forall (k: K).(cle (CHead c1 k u1) (CHead c2 k 
u2))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (le (cweight c1) (cweight 
c2))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H0: (le (tweight u1) 
(tweight u2))).(\lambda (_: K).(le_plus_plus (cweight c1) (cweight c2) 
(tweight u1) (tweight u2) H H0))))))).

lemma cle_trans_head:
 \forall (c1: C).(\forall (c2: C).((cle c1 c2) \to (\forall (k: K).(\forall 
(u: T).(cle c1 (CHead c2 k u))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (le (cweight c1) (cweight 
c2))).(\lambda (_: K).(\lambda (u: T).(le_plus_trans (cweight c1) (cweight 
c2) (tweight u) H))))).

lemma clt_cong:
 \forall (c: C).(\forall (d: C).((clt c d) \to (\forall (k: K).(\forall (t: 
T).(clt (CHead c k t) (CHead d k t))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (H: (lt (cweight c) (cweight 
d))).(\lambda (_: K).(\lambda (t: T).(lt_reg_r (cweight c) (cweight d) 
(tweight t) H))))).

lemma clt_head:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(clt c (CHead c k u))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (u: T).(eq_ind_r nat (plus (cweight 
c) O) (\lambda (n: nat).(lt n (plus (cweight c) (tweight u)))) (lt_reg_l O 
(tweight u) (cweight c) (tweight_lt u)) (cweight c) (plus_n_O (cweight c))))).

lemma chead_ctail:
 \forall (c: C).(\forall (t: T).(\forall (k: K).(ex_3 K C T (\lambda (h: 
K).(\lambda (d: C).(\lambda (u: T).(eq C (CHead c k t) (CTail h u d))))))))
\def
 \lambda (c: C).(C_ind (\lambda (c0: C).(\forall (t: T).(\forall (k: K).(ex_3 
K C T (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(eq C (CHead c0 k t) 
(CTail h u d))))))))) (\lambda (n: nat).(\lambda (t: T).(\lambda (k: 
K).(ex_3_intro K C T (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(eq C 
(CHead (CSort n) k t) (CTail h u d))))) k (CSort n) t (refl_equal C (CHead 
(CSort n) k t)))))) (\lambda (c0: C).(\lambda (H: ((\forall (t: T).(\forall 
(k: K).(ex_3 K C T (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(eq C 
(CHead c0 k t) (CTail h u d)))))))))).(\lambda (k: K).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (k0: K).(let H_x \def (H t k) in (let H0 \def 
H_x in (ex_3_ind K C T (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(eq C 
(CHead c0 k t) (CTail h u d))))) (ex_3 K C T (\lambda (h: K).(\lambda (d: 
C).(\lambda (u: T).(eq C (CHead (CHead c0 k t) k0 t0) (CTail h u d)))))) 
(\lambda (x0: K).(\lambda (x1: C).(\lambda (x2: T).(\lambda (H1: (eq C (CHead 
c0 k t) (CTail x0 x2 x1))).(eq_ind_r C (CTail x0 x2 x1) (\lambda (c1: 
C).(ex_3 K C T (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(eq C (CHead 
c1 k0 t0) (CTail h u d))))))) (ex_3_intro K C T (\lambda (h: K).(\lambda (d: 
C).(\lambda (u: T).(eq C (CHead (CTail x0 x2 x1) k0 t0) (CTail h u d))))) x0 
(CHead x1 k0 t0) x2 (refl_equal C (CHead (CTail x0 x2 x1) k0 t0))) (CHead c0 
k t) H1))))) H0))))))))) c).

lemma clt_thead:
 \forall (k: K).(\forall (u: T).(\forall (c: C).(clt c (CTail k u c))))
\def
 \lambda (k: K).(\lambda (u: T).(\lambda (c: C).(C_ind (\lambda (c0: C).(clt 
c0 (CTail k u c0))) (\lambda (n: nat).(clt_head k (CSort n) u)) (\lambda (c0: 
C).(\lambda (H: (clt c0 (CTail k u c0))).(\lambda (k0: K).(\lambda (t: 
T).(clt_cong c0 (CTail k u c0) H k0 t))))) c))).

lemma c_tail_ind:
 \forall (P: ((C \to Prop))).(((\forall (n: nat).(P (CSort n)))) \to 
(((\forall (c: C).((P c) \to (\forall (k: K).(\forall (t: T).(P (CTail k t 
c))))))) \to (\forall (c: C).(P c))))
\def
 \lambda (P: ((C \to Prop))).(\lambda (H: ((\forall (n: nat).(P (CSort 
n))))).(\lambda (H0: ((\forall (c: C).((P c) \to (\forall (k: K).(\forall (t: 
T).(P (CTail k t c)))))))).(\lambda (c: C).(clt_wf_ind (\lambda (c0: C).(P 
c0)) (\lambda (c0: C).(C_ind (\lambda (c1: C).(((\forall (d: C).((clt d c1) 
\to (P d)))) \to (P c1))) (\lambda (n: nat).(\lambda (_: ((\forall (d: 
C).((clt d (CSort n)) \to (P d))))).(H n))) (\lambda (c1: C).(\lambda (_: 
((((\forall (d: C).((clt d c1) \to (P d)))) \to (P c1)))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (H2: ((\forall (d: C).((clt d (CHead c1 k t)) \to 
(P d))))).(let H_x \def (chead_ctail c1 t k) in (let H3 \def H_x in (ex_3_ind 
K C T (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(eq C (CHead c1 k t) 
(CTail h u d))))) (P (CHead c1 k t)) (\lambda (x0: K).(\lambda (x1: 
C).(\lambda (x2: T).(\lambda (H4: (eq C (CHead c1 k t) (CTail x0 x2 
x1))).(eq_ind_r C (CTail x0 x2 x1) (\lambda (c2: C).(P c2)) (let H5 \def 
(eq_ind C (CHead c1 k t) (\lambda (c2: C).(\forall (d: C).((clt d c2) \to (P 
d)))) H2 (CTail x0 x2 x1) H4) in (H0 x1 (H5 x1 (clt_thead x0 x2 x1)) x0 x2)) 
(CHead c1 k t) H4))))) H3)))))))) c0)) c)))).

