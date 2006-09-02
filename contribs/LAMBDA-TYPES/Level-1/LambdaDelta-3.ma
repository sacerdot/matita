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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta-3".

include "LambdaDelta-1.ma".

inductive C: Set \def
| CSort: nat \to C
| CHead: C \to (K \to (T \to C)).

definition r:
 K \to (nat \to nat)
\def
 \lambda (k: K).(\lambda (i: nat).(match k with [(Bind _) \Rightarrow i | (Flat _) \Rightarrow (S i)])).

definition clen:
 C \to nat
\def
 let rec clen (c: C) on c: nat \def (match c with [(CSort _) \Rightarrow O | (CHead c0 k _) \Rightarrow (s k (clen c0))]) in clen.

theorem r_S:
 \forall (k: K).(\forall (i: nat).(eq nat (r k (S i)) (S (r k i))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(eq nat (r k0 (S i)) (S (r k0 i))))) (\lambda (b: B).(\lambda (i: nat).(refl_equal nat (S (r (Bind b) i))))) (\lambda (f: F).(\lambda (i: nat).(refl_equal nat (S (r (Flat f) i))))) k).

theorem r_plus:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (r k (plus i j)) (plus (r k i) j))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(\forall (j: nat).(eq nat (r k0 (plus i j)) (plus (r k0 i) j))))) (\lambda (b: B).(\lambda (i: nat).(\lambda (j: nat).(refl_equal nat (plus (r (Bind b) i) j))))) (\lambda (f: F).(\lambda (i: nat).(\lambda (j: nat).(refl_equal nat (plus (r (Flat f) i) j))))) k).

theorem r_plus_sym:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (r k (plus i j)) (plus i (r k j)))))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(\forall (j: nat).(eq nat (r k0 (plus i j)) (plus i (r k0 j)))))) (\lambda (_: B).(\lambda (i: nat).(\lambda (j: nat).(refl_equal nat (plus i j))))) (\lambda (_: F).(\lambda (i: nat).(\lambda (j: nat).(plus_n_Sm i j)))) k).

theorem r_minus:
 \forall (i: nat).(\forall (n: nat).((lt n i) \to (\forall (k: K).(eq nat (minus (r k i) (S n)) (r k (minus i (S n)))))))
\def
 \lambda (i: nat).(\lambda (n: nat).(\lambda (H: (lt n i)).(\lambda (k: K).(K_ind (\lambda (k0: K).(eq nat (minus (r k0 i) (S n)) (r k0 (minus i (S n))))) (\lambda (_: B).(refl_equal nat (minus i (S n)))) (\lambda (_: F).(minus_x_Sy i n H)) k)))).

theorem r_dis:
 \forall (k: K).(\forall (P: Prop).(((((\forall (i: nat).(eq nat (r k i) i))) \to P)) \to (((((\forall (i: nat).(eq nat (r k i) (S i)))) \to P)) \to P)))
\def
 \lambda (k: K).(K_ind (\lambda (k0: K).(\forall (P: Prop).(((((\forall (i: nat).(eq nat (r k0 i) i))) \to P)) \to (((((\forall (i: nat).(eq nat (r k0 i) (S i)))) \to P)) \to P)))) (\lambda (b: B).(\lambda (P: Prop).(\lambda (H: ((((\forall (i: nat).(eq nat (r (Bind b) i) i))) \to P))).(\lambda (_: ((((\forall (i: nat).(eq nat (r (Bind b) i) (S i)))) \to P))).(H (\lambda (i: nat).(refl_equal nat i))))))) (\lambda (f: F).(\lambda (P: Prop).(\lambda (_: ((((\forall (i: nat).(eq nat (r (Flat f) i) i))) \to P))).(\lambda (H0: ((((\forall (i: nat).(eq nat (r (Flat f) i) (S i)))) \to P))).(H0 (\lambda (i: nat).(refl_equal nat (S i)))))))) k).

theorem s_r:
 \forall (k: K).(\forall (i: nat).(eq nat (s k (r k i)) (S i)))
\def
 \lambda (k: K).(match k return (\lambda (k0: K).(\forall (i: nat).(eq nat (s k0 (r k0 i)) (S i)))) with [(Bind _) \Rightarrow (\lambda (i: nat).(refl_equal nat (S i))) | (Flat _) \Rightarrow (\lambda (i: nat).(refl_equal nat (S i)))]).

theorem r_arith0:
 \forall (k: K).(\forall (i: nat).(eq nat (minus (r k (S i)) (S O)) (r k i)))
\def
 \lambda (k: K).(\lambda (i: nat).(eq_ind_r nat (S (r k i)) (\lambda (n: nat).(eq nat (minus n (S O)) (r k i))) (eq_ind_r nat (r k i) (\lambda (n: nat).(eq nat n (r k i))) (refl_equal nat (r k i)) (minus (S (r k i)) (S O)) (minus_Sx_SO (r k i))) (r k (S i)) (r_S k i))).

theorem r_arith1:
 \forall (k: K).(\forall (i: nat).(\forall (j: nat).(eq nat (minus (r k (S i)) (S j)) (minus (r k i) j))))
\def
 \lambda (k: K).(\lambda (i: nat).(\lambda (j: nat).(eq_ind_r nat (S (r k i)) (\lambda (n: nat).(eq nat (minus n (S j)) (minus (r k i) j))) (refl_equal nat (minus (r k i) j)) (r k (S i)) (r_S k i)))).

definition tweight:
 T \to nat
\def
 let rec tweight (t: T) on t: nat \def (match t with [(TSort _) \Rightarrow (S O) | (TLRef _) \Rightarrow (S O) | (THead _ u t0) \Rightarrow (S (plus (tweight u) (tweight t0)))]) in tweight.

definition cweight:
 C \to nat
\def
 let rec cweight (c: C) on c: nat \def (match c with [(CSort _) \Rightarrow O | (CHead c0 _ t) \Rightarrow (plus (cweight c0) (tweight t))]) in cweight.

definition clt:
 C \to (C \to Prop)
\def
 \lambda (c1: C).(\lambda (c2: C).(lt (cweight c1) (cweight c2))).

definition cle:
 C \to (C \to Prop)
\def
 \lambda (c1: C).(\lambda (c2: C).(le (cweight c1) (cweight c2))).

theorem tweight_lt:
 \forall (t: T).(lt O (tweight t))
\def
 \lambda (t: T).(match t return (\lambda (t0: T).(lt O (tweight t0))) with [(TSort _) \Rightarrow (le_n (S O)) | (TLRef _) \Rightarrow (le_n (S O)) | (THead _ t0 t1) \Rightarrow (le_S_n (S O) (S (plus (tweight t0) (tweight t1))) (le_n_S (S O) (S (plus (tweight t0) (tweight t1))) (le_n_S O (plus (tweight t0) (tweight t1)) (le_O_n (plus (tweight t0) (tweight t1))))))]).

theorem clt_cong:
 \forall (c: C).(\forall (d: C).((clt c d) \to (\forall (k: K).(\forall (t: T).(clt (CHead c k t) (CHead d k t))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (H: (lt (cweight c) (cweight d))).(\lambda (_: K).(\lambda (t: T).(lt_le_S (plus (cweight c) (tweight t)) (plus (cweight d) (tweight t)) (plus_lt_compat_r (cweight c) (cweight d) (tweight t) H)))))).

theorem clt_head:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(clt c (CHead c k u))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (u: T).(eq_ind_r nat (plus (cweight c) O) (\lambda (n: nat).(lt n (plus (cweight c) (tweight u)))) (lt_le_S (plus (cweight c) O) (plus (cweight c) (tweight u)) (plus_le_lt_compat (cweight c) (cweight c) O (tweight u) (le_n (cweight c)) (tweight_lt u))) (cweight c) (plus_n_O (cweight c))))).

theorem clt_wf__q_ind:
 \forall (P: ((C \to Prop))).(((\forall (n: nat).((\lambda (P: ((C \to Prop))).(\lambda (n0: nat).(\forall (c: C).((eq nat (cweight c) n0) \to (P c))))) P n))) \to (\forall (c: C).(P c)))
\def
 let Q \def (\lambda (P: ((C \to Prop))).(\lambda (n: nat).(\forall (c: C).((eq nat (cweight c) n) \to (P c))))) in (\lambda (P: ((C \to Prop))).(\lambda (H: ((\forall (n: nat).(\forall (c: C).((eq nat (cweight c) n) \to (P c)))))).(\lambda (c: C).(H (cweight c) c (refl_equal nat (cweight c)))))).

theorem clt_wf_ind:
 \forall (P: ((C \to Prop))).(((\forall (c: C).(((\forall (d: C).((clt d c) \to (P d)))) \to (P c)))) \to (\forall (c: C).(P c)))
\def
 let Q \def (\lambda (P: ((C \to Prop))).(\lambda (n: nat).(\forall (c: C).((eq nat (cweight c) n) \to (P c))))) in (\lambda (P: ((C \to Prop))).(\lambda (H: ((\forall (c: C).(((\forall (d: C).((lt (cweight d) (cweight c)) \to (P d)))) \to (P c))))).(\lambda (c: C).(clt_wf__q_ind (\lambda (c0: C).(P c0)) (\lambda (n: nat).(lt_wf_ind n (Q (\lambda (c0: C).(P c0))) (\lambda (n0: nat).(\lambda (H0: ((\forall (m: nat).((lt m n0) \to (Q (\lambda (c: C).(P c)) m))))).(\lambda (c0: C).(\lambda (H1: (eq nat (cweight c0) n0)).(let H2 \def (eq_ind_r nat n0 (\lambda (n: nat).(\forall (m: nat).((lt m n) \to (\forall (c: C).((eq nat (cweight c) m) \to (P c)))))) H0 (cweight c0) H1) in (H c0 (\lambda (d: C).(\lambda (H3: (lt (cweight d) (cweight c0))).(H2 (cweight d) H3 d (refl_equal nat (cweight d))))))))))))) c)))).

definition CTail:
 K \to (T \to (C \to C))
\def
 let rec CTail (k: K) (t: T) (c: C) on c: C \def (match c with [(CSort n) \Rightarrow (CHead (CSort n) k t) | (CHead d h u) \Rightarrow (CHead (CTail k t d) h u)]) in CTail.

theorem chead_ctail:
 \forall (c: C).(\forall (t: T).(\forall (k: K).(ex_3 K C T (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(eq C (CHead c k t) (CTail h u d))))))))
\def
 \lambda (c: C).(C_ind (\lambda (c0: C).(\forall (t: T).(\forall (k: K).(ex_3 K C T (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(eq C (CHead c0 k t) (CTail h u d))))))))) (\lambda (n: nat).(\lambda (t: T).(\lambda (k: K).(ex_3_intro K C T (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(eq C (CHead (CSort n) k t) (CTail h u d))))) k (CSort n) t (refl_equal C (CHead (CSort n) k t)))))) (\lambda (c0: C).(\lambda (H: ((\forall (t: T).(\forall (k: K).(ex_3 K C T (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(eq C (CHead c0 k t) (CTail h u d)))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (t0: T).(\lambda (k0: K).(let H_x \def (H t k) in (let H0 \def H_x in (ex_3_ind K C T (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(eq C (CHead c0 k t) (CTail h u d))))) (ex_3 K C T (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(eq C (CHead (CHead c0 k t) k0 t0) (CTail h u d)))))) (\lambda (x0: K).(\lambda (x1: C).(\lambda (x2: T).(\lambda (H1: (eq C (CHead c0 k t) (CTail x0 x2 x1))).(eq_ind_r C (CTail x0 x2 x1) (\lambda (c1: C).(ex_3 K C T (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(eq C (CHead c1 k0 t0) (CTail h u d))))))) (ex_3_intro K C T (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(eq C (CHead (CTail x0 x2 x1) k0 t0) (CTail h u d))))) x0 (CHead x1 k0 t0) x2 (refl_equal C (CHead (CTail x0 x2 x1) k0 t0))) (CHead c0 k t) H1))))) H0))))))))) c).

theorem clt_thead:
 \forall (k: K).(\forall (u: T).(\forall (c: C).(clt c (CTail k u c))))
\def
 \lambda (k: K).(\lambda (u: T).(\lambda (c: C).(C_ind (\lambda (c0: C).(clt c0 (CTail k u c0))) (\lambda (n: nat).(clt_head k (CSort n) u)) (\lambda (c0: C).(\lambda (H: (clt c0 (CTail k u c0))).(\lambda (k0: K).(\lambda (t: T).(clt_cong c0 (CTail k u c0) H k0 t))))) c))).

theorem c_tail_ind:
 \forall (P: ((C \to Prop))).(((\forall (n: nat).(P (CSort n)))) \to (((\forall (c: C).((P c) \to (\forall (k: K).(\forall (t: T).(P (CTail k t c))))))) \to (\forall (c: C).(P c))))
\def
 \lambda (P: ((C \to Prop))).(\lambda (H: ((\forall (n: nat).(P (CSort n))))).(\lambda (H0: ((\forall (c: C).((P c) \to (\forall (k: K).(\forall (t: T).(P (CTail k t c)))))))).(\lambda (c: C).(clt_wf_ind (\lambda (c0: C).(P c0)) (\lambda (c0: C).(match c0 return (\lambda (c1: C).(((\forall (d: C).((clt d c1) \to (P d)))) \to (P c1))) with [(CSort n) \Rightarrow (\lambda (_: ((\forall (d: C).((clt d (CSort n)) \to (P d))))).(H n)) | (CHead c1 k t) \Rightarrow (\lambda (H1: ((\forall (d: C).((clt d (CHead c1 k t)) \to (P d))))).(let H_x \def (chead_ctail c1 t k) in (let H2 \def H_x in (ex_3_ind K C T (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(eq C (CHead c1 k t) (CTail h u d))))) (P (CHead c1 k t)) (\lambda (x0: K).(\lambda (x1: C).(\lambda (x2: T).(\lambda (H3: (eq C (CHead c1 k t) (CTail x0 x2 x1))).(eq_ind_r C (CTail x0 x2 x1) (\lambda (c2: C).(P c2)) (let H4 \def (eq_ind C (CHead c1 k t) (\lambda (c: C).(\forall (d: C).((clt d c) \to (P d)))) H1 (CTail x0 x2 x1) H3) in (H0 x1 (H4 x1 (clt_thead x0 x2 x1)) x0 x2)) (CHead c1 k t) H3))))) H2))))])) c)))).

definition fweight:
 C \to (T \to nat)
\def
 \lambda (c: C).(\lambda (t: T).(plus (cweight c) (tweight t))).

definition flt:
 C \to (T \to (C \to (T \to Prop)))
\def
 \lambda (c1: C).(\lambda (t1: T).(\lambda (c2: C).(\lambda (t2: T).(lt (fweight c1 t1) (fweight c2 t2))))).

theorem flt_thead_sx:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).(flt c u c (THead k u t)))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(lt_le_S (plus (cweight c) (tweight u)) (plus (cweight c) (S (plus (tweight u) (tweight t)))) (plus_le_lt_compat (cweight c) (cweight c) (tweight u) (S (plus (tweight u) (tweight t))) (le_n (cweight c)) (le_lt_n_Sm (tweight u) (plus (tweight u) (tweight t)) (le_plus_l (tweight u) (tweight t)))))))).

theorem flt_thead_dx:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).(flt c t c (THead k u t)))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(lt_le_S (plus (cweight c) (tweight t)) (plus (cweight c) (S (plus (tweight u) (tweight t)))) (plus_le_lt_compat (cweight c) (cweight c) (tweight t) (S (plus (tweight u) (tweight t))) (le_n (cweight c)) (le_lt_n_Sm (tweight t) (plus (tweight u) (tweight t)) (le_plus_r (tweight u) (tweight t)))))))).

theorem flt_shift:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).(flt (CHead c k u) t c (THead k u t)))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(eq_ind nat (S (plus (cweight c) (plus (tweight u) (tweight t)))) (\lambda (n: nat).(lt (plus (plus (cweight c) (tweight u)) (tweight t)) n)) (eq_ind_r nat (plus (plus (cweight c) (tweight u)) (tweight t)) (\lambda (n: nat).(lt (plus (plus (cweight c) (tweight u)) (tweight t)) (S n))) (le_n (S (plus (plus (cweight c) (tweight u)) (tweight t)))) (plus (cweight c) (plus (tweight u) (tweight t))) (plus_assoc (cweight c) (tweight u) (tweight t))) (plus (cweight c) (S (plus (tweight u) (tweight t)))) (plus_n_Sm (cweight c) (plus (tweight u) (tweight t))))))).

theorem flt_arith0:
 \forall (k: K).(\forall (c: C).(\forall (t: T).(\forall (i: nat).(flt c t (CHead c k t) (TLRef i)))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (t: T).(\lambda (_: nat).(le_S_n (S (plus (cweight c) (tweight t))) (plus (plus (cweight c) (tweight t)) (S O)) (lt_le_S (S (plus (cweight c) (tweight t))) (S (plus (plus (cweight c) (tweight t)) (S O))) (lt_n_S (plus (cweight c) (tweight t)) (plus (plus (cweight c) (tweight t)) (S O)) (lt_x_plus_x_Sy (plus (cweight c) (tweight t)) O))))))).

theorem flt_arith1:
 \forall (k1: K).(\forall (c1: C).(\forall (c2: C).(\forall (t1: T).((cle (CHead c1 k1 t1) c2) \to (\forall (k2: K).(\forall (t2: T).(\forall (i: nat).(flt c1 t1 (CHead c2 k2 t2) (TLRef i)))))))))
\def
 \lambda (_: K).(\lambda (c1: C).(\lambda (c2: C).(\lambda (t1: T).(\lambda (H: (le (plus (cweight c1) (tweight t1)) (cweight c2))).(\lambda (_: K).(\lambda (t2: T).(\lambda (_: nat).(le_lt_trans (plus (cweight c1) (tweight t1)) (cweight c2) (plus (plus (cweight c2) (tweight t2)) (S O)) H (eq_ind_r nat (plus (S O) (plus (cweight c2) (tweight t2))) (\lambda (n: nat).(lt (cweight c2) n)) (le_lt_n_Sm (cweight c2) (plus (cweight c2) (tweight t2)) (le_plus_l (cweight c2) (tweight t2))) (plus (plus (cweight c2) (tweight t2)) (S O)) (plus_comm (plus (cweight c2) (tweight t2)) (S O))))))))))).

theorem flt_arith2:
 \forall (c1: C).(\forall (c2: C).(\forall (t1: T).(\forall (i: nat).((flt c1 t1 c2 (TLRef i)) \to (\forall (k2: K).(\forall (t2: T).(\forall (j: nat).(flt c1 t1 (CHead c2 k2 t2) (TLRef j)))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (t1: T).(\lambda (_: nat).(\lambda (H: (lt (plus (cweight c1) (tweight t1)) (plus (cweight c2) (S O)))).(\lambda (_: K).(\lambda (t2: T).(\lambda (_: nat).(lt_le_trans (plus (cweight c1) (tweight t1)) (plus (cweight c2) (S O)) (plus (plus (cweight c2) (tweight t2)) (S O)) H (le_S_n (plus (cweight c2) (S O)) (plus (plus (cweight c2) (tweight t2)) (S O)) (lt_le_S (plus (cweight c2) (S O)) (S (plus (plus (cweight c2) (tweight t2)) (S O))) (le_lt_n_Sm (plus (cweight c2) (S O)) (plus (plus (cweight c2) (tweight t2)) (S O)) (plus_le_compat (cweight c2) (plus (cweight c2) (tweight t2)) (S O) (S O) (le_plus_l (cweight c2) (tweight t2)) (le_n (S O)))))))))))))).

theorem flt_wf__q_ind:
 \forall (P: ((C \to (T \to Prop)))).(((\forall (n: nat).((\lambda (P: ((C \to (T \to Prop)))).(\lambda (n0: nat).(\forall (c: C).(\forall (t: T).((eq nat (fweight c t) n0) \to (P c t)))))) P n))) \to (\forall (c: C).(\forall (t: T).(P c t))))
\def
 let Q \def (\lambda (P: ((C \to (T \to Prop)))).(\lambda (n: nat).(\forall (c: C).(\forall (t: T).((eq nat (fweight c t) n) \to (P c t)))))) in (\lambda (P: ((C \to (T \to Prop)))).(\lambda (H: ((\forall (n: nat).(\forall (c: C).(\forall (t: T).((eq nat (fweight c t) n) \to (P c t))))))).(\lambda (c: C).(\lambda (t: T).(H (fweight c t) c t (refl_equal nat (fweight c t))))))).

theorem flt_wf_ind:
 \forall (P: ((C \to (T \to Prop)))).(((\forall (c2: C).(\forall (t2: T).(((\forall (c1: C).(\forall (t1: T).((flt c1 t1 c2 t2) \to (P c1 t1))))) \to (P c2 t2))))) \to (\forall (c: C).(\forall (t: T).(P c t))))
\def
 let Q \def (\lambda (P: ((C \to (T \to Prop)))).(\lambda (n: nat).(\forall (c: C).(\forall (t: T).((eq nat (fweight c t) n) \to (P c t)))))) in (\lambda (P: ((C \to (T \to Prop)))).(\lambda (H: ((\forall (c2: C).(\forall (t2: T).(((\forall (c1: C).(\forall (t1: T).((flt c1 t1 c2 t2) \to (P c1 t1))))) \to (P c2 t2)))))).(\lambda (c: C).(\lambda (t: T).(flt_wf__q_ind P (\lambda (n: nat).(lt_wf_ind n (Q P) (\lambda (n0: nat).(\lambda (H0: ((\forall (m: nat).((lt m n0) \to (Q P m))))).(\lambda (c0: C).(\lambda (t0: T).(\lambda (H1: (eq nat (fweight c0 t0) n0)).(let H2 \def (eq_ind_r nat n0 (\lambda (n: nat).(\forall (m: nat).((lt m n) \to (\forall (c: C).(\forall (t: T).((eq nat (fweight c t) m) \to (P c t))))))) H0 (fweight c0 t0) H1) in (H c0 t0 (\lambda (c1: C).(\lambda (t1: T).(\lambda (H3: (flt c1 t1 c0 t0)).(H2 (fweight c1 t1) H3 c1 t1 (refl_equal nat (fweight c1 t1))))))))))))))) c t))))).
