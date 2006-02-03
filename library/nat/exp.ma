(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

set "baseuri" "cic:/matita/nat/exp".

include "nat/div_and_mod.ma".

let rec exp n m on m\def 
 match m with 
 [ O \Rightarrow (S O)
 | (S p) \Rightarrow (times n (exp n p)) ].

interpretation "natural exponent" 'exp a b = (cic:/matita/nat/exp/exp.con a b).

theorem exp_plus_times : \forall n,p,q:nat. 
n \sup (p + q) = (n \sup p) * (n \sup q).
intros.elim p.
simplify.rewrite < plus_n_O.reflexivity.
simplify.rewrite > H.symmetry.
apply assoc_times.
qed.

theorem exp_n_O : \forall n:nat. S O = n \sup O.
intro.simplify.reflexivity.
qed.

theorem exp_n_SO : \forall n:nat. n = n \sup (S O).
intro.simplify.rewrite < times_n_SO.reflexivity.
qed.

theorem exp_exp_times : \forall n,p,q:nat. 
(n \sup p) \sup q = n \sup (p * q).
intros.
elim q.simplify.rewrite < times_n_O.simplify.reflexivity.
simplify.rewrite > H.rewrite < exp_plus_times.
rewrite < times_n_Sm.reflexivity.
qed.

theorem lt_O_exp: \forall n,m:nat. O < n \to O < n \sup m. 
intros.elim m.simplify.unfold lt.apply le_n.
simplify.unfold lt.rewrite > times_n_SO.
apply le_times.assumption.assumption.
qed.

theorem lt_m_exp_nm: \forall n,m:nat. (S O) < n \to m < n \sup m.
intros.elim m.simplify.unfold lt.reflexivity.
simplify.unfold lt.
apply (trans_le ? ((S(S O))*(S n1))).
simplify.
rewrite < plus_n_Sm.apply le_S_S.apply le_S_S.
rewrite < sym_plus.
apply le_plus_n.
apply le_times.assumption.assumption.
qed.

theorem exp_to_eq_O: \forall n,m:nat. (S O) < n 
\to n \sup m = (S O) \to m = O.
intros.apply antisym_le.apply le_S_S_to_le.
rewrite < H1.change with (m < n \sup m).
apply lt_m_exp_nm.assumption.
apply le_O_n.
qed.

theorem injective_exp_r: \forall n:nat. (S O) < n \to 
injective nat nat (\lambda m:nat. n \sup m).
simplify.intros 4.
apply (nat_elim2 (\lambda x,y.n \sup x = n \sup y \to x = y)).
intros.apply sym_eq.apply (exp_to_eq_O n).assumption.
rewrite < H1.reflexivity.
intros.apply (exp_to_eq_O n).assumption.assumption.
intros.apply eq_f.
apply H1.
(* esprimere inj_times senza S *)
cut (\forall a,b:nat.O < n \to n*a=n*b \to a=b).
apply Hcut.simplify.unfold lt.apply le_S_S_to_le. apply le_S. assumption.
assumption.
intros 2.
apply (nat_case n).
intros.apply False_ind.apply (not_le_Sn_O O H3).
intros.
apply (inj_times_r m1).assumption.
qed.

variant inj_exp_r: \forall p:nat. (S O) < p \to \forall n,m:nat.
p \sup n = p \sup m \to n = m \def
injective_exp_r.
