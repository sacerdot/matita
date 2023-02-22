(**************************************************************************)
(*       ___	                                                          *)
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

include "nat/exp.ma".
include "nat/gcd.ma".
include "nat/permutation.ma".
include "nat/congruence.ma".

theorem and_congruent_congruent: \forall m,n,a,b:nat. O < n \to O < m \to 
gcd n m = (S O) \to ex nat (\lambda x. congruent x a m \land congruent x b n).
intros.
cut (\exists c,d.c*n - d*m = (S O) \lor d*m - c*n = (S O)).
elim Hcut.elim H3.elim H4.
apply (ex_intro nat ? ((a+b*m)*a1*n-b*a2*m)).
split.
(* congruent to a *)
cut (a1*n = a2*m + (S O)).
rewrite > assoc_times.
rewrite > Hcut1.
rewrite < (sym_plus ? (a2*m)).
rewrite > distr_times_plus.
rewrite < times_n_SO.
rewrite > assoc_plus.
rewrite < assoc_times.
rewrite < times_plus_l.
rewrite > eq_minus_plus_plus_minus.
rewrite < times_minus_l.
rewrite > sym_plus.
apply (eq_times_plus_to_congruent ? ? ? ((b+(a+b*m)*a2)-b*a2)).
assumption.reflexivity.
apply le_times_l.
apply (trans_le ? ((a+b*m)*a2)).
apply le_times_l.
apply (trans_le ? (b*m)).
rewrite > times_n_SO in \vdash (? % ?).
apply le_times_r.assumption.
apply le_plus_n.
apply le_plus_n.
apply minus_to_plus.
apply lt_to_le.
change with (O + a2*m < a1*n).
apply lt_minus_to_plus.
rewrite > H5.unfold lt.apply le_n.
assumption.
(* congruent to b *)
cut (a2*m = a1*n - (S O)).
rewrite > (assoc_times b a2).
rewrite > Hcut1.
rewrite > distr_times_minus.
rewrite < assoc_times.
rewrite < eq_plus_minus_minus_minus.
rewrite < times_n_SO.
rewrite < times_minus_l.
rewrite < sym_plus.
apply (eq_times_plus_to_congruent ? ? ? ((a+b*m)*a1-b*a1)).
assumption.reflexivity.
rewrite > assoc_times.
apply le_times_r.
apply (trans_le ? (a1*n - a2*m)).
rewrite > H5.apply le_n.
apply (le_minus_m ? (a2*m)).
apply le_times_l.
apply le_times_l.
apply (trans_le ? (b*m)).
rewrite > times_n_SO in \vdash (? % ?).
apply le_times_r.assumption.
apply le_plus_n.
apply sym_eq. apply plus_to_minus.
rewrite > sym_plus.
apply minus_to_plus.
apply lt_to_le.
change with (O + a2*m < a1*n).
apply lt_minus_to_plus.
rewrite > H5.unfold lt.apply le_n.
assumption.
(* and now the symmetric case; the price to pay for working
   in nat instead than Z *)
apply (ex_intro nat ? ((b+a*n)*a2*m-a*a1*n)).
split.
(* congruent to a *)
cut (a1*n = a2*m - (S O)).
rewrite > (assoc_times a a1).
rewrite > Hcut1.
rewrite > distr_times_minus.
rewrite < assoc_times.
rewrite < eq_plus_minus_minus_minus.
rewrite < times_n_SO.
rewrite < times_minus_l.
rewrite < sym_plus.
apply (eq_times_plus_to_congruent ? ? ? ((b+a*n)*a2-a*a2)).
assumption.reflexivity.
rewrite > assoc_times.
apply le_times_r.
apply (trans_le ? (a2*m - a1*n)).
rewrite > H5.apply le_n.
apply (le_minus_m ? (a1*n)).
rewrite > assoc_times.rewrite > assoc_times.
apply le_times_l.
apply (trans_le ? (a*n)).
rewrite > times_n_SO in \vdash (? % ?).
apply le_times_r.assumption.
apply le_plus_n.
apply sym_eq.apply plus_to_minus.
rewrite > sym_plus.
apply minus_to_plus.
apply lt_to_le.
change with (O + a1*n < a2*m).
apply lt_minus_to_plus.
rewrite > H5.unfold lt.apply le_n.
assumption.
(* congruent to a *)
cut (a2*m = a1*n + (S O)).
rewrite > assoc_times.
rewrite > Hcut1.
rewrite > (sym_plus (a1*n)).
rewrite > distr_times_plus.
rewrite < times_n_SO.
rewrite < assoc_times.
rewrite > assoc_plus.
rewrite < times_plus_l.
rewrite > eq_minus_plus_plus_minus.
rewrite < times_minus_l.
rewrite > sym_plus.
apply (eq_times_plus_to_congruent ? ? ? ((a+(b+a*n)*a1)-a*a1)).
assumption.reflexivity.
apply le_times_l.
apply (trans_le ? ((b+a*n)*a1)).
apply le_times_l.
apply (trans_le ? (a*n)).
rewrite > times_n_SO in \vdash (? % ?).
apply le_times_r.
assumption.
apply le_plus_n.
apply le_plus_n.
apply minus_to_plus.
apply lt_to_le.
change with (O + a1*n < a2*m).
apply lt_minus_to_plus.
rewrite > H5.unfold lt.apply le_n.
assumption.
(* proof of the cut *)
rewrite < H2.
apply eq_minus_gcd.
qed.

theorem and_congruent_congruent_lt: \forall m,n,a,b:nat. O < n \to O < m \to 
gcd n m = (S O) \to 
ex nat (\lambda x. (congruent x a m \land congruent x b n) \land
 (x < m*n)).
intros.elim (and_congruent_congruent m n a b).
elim H3.
apply (ex_intro ? ? (a1 \mod (m*n))).
split.split.
apply (transitive_congruent m ? a1).
unfold congruent.
apply sym_eq.
change with (congruent a1 (a1 \mod (m*n)) m).
rewrite < sym_times.
apply congruent_n_mod_times.
assumption.assumption.assumption.
apply (transitive_congruent n ? a1).
unfold congruent.
apply sym_eq.
change with (congruent a1 (a1 \mod (m*n)) n).
apply congruent_n_mod_times.
assumption.assumption.assumption.
apply lt_mod_m_m.
rewrite > (times_n_O O).
apply lt_times.assumption.assumption.
assumption.assumption.assumption.
qed.

definition cr_pair : nat \to nat \to nat \to nat \to nat \def
\lambda n,m,a,b. 
min (pred (n*m)) (\lambda x. andb (eqb (x \mod n) a) (eqb (x \mod m) b)).

theorem cr_pair1: cr_pair (S (S O)) (S (S (S O))) O O = O.
reflexivity.
qed.

theorem cr_pair2: cr_pair (S(S O)) (S(S(S O))) (S O) O = (S(S(S O))).
simplify.
reflexivity.
qed.

theorem cr_pair3: cr_pair (S(S O)) (S(S(S O))) (S O) (S(S O)) = (S(S(S(S(S O))))).
reflexivity.
qed.

theorem cr_pair4: cr_pair (S(S(S(S(S O))))) (S(S(S(S(S(S(S O))))))) (S(S(S O))) (S(S O)) = 
(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S O))))))))))))))))))))))).
reflexivity.
qed.

theorem mod_cr_pair : \forall m,n,a,b. a \lt m \to b \lt n \to 
gcd n m = (S O) \to 
(cr_pair m n a b) \mod m = a \land (cr_pair m n a b) \mod n = b.
intros.
cut (andb (eqb ((cr_pair m n a b) \mod m) a) 
         (eqb ((cr_pair m n a b) \mod n) b) = true).
generalize in match Hcut.
apply andb_elim.
apply eqb_elim.intro.
rewrite > H3.
simplify.
intro.split.reflexivity.
apply eqb_true_to_eq.assumption.
intro.
simplify.
intro.apply False_ind.
apply not_eq_true_false.apply sym_eq.assumption.
apply (f_min_aux_true 
(\lambda x. andb (eqb (x \mod m) a) (eqb (x \mod n) b)) (pred (m*n)) O).
elim (and_congruent_congruent_lt m n a b).
apply (ex_intro ? ? a1).split.split.
apply le_O_n.
elim H3.apply le_S_S_to_le.apply (trans_le ? (m*n)).
assumption.apply (nat_case (m*n)).apply le_O_n.
intro.
rewrite < pred_Sn.
rewrite < plus_n_O.apply le_n.
elim H3.elim H4.
apply andb_elim.
cut (a1 \mod m = a).
cut (a1 \mod n = b).
rewrite > (eq_to_eqb_true ? ? Hcut).
rewrite > (eq_to_eqb_true ? ? Hcut1).
simplify.reflexivity.
rewrite < (lt_to_eq_mod b n).assumption.
assumption.
rewrite < (lt_to_eq_mod a m).assumption.
assumption.
apply (le_to_lt_to_lt ? b).apply le_O_n.assumption.
apply (le_to_lt_to_lt ? a).apply le_O_n.assumption.
assumption.
qed.