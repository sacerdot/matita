(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        Matita is distributed under the terms of the          *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "nat/relevant_equations.ma".
include "nat/primes.ma".

definition S_mod: nat \to nat \to nat \def
\lambda n,m:nat. (S m) \mod n.

definition congruent: nat \to nat \to nat \to Prop \def
\lambda n,m,p:nat. mod n p = mod m p.

interpretation "congruent" 'congruent n m p = (congruent n m p).

theorem congruent_n_n: \forall n,p:nat.congruent n n p.
intros.unfold congruent.reflexivity.
qed.

theorem transitive_congruent: \forall p:nat. transitive nat 
(\lambda n,m. congruent n m p).
intros.unfold transitive.unfold congruent.intros.
whd.apply (trans_eq ? ? (y \mod p)).
apply H.apply H1.
qed.

theorem le_to_mod: \forall n,m:nat. n \lt m \to n = n \mod m.
intros.
apply (div_mod_spec_to_eq2 n m O n (n/m) (n \mod m)).
constructor 1.assumption.simplify.reflexivity.
apply div_mod_spec_div_mod.
apply (le_to_lt_to_lt O n m).apply le_O_n.assumption.
qed.

theorem mod_mod : \forall n,p:nat. O<p \to n \mod p = (n \mod p) \mod p.
intros.
rewrite > (div_mod (n \mod p) p) in \vdash (? ? % ?).
rewrite > (eq_div_O ? p).reflexivity.
(* uffa: hint non lo trova lt vs. le*)
apply lt_mod_m_m.
assumption.
assumption.
qed.

theorem mod_times_mod : \forall n,m,p:nat. O<p \to O<m \to n \mod p = (n \mod (m*p)) \mod p.
intros.
apply (div_mod_spec_to_eq2 n p (n/p) (n \mod p) 
(n/(m*p)*m + (n \mod (m*p)/p))).
apply div_mod_spec_div_mod.assumption.
constructor 1.
apply lt_mod_m_m.assumption.
rewrite > times_plus_l.
rewrite > assoc_plus.
rewrite < div_mod.
rewrite > assoc_times.
rewrite < div_mod.
reflexivity.
rewrite > (times_n_O O).
apply lt_times.
assumption.assumption.assumption.
qed.

theorem congruent_n_mod_n : 
\forall n,p:nat. O < p \to congruent n (n \mod p) p.
intros.unfold congruent.
apply mod_mod.assumption.
qed.

theorem congruent_n_mod_times : 
\forall n,m,p:nat. O < p \to O < m \to congruent n (n \mod (m*p)) p.
intros.unfold congruent.
apply mod_times_mod.assumption.assumption.
qed.

theorem eq_times_plus_to_congruent: \forall n,m,p,r:nat. O< p \to 
n = r*p+m \to congruent n m p.
intros.unfold congruent.
apply (div_mod_spec_to_eq2 n p (div n p) (mod n p) (r +(div m p)) (mod m p)).
apply div_mod_spec_div_mod.assumption.
constructor 1.
apply lt_mod_m_m.assumption.
(*cut (n = r * p + (m / p * p + m \mod p)).*)
(*lapply (div_mod m p H). 
rewrite > sym_times.
rewrite > distr_times_plus.
(*rewrite > (sym_times p (m/p)).*)
(*rewrite > sym_times.*)
rewrite > assoc_plus.
autobatch paramodulation.
rewrite < div_mod.
assumption.
assumption.
*)
rewrite > sym_times.
rewrite > distr_times_plus.
rewrite > sym_times.
rewrite > (sym_times p).
rewrite > assoc_plus.
rewrite < div_mod.
assumption.assumption.
qed.

theorem divides_to_congruent: \forall n,m,p:nat. O < p \to m \le n \to 
divides p (n - m) \to congruent n m p.
intros.elim H2.
apply (eq_times_plus_to_congruent n m p n1).
assumption.
rewrite < sym_plus.
apply minus_to_plus.assumption.
rewrite > sym_times. assumption.
qed.

theorem congruent_to_divides: \forall n,m,p:nat.
O < p \to congruent n m p \to divides p (n - m).
intros.unfold congruent in H1.
apply (witness ? ? ((n / p)-(m / p))).
rewrite > sym_times.
rewrite > (div_mod n p) in \vdash (? ? % ?).
rewrite > (div_mod m p) in \vdash (? ? % ?).
rewrite < (sym_plus (m \mod p)).
rewrite < H1.
rewrite < (eq_minus_minus_minus_plus ? (n \mod p)).
rewrite < minus_plus_m_m.
apply sym_eq.
apply times_minus_l.
assumption.assumption.
qed.

theorem mod_times: \forall n,m,p:nat. 
O < p \to mod (n*m) p = mod ((mod n p)*(mod m p)) p.
intros.
change with (congruent (n*m) ((mod n p)*(mod m p)) p).
apply (eq_times_plus_to_congruent ? ? p 
((n / p)*p*(m / p) + (n / p)*(m \mod p) + (n \mod p)*(m / p))).
assumption.
apply (trans_eq ? ? (((n/p)*p+(n \mod p))*((m/p)*p+(m \mod p)))).
apply eq_f2.
apply div_mod.assumption.
apply div_mod.assumption.
apply (trans_eq ? ? (((n/p)*p)*((m/p)*p) + (n/p)*p*(m \mod p) +
(n \mod p)*((m / p)*p) + (n \mod p)*(m \mod p))).
apply times_plus_plus.
apply eq_f2.
rewrite < assoc_times.
rewrite > (assoc_times (n/p) p (m \mod p)).
rewrite > (sym_times p (m \mod p)).
rewrite < (assoc_times (n/p) (m \mod p) p).
rewrite < times_plus_l.
rewrite < (assoc_times (n \mod p)).
rewrite < times_plus_l.
apply eq_f2.
apply eq_f2.reflexivity.
reflexivity.reflexivity.
reflexivity.
qed.

theorem congruent_times: \forall n,m,n1,m1,p. O < p \to congruent n n1 p \to 
congruent m m1 p \to congruent (n*m) (n1*m1) p.
unfold congruent. 
intros. 
rewrite > (mod_times n m p H).
rewrite > H1.
rewrite > H2.
apply sym_eq.
apply mod_times.assumption.
qed.

theorem congruent_pi: \forall f:nat \to nat. \forall n,m,p:nat.O < p \to
congruent (pi n f m) (pi n (\lambda m. mod (f m) p) m) p.
intros.
elim n. simplify.
apply congruent_n_mod_n.assumption.
simplify.
apply congruent_times.
assumption.
apply congruent_n_mod_n.assumption.
assumption.
qed.
