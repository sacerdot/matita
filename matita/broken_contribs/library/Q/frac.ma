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

include "Q/q/qinv.ma".

(*
let rec nat_fact_to_fraction_inv l \def
  match l with
  [nf_last a \Rightarrow nn a
  |nf_cons a p \Rightarrow 
    cons (neg_Z_of_nat a) (nat_fact_to_fraction_inv p)
  ]
.

definition nat_fact_all_to_Q_inv \def
\lambda n.
  match n with
  [nfa_zero \Rightarrow OQ
  |nfa_one \Rightarrow Qpos one
  |nfa_proper l \Rightarrow Qpos (frac (nat_fact_to_fraction_inv l))
  ]
.

definition nat_to_Q_inv \def
\lambda n. nat_fact_all_to_Q_inv (factorize n).

definition frac:nat \to nat \to Q \def
\lambda p,q. Qtimes (nat_to_Q p) (Qinv (nat_to_Q q)).

theorem Qtimes_frac_frac: \forall p,q,r,s.
Qtimes (frac p q) (frac r s) = (frac (p*r) (q*s)).
intros.
unfold frac.
rewrite > associative_Qtimes.
rewrite < associative_Qtimes in ⊢ (? ? (? ? %) ?).
rewrite > symmetric_Qtimes in ⊢ (? ? (? ? (? % ?)) ?).
rewrite > associative_Qtimes in ⊢ (? ? (? ? %) ?).
rewrite < associative_Qtimes.
rewrite < times_Qtimes.
rewrite < Qinv_Qtimes'.
rewrite < times_Qtimes.
reflexivity.
qed.
*)

(*     
definition numQ:Q \to Z \def
\lambda q. 
match q with
[OQ \Rightarrow OZ
|Qpos r \Rightarrow Z_of_nat (defactorize (numeratorQ (Qpos r)))
|Qneg r \Rightarrow neg_Z_of_nat (defactorize (numeratorQ (Qpos r)))
].
*)

definition numQ:Q \to nat \def
\lambda q. defactorize (numeratorQ q).

definition denomQ:Q \to nat \def
\lambda q. defactorize (numeratorQ (Qinv q)).

(*CSC
theorem frac_numQ_denomQ1: \forall r:ratio. 
frac (numQ (Qpos r)) (denomQ (Qpos r)) = (Qpos r).
intro.
unfold frac.unfold denomQ.unfold numQ.
unfold nat_to_Q.
rewrite > factorize_defactorize.
rewrite > factorize_defactorize.
elim r
  [reflexivity
  |elim f
    [reflexivity
    |reflexivity
    |apply Qtimes_numerator_denominator.
    ]
  ]
qed.*)

(*CSC
theorem frac_numQ_denomQ2: \forall r:ratio. 
frac (numQ (Qneg r)) (denomQ (Qneg r)) = (Qpos r).
intro.
unfold frac.unfold denomQ.unfold numQ.
unfold nat_to_Q.
rewrite > factorize_defactorize.
rewrite > factorize_defactorize.
elim r
  [reflexivity
  |elim f
    [reflexivity
    |reflexivity
    |apply Qtimes_numerator_denominator.
    ]
  ]
qed.*)

definition Qabs:Q \to Q \def \lambda q.
match q with
[OQ \Rightarrow OQ
|Qpos q \Rightarrow Qpos q
|Qneg q \Rightarrow Qpos q
].
(*CSC
theorem frac_numQ_denomQ: \forall q. 
frac (numQ q) (denomQ q) = (Qabs q).
intros.
cases q
  [reflexivity
  |simplify in ⊢ (? ? ? %).apply frac_numQ_denomQ1
  |simplify in ⊢ (? ? ? %).apply frac_numQ_denomQ2
  ]
qed.*)
(*CSC
definition Qfrac: Z \to nat \to Q \def
\lambda z,n.match z with
[OZ \Rightarrow OQ
|Zpos m \Rightarrow (frac (S m) n)
|Zneg m \Rightarrow Qopp (frac (S m) n)
].

definition QnumZ \def \lambda q.
match q with
[OQ \Rightarrow OZ
|Qpos r \Rightarrow Z_of_nat (numQ (Qpos r))
|Qneg r \Rightarrow neg_Z_of_nat (numQ (Qpos r))
].

theorem Qfrac_Z_of_nat: \forall n,m.
Qfrac (Z_of_nat n) m = frac n m.
intros.cases n;reflexivity.
qed.

theorem Qfrac_neg_Z_of_nat: \forall n,m.
Qfrac (neg_Z_of_nat n) m = Qopp (frac n m).
intros.cases n;reflexivity.
qed.

theorem Qfrac_QnumZ_denomQ: \forall q. 
Qfrac (QnumZ q) (denomQ q) = q.
intros.
cases q
  [reflexivity
  |change with
    (Qfrac (Z_of_nat (numQ (Qpos r))) (denomQ (Qpos r))=Qpos r).
   rewrite > Qfrac_Z_of_nat.
   apply frac_numQ_denomQ1.
  |simplify in ⊢ (? ? ? %).apply frac_numQ_denomQ2
  ]
qed.
*)
