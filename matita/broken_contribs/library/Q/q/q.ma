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

include "Q/ratio/ratio.ma".
include "Q/fraction/numerator_denominator.ma".

(* a rational number is either O or a ratio with a sign *)
inductive Q : Set \def 
    OQ : Q
  | Qpos : ratio  \to Q
  | Qneg : ratio  \to Q.

interpretation "Rationals" 'Q = Q.

definition Qone ≝ Qpos one.

definition Qopp ≝
 λq.
  match q with
   [ OQ ⇒ OQ
   | Qpos r ⇒ Qneg r
   | Qneg r ⇒ Qpos r
   ].

definition nat_fact_all_to_Q \def
\lambda n.
  match n with
  [nfa_zero \Rightarrow OQ
  |nfa_one \Rightarrow Qpos one
  |nfa_proper l \Rightarrow Qpos (frac (nat_fact_to_fraction l))
  ].

definition nat_to_Q ≝ λn.nat_fact_all_to_Q (factorize n).

definition Z_to_Q ≝
 λz.
  match z with
   [ OZ ⇒ OQ
   | pos n ⇒ nat_to_Q (S n)
   | neg n ⇒ Qopp (nat_to_Q (S n))
   ].

definition numeratorQ \def
\lambda q.match q with
  [OQ \Rightarrow nfa_zero
  |Qpos r \Rightarrow 
    match r with 
    [one \Rightarrow nfa_one
    |frac x \Rightarrow numerator x
    ]
  |Qneg r \Rightarrow 
    match r with 
    [one \Rightarrow nfa_one
    |frac x \Rightarrow numerator x
    ]
  ].

theorem numeratorQ_nat_fact_all_to_Q: \forall g.
numeratorQ (nat_fact_all_to_Q g) = g.
intro.cases g
  [reflexivity
  |reflexivity
  |apply numerator_nat_fact_to_fraction
  ]
qed.
