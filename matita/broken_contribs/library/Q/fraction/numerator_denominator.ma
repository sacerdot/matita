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

include "Q/fraction/finv.ma".

(* returns the numerator of a fraction in the form of a nat_fact_all *)
let rec numerator f \def
  match f with
  [pp a \Rightarrow nfa_proper (nf_last a)
  |nn a \Rightarrow nfa_one
  |cons a l \Rightarrow
    let n \def numerator l in
    match n with
    [nfa_zero \Rightarrow (* this case is vacuous *) nfa_zero
    |nfa_one  \Rightarrow
      match a with 
      [OZ \Rightarrow nfa_one
      |pos x \Rightarrow nfa_proper (nf_last x)
      |neg x \Rightarrow nfa_one
      ]
    |nfa_proper g \Rightarrow
      match a with 
      [OZ \Rightarrow nfa_proper (nf_cons O g)
      |pos x \Rightarrow nfa_proper (nf_cons (S x) g)
      |neg x \Rightarrow nfa_proper (nf_cons O g)
      ]]].

definition denominator ≝ λf.numerator (finv f).

theorem not_eq_numerator_nfa_zero: ∀f.numerator f ≠ nfa_zero.
intro.elim f
  [simplify.intro.destruct H
  |simplify.intro.destruct H
  |simplify.generalize in match H.
   cases (numerator f1)
    [intro.elim H1.reflexivity
    |simplify.intro.
     cases z;simplify;intro;destruct H2
    |simplify.intro.
     cases z;simplify;intro;destruct H2]]
qed.

theorem not_eq_denominator_nfa_zero: ∀f.denominator f ≠ nfa_zero.
 unfold denominator; intro; apply not_eq_numerator_nfa_zero.
qed.

theorem numerator_nat_fact_to_fraction: ∀g:nat_fact. 
numerator (nat_fact_to_fraction g) = nfa_proper g.
intro.
elim g
  [simplify.reflexivity.
  |simplify.rewrite > H.simplify.
   cases n;reflexivity
  ]
qed.

theorem denominator_nat_fact_to_fraction: ∀g:nat_fact.
denominator (finv (nat_fact_to_fraction g)) = nfa_proper g.
 unfold denominator;
 intro;
 rewrite > finv_finv;
 apply numerator_nat_fact_to_fraction.
qed.

theorem or_numerator_nfa_one_nfa_proper: 
∀f.
 (numerator f = nfa_one ∧ ∃g.denominator f = nfa_proper g) ∨
 ∃g.numerator f = nfa_proper g.
intro.elim f
  [simplify.right.
   apply (ex_intro ? ? (nf_last n)).reflexivity
  |simplify.left.split
    [reflexivity
    |apply (ex_intro ? ? (nf_last n)).reflexivity
    ]
  |elim H;clear H
    [elim H1.clear H1.
     elim H2.clear H2.
     elim z
      [simplify.
       rewrite > H.rewrite > H1.simplify.
       left.split
        [reflexivity
        |apply (ex_intro ? ? (nf_cons O a)).reflexivity
        ]
      |simplify.
       rewrite > H.rewrite > H1.simplify.
       right.apply (ex_intro ? ? (nf_last n)).reflexivity
      |simplify.
       rewrite > H.rewrite > H1.simplify.
       left.split
        [reflexivity
        |apply (ex_intro ? ? (nf_cons (S n) a)).reflexivity
        ]
      ]
    |elim H1.clear H1.
      elim z
      [simplify.
       rewrite > H.simplify.
       right.
       apply (ex_intro ? ? (nf_cons O a)).reflexivity
      |simplify.
       rewrite > H.simplify.
       right.apply (ex_intro ? ? (nf_cons (S n) a)).reflexivity
      |simplify.
       rewrite > H.simplify.
       right.
       apply (ex_intro ? ? (nf_cons O a)).reflexivity
      ]
    ]
  ]
qed.
  
theorem eq_nfa_one_to_eq_finv_nfa_proper: 
∀f.numerator f = nfa_one → ∃h.denominator f = nfa_proper h.
  intros;
  elim (or_numerator_nfa_one_nfa_proper f); cases H1;
   [ assumption
   | rewrite > H in H2;
     destruct]
qed.