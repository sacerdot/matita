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

include "nat/factorization.ma".

let rec times_f h g \def
  match h with
  [nf_last a \Rightarrow 
    match g with
    [nf_last b \Rightarrow nf_last (S (a+b))
    |nf_cons b g1 \Rightarrow nf_cons (S (a+b)) g1
    ]
  |nf_cons a h1 \Rightarrow 
    match g with
    [nf_last b \Rightarrow nf_cons (S (a+b)) h1
    |nf_cons b g1 \Rightarrow nf_cons (a+b) (times_f h1 g1)
    ]].

theorem eq_times_f_times1:\forall g,h,m. defactorize_aux (times_f g h) m
=defactorize_aux g m*defactorize_aux h m.
intro.elim g
  [elim h;simplify;autobatch;
  |elim h
    [simplify;autobatch
    |simplify.rewrite > (H n3 (S m)).autobatch
    ]]
qed.


(******************* times_fa *********************)

definition times_fa \def 
\lambda f,g.
match f with
[nfa_zero \Rightarrow nfa_zero
|nfa_one \Rightarrow g
|nfa_proper f1 \Rightarrow match g with
  [nfa_zero \Rightarrow nfa_zero
  |nfa_one \Rightarrow nfa_proper f1
  |nfa_proper g1 \Rightarrow nfa_proper (times_f f1 g1)
  ]].

theorem eq_times_fa_times: \forall f,g.
defactorize (times_fa f g) = defactorize f*defactorize g.
intros.
elim f
  [reflexivity
  |simplify.apply plus_n_O
  |elim g;simplify
    [apply times_n_O
    |apply times_n_SO
    |apply eq_times_f_times1
    ]]
qed.

theorem eq_times_times_fa: \forall n,m.
factorize (n*m) = times_fa (factorize n) (factorize m).
intros.
rewrite <(factorize_defactorize (times_fa (factorize n) (factorize m))).
rewrite > eq_times_fa_times.
rewrite > defactorize_factorize.
rewrite > defactorize_factorize.
reflexivity.
qed.