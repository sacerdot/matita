
(**************************************************************************)
(*       __                                                               *)
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

include "nat/plus.ma".

let rec times n m \def 
 match n with 
 [ O \Rightarrow O
 | (S p) \Rightarrow m+(times p m) ].

interpretation "natural times" 'times x y = (times x y).

theorem times_Sn_m:
\forall n,m:nat. m+n*m = S n*m.
intros. reflexivity.
qed.

theorem times_n_O: \forall n:nat. O = n*O.
intros.elim n.
simplify.reflexivity.
simplify.assumption.
qed.

theorem times_n_Sm : 
\forall n,m:nat. n+(n*m) = n*(S m).
intros.elim n.
simplify.reflexivity.
simplify.
demodulate all.
(*
apply eq_f.rewrite < H.
transitivity ((n1+m)+n1*m).symmetry.apply assoc_plus.
transitivity ((m+n1)+n1*m).
apply eq_f2.
apply sym_plus.
reflexivity.
apply assoc_plus.
*)
qed.

theorem times_O_to_O: \forall n,m:nat.n*m = O \to n = O \lor m= O.
apply nat_elim2;intros
  [left.reflexivity
  |right.reflexivity
  |apply False_ind.
   simplify in H1.
   apply (not_eq_O_S ? (sym_eq  ? ? ? H1))
  ]
qed.

theorem times_n_SO : \forall n:nat. n = n * S O.
intros. demodulate. reflexivity. (*
rewrite < times_n_Sm.
rewrite < times_n_O.
rewrite < plus_n_O.
reflexivity.*)
qed.

theorem times_SSO_n : \forall n:nat. n + n = S (S O) * n.
intros.
simplify.
rewrite < plus_n_O.
reflexivity.
qed.

alias num (instance 0) = "natural number".
lemma times_SSO: \forall n.2*(S n) = S(S(2*n)).
intro.simplify.rewrite < plus_n_Sm.reflexivity.
qed.

theorem or_eq_eq_S: \forall n.\exists m. 
n = (S(S O))*m \lor n = S ((S(S O))*m).
intro.elim n
  [apply (ex_intro ? ? O).
   left.reflexivity
  |elim H.elim H1
    [apply (ex_intro ? ? a).
     right.apply eq_f.assumption
    |apply (ex_intro ? ? (S a)).
     left.rewrite > H2.
     apply sym_eq.
     apply times_SSO
    ]
  ]
qed.

theorem symmetric_times : symmetric nat times. 
unfold symmetric.
intros.elim x;
 [ simplify. apply times_n_O.
 | demodulate. reflexivity. (*
(* applyS times_n_Sm. *) 
simplify.rewrite > H.apply times_n_Sm.*)]
qed.

variant sym_times : \forall n,m:nat. n*m = m*n \def
symmetric_times.

theorem distributive_times_plus : distributive nat times plus.
unfold distributive.
intros.elim x.
simplify.reflexivity.
simplify.
demodulate all.
(*
rewrite > H. rewrite > assoc_plus.rewrite > assoc_plus.
apply eq_f.rewrite < assoc_plus. rewrite < (sym_plus ? z).
rewrite > assoc_plus.reflexivity. *)
qed.

variant distr_times_plus: \forall n,m,p:nat. n*(m+p) = n*m + n*p
\def distributive_times_plus.

theorem associative_times: associative nat times.
unfold associative.
intros.
elim x. simplify.apply refl_eq. 
simplify.
demodulate all.
(*
rewrite < sym_times.
rewrite > distr_times_plus.
rewrite < sym_times.
rewrite < (sym_times (times n y) z).
rewrite < H.apply refl_eq.
*)
qed.

variant assoc_times: \forall n,m,p:nat. (n*m)*p = n*(m*p) \def
associative_times.

lemma times_times: ∀x,y,z. x*(y*z) = y*(x*z).
intros. 
demodulate. reflexivity.
(* autobatch paramodulation. *)
qed.

