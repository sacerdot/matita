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

include "Z/compare.ma".
include "nat/factorization.ma".

(* a fraction is a list of Z-coefficients for primes, in natural
order. The last coefficient must eventually be different from 0 *)

inductive fraction : Set \def
  pp : nat \to fraction
| nn: nat \to fraction
| cons : Z \to fraction \to fraction.

let rec nat_fact_to_fraction n ≝
 match n with
  [ nf_last m ⇒ pp m
  | nf_cons m l ⇒ cons (Z_of_nat m) (nat_fact_to_fraction l)
  ].

(* double elimination principles *)
theorem fraction_elim2:
\forall R:fraction \to fraction \to Prop.
(\forall n:nat.\forall g:fraction.R (pp n) g) \to
(\forall n:nat.\forall g:fraction.R (nn n) g) \to
(\forall x:Z.\forall f:fraction.\forall m:nat.R (cons x f) (pp m)) \to
(\forall x:Z.\forall f:fraction.\forall m:nat.R (cons x f) (nn m)) \to
(\forall x,y:Z.\forall f,g:fraction.R f g \to R (cons x f) (cons y g)) \to
\forall f,g:fraction. R f g.
intros 7.elim f.
  apply H.
  apply H1.
  elim g.
    apply H2.
    apply H3.
    apply H4.apply H5.
qed. 

(* boolean equality *)
let rec eqfb f g \def
match f with
[ (pp n) \Rightarrow 
  match g with 
  [ (pp m) \Rightarrow eqb n m
  | (nn m) \Rightarrow false
  | (cons y g1) \Rightarrow false]
| (nn n) \Rightarrow 
  match g with 
  [ (pp m) \Rightarrow false
  | (nn m) \Rightarrow eqb n m
  | (cons y g1) \Rightarrow false] 
| (cons x f1) \Rightarrow 
  match g with 
  [ (pp m) \Rightarrow false
  | (nn m) \Rightarrow false
  | (cons y g1) \Rightarrow andb (eqZb x y) (eqfb f1 g1)]]. 

(* discrimination *)
definition aux \def
  \lambda f. match f with
    [ (pp n) \Rightarrow n
    | (nn n) \Rightarrow n
    | (cons x f) \Rightarrow O].

definition fhd \def
\lambda f. match f with
    [ (pp n) \Rightarrow (pos n)
    | (nn n) \Rightarrow (neg n)
    | (cons x f) \Rightarrow x].

definition ftl \def
\lambda f. match f with
    [ (pp n) \Rightarrow (pp n)
    | (nn n) \Rightarrow (nn n)
    | (cons x f) \Rightarrow f].
    
theorem injective_pp : injective nat fraction pp.
unfold injective.intros.
change with ((aux (pp x)) = (aux (pp y))).
apply eq_f.assumption.
qed.

theorem injective_nn : injective nat fraction nn.
unfold injective.intros.
change with ((aux (nn x)) = (aux (nn y))).
apply eq_f.assumption.
qed.

theorem eq_cons_to_eq1: \forall f,g:fraction.\forall x,y:Z. 
(cons x f) = (cons y g) \to x = y.
intros.
change with ((fhd (cons x f)) = (fhd (cons y g))).
apply eq_f.assumption.
qed.

theorem eq_cons_to_eq2: \forall x,y:Z.\forall f,g:fraction.
(cons x f) = (cons y g) \to f = g.
intros.
change with ((ftl (cons x f)) = (ftl (cons y g))).
apply eq_f.assumption.
qed.

theorem not_eq_pp_nn: \forall n,m:nat. pp n \neq nn m.
intros.unfold Not. intro.
change with match (pp n) with
[ (pp n) \Rightarrow False
| (nn n) \Rightarrow True
| (cons x f) \Rightarrow True].
rewrite > H.
simplify.exact I.
qed.

theorem not_eq_pp_cons: 
\forall n:nat.\forall x:Z. \forall f:fraction. 
pp n \neq cons x f.
intros.unfold Not. intro.
change with match (pp n) with
[ (pp n) \Rightarrow False
| (nn n) \Rightarrow True
| (cons x f) \Rightarrow True].
rewrite > H.
simplify.exact I.
qed.

theorem not_eq_nn_cons: 
\forall n:nat.\forall x:Z. \forall f:fraction. 
nn n \neq cons x f.
intros.unfold Not. intro.
change with match (nn n) with
[ (pp n) \Rightarrow True
| (nn n) \Rightarrow False
| (cons x f) \Rightarrow True].
rewrite > H.
simplify.exact I.
qed.

theorem decidable_eq_fraction: \forall f,g:fraction.
decidable (f = g).
intros.unfold decidable.
apply (fraction_elim2 (\lambda f,g. f=g \lor (f=g \to False))).
  intros.elim g1.
    elim ((decidable_eq_nat n n1) : n=n1 \lor (n=n1 \to False)).
      left.apply eq_f. assumption.
      right.intro.apply H.apply injective_pp.assumption.
    right.apply not_eq_pp_nn.
    right.apply not_eq_pp_cons.
  intros. elim g1.
      right.intro.apply (not_eq_pp_nn n1 n).apply sym_eq. assumption.
      elim ((decidable_eq_nat n n1) : n=n1 \lor (n=n1 \to False)).
        left. apply eq_f. assumption.
        right.intro.apply H.apply injective_nn.assumption.
      right.apply not_eq_nn_cons.
  intros.right.intro.apply (not_eq_pp_cons m x f1).apply sym_eq.assumption.
  intros.right.intro.apply (not_eq_nn_cons m x f1).apply sym_eq.assumption.
  intros.elim H.
    elim ((decidable_eq_Z x y) : x=y \lor (x=y \to False)).
      left.apply eq_f2.assumption.
      assumption.
    right.intro.apply H2.apply (eq_cons_to_eq1 f1 g1).assumption.
    right.intro.apply H1.apply (eq_cons_to_eq2 x y f1 g1).assumption.
qed.

theorem eqfb_to_Prop: \forall f,g:fraction.
match (eqfb f g) with
[true \Rightarrow f=g
|false \Rightarrow f \neq g].
intros.apply (fraction_elim2 
(\lambda f,g.match (eqfb f g) with
[true \Rightarrow f=g
|false \Rightarrow f \neq g])).
  intros.elim g1.
    simplify.apply eqb_elim.
      intro.simplify.apply eq_f.assumption.
      intro.simplify.unfold Not.intro.apply H.apply injective_pp.assumption.
    simplify.apply not_eq_pp_nn.
    simplify.apply not_eq_pp_cons.
  intros.elim g1.
    simplify.unfold Not.intro.apply (not_eq_pp_nn n1 n).apply sym_eq. assumption.
    simplify.apply eqb_elim.intro.simplify.apply eq_f.assumption.
    intro.simplify.unfold Not.intro.apply H.apply injective_nn.assumption.
  simplify.apply not_eq_nn_cons.
  intros.simplify.unfold Not.intro.apply (not_eq_pp_cons m x f1).apply sym_eq. assumption.
  intros.simplify.unfold Not.intro.apply (not_eq_nn_cons m x f1).apply sym_eq. assumption.
  intros.
   simplify.
   apply eqZb_elim.
      intro.generalize in match H.elim (eqfb f1 g1).
        simplify.apply eq_f2.assumption.
        apply H2.
      simplify.unfold Not.intro.apply H2.apply (eq_cons_to_eq2 x y).assumption.
      intro.simplify.unfold Not.intro.apply H1.apply (eq_cons_to_eq1 f1 g1).assumption.
qed.
