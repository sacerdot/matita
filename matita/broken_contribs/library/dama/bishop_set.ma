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

include "dama/ordered_set.ma".

(* Definition 2.2, setoid *)
record bishop_set: Type ≝ {
  bs_carr:> Type;
  bs_apart: bs_carr → bs_carr → CProp;
  bs_coreflexive: coreflexive ? bs_apart;
  bs_symmetric: symmetric ? bs_apart;
  bs_cotransitive: cotransitive ? bs_apart
}.

interpretation "bishop set apartness" 'apart x y = (bs_apart ? x y).

definition bishop_set_of_ordered_set: ordered_set → bishop_set.
intros (E); apply (mk_bishop_set E (λa,b:E. a ≰ b ∨ b ≰ a));  
[1: intro x; simplify; intro H; cases H; clear H;
    apply (exc_coreflexive x H1);
|2: intros 3 (x y H); simplify in H ⊢ %; cases H; [right|left]assumption; 
|3: intros 4 (x y z H);  simplify in H ⊢ %; cases H; clear H;
    [ cases (exc_cotransitive x y z H1); [left;left|right;left] assumption;
    | cases (exc_cotransitive y x z H1); [right;right|left;right] assumption;]]
qed.

(* Definition 2.2 (2) *)
definition eq ≝ λA:bishop_set.λa,b:A. ¬ (a # b).

interpretation "Bishop set alikeness" 'napart a b = (eq ? a b). 

lemma eq_reflexive:∀E:bishop_set. reflexive ? (eq E).
intros (E); unfold; intros (x); apply bs_coreflexive; 
qed.

lemma eq_sym_:∀E:bishop_set.symmetric ? (eq E).
intros 4 (E x y H); intro T; cases (H (bs_symmetric ??? T)); 
qed.

lemma eq_sym:∀E:bishop_set.∀x,y:E.x ≈ y → y ≈ x ≝ eq_sym_.

lemma eq_trans_: ∀E:bishop_set.transitive ? (eq E).
intros 6 (E x y z Exy Eyz); intro Axy; cases (bs_cotransitive ???y Axy); 
[apply Exy|apply Eyz] assumption.
qed.

coercion bishop_set_of_ordered_set.

lemma le_antisymmetric: 
  ∀E:ordered_set.antisymmetric E (le (os_l E)) (eq E).
intros 5 (E x y Lxy Lyx); intro H; 
cases H; [apply Lxy;|apply Lyx] assumption;
qed.

lemma le_le_eq: ∀E:ordered_set.∀a,b:E. a ≤ b → b ≤ a → a ≈ b.
intros (E x y L1 L2); intro H; cases H; [apply L1|apply L2] assumption;
qed.

definition bs_subset ≝ λO:bishop_set.λP,Q:O→Prop.∀x:O.P x → Q x.

interpretation "bishop set subset" 'subseteq a b = (bs_subset ? a b). 

definition square_bishop_set : bishop_set → bishop_set.
intro S; apply (mk_bishop_set (S × S));
[1: intros (x y); apply ((\fst x # \fst y) ∨ (\snd x # \snd y));
|2: intro x; simplify; intro; cases H (X X); clear H; apply (bs_coreflexive ?? X);   
|3: intros 2 (x y); simplify; intro H; cases H (X X); clear H; [left|right] apply (bs_symmetric ??? X); 
|4: intros 3 (x y z); simplify; intro H; cases H (X X); clear H;
    [1: cases (bs_cotransitive ??? (\fst z) X); [left;left|right;left]assumption;
    |2: cases (bs_cotransitive ??? (\snd z) X); [left;right|right;right]assumption;]]
qed.

notation "s 2 \atop \neq" non associative with precedence 90
  for @{ 'square_bs $s }.
notation > "s 'squareB'" non associative with precedence 90
  for @{ 'squareB $s }.
interpretation "bishop set square" 'squareB x = (square_bishop_set x).
interpretation "bishop set square" 'square_bs x = (square_bishop_set x).
