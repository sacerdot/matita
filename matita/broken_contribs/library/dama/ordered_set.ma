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

include "datatypes/constructors.ma".
include "logic/cprop_connectives.ma".


(* TEMPLATES
notation "''" non associative with precedence 90 for @{'}.
notation "''" non associative with precedence 90 for @{'}.

interpretation "" ' = ( (os_l ?)).
interpretation "" ' = ( (os_r ?)).
*)

(* Definition 2.1 *)
record half_ordered_set: Type ≝ {
  hos_carr:> Type;
  wloss: ∀A,B:Type. (A → A → B) → A → A → B;
  wloss_prop: (∀T,R,P,x,y.P x y = wloss T R P x y) ∨ (∀T,R,P,x,y.P y x = wloss T R P x y); 
  hos_excess_: hos_carr → hos_carr → CProp;
  hos_coreflexive: coreflexive ? (wloss ?? hos_excess_);
  hos_cotransitive: cotransitive ? (wloss ?? hos_excess_)
}.

definition hos_excess ≝ λO:half_ordered_set.wloss O ?? (hos_excess_ O). 

definition dual_hos : half_ordered_set → half_ordered_set.
intro; constructor 1;
[ apply (hos_carr h);
| apply (λT,R,f,x,y.wloss h T R f y x); 
| intros; cases (wloss_prop h);[right|left]intros;apply H; 
| apply (hos_excess_ h);
| apply (hos_coreflexive h);
| intros 4 (x y z H); simplify in H ⊢ %; cases (hos_cotransitive h y x z H);
  [right|left] assumption;]
qed.

record ordered_set : Type ≝ {
  os_l : half_ordered_set
}.

definition os_r : ordered_set → half_ordered_set.
intro o; apply (dual_hos (os_l o)); qed.

lemma half2full : half_ordered_set → ordered_set.
intro hos;
constructor 1; apply hos;  
qed.

definition Type_of_ordered_set : ordered_set → Type.
intro o; apply (hos_carr (os_l o)); qed.

definition Type_of_ordered_set_dual : ordered_set → Type.
intro o; apply (hos_carr (os_r o)); qed.

coercion Type_of_ordered_set_dual.
coercion Type_of_ordered_set.

notation "a ≰≰ b" non associative with precedence 45 for @{'nleq_low $a $b}.
interpretation "Ordered half set excess" 'nleq_low a b = (hos_excess ? a b).

interpretation "Ordered set excess (dual)" 'ngeq a b = (hos_excess (os_r ?) a b).
interpretation "Ordered set excess" 'nleq a b = (hos_excess (os_l ?) a b).

notation "'exc_coreflexive'" non associative with precedence 90 for @{'exc_coreflexive}.
notation "'cxe_coreflexive'" non associative with precedence 90 for @{'cxe_coreflexive}.

interpretation "exc_coreflexive" 'exc_coreflexive = ((hos_coreflexive (os_l ?))).
interpretation "cxe_coreflexive" 'cxe_coreflexive = ((hos_coreflexive (os_r ?))).

notation "'exc_cotransitive'" non associative with precedence 90 for @{'exc_cotransitive}.
notation "'cxe_cotransitive'" non associative with precedence 90 for @{'cxe_cotransitive}.

interpretation "exc_cotransitive" 'exc_cotransitive = ((hos_cotransitive (os_l ?))).
interpretation "cxe_cotransitive" 'cxe_cotransitive = ((hos_cotransitive (os_r ?))).

(* Definition 2.2 (3) *)
definition le ≝ λE:half_ordered_set.λa,b:E. ¬ (a ≰≰ b).

notation "hvbox(a break ≤≤ b)" non associative with precedence 45 for @{ 'leq_low $a $b }.
interpretation "Half ordered set greater or equal than" 'leq_low a b = ((le ? a b)).

interpretation "Ordered set greater or equal than" 'geq a b = ((le (os_r ?) a b)).
interpretation "Ordered set less or equal than" 'leq a b = ((le (os_l ?) a b)).

lemma hle_reflexive: ∀E.reflexive ? (le E).
unfold reflexive; intros 3; apply (hos_coreflexive ? x H);
qed.

notation "'le_reflexive'" non associative with precedence 90 for @{'le_reflexive}.
notation "'ge_reflexive'" non associative with precedence 90 for @{'ge_reflexive}.

interpretation "le reflexive" 'le_reflexive = (hle_reflexive (os_l ?)).
interpretation "ge reflexive" 'ge_reflexive = (hle_reflexive (os_r ?)).

(* DUALITY TESTS 
lemma test_le_ge_convertible :∀o:ordered_set.∀x,y:o. x ≤ y → y ≥ x.
intros; assumption; qed.

lemma test_ge_reflexive :∀o:ordered_set.∀x:o. x ≥ x.
intros; apply ge_reflexive. qed.

lemma test_le_reflexive :∀o:ordered_set.∀x:o. x ≤ x.
intros; apply le_reflexive. qed.
*)

lemma hle_transitive: ∀E.transitive ? (le E).
unfold transitive; intros 7 (E x y z H1 H2 H3); cases (hos_cotransitive E x z y H3) (H4 H4);
[cases (H1 H4)|cases (H2 H4)]
qed.

notation "'le_transitive'" non associative with precedence 90 for @{'le_transitive}.
notation "'ge_transitive'" non associative with precedence 90 for @{'ge_transitive}.

interpretation "le transitive" 'le_transitive = (hle_transitive (os_l ?)).
interpretation "ge transitive" 'ge_transitive = (hle_transitive (os_r ?)).

(* Lemma 2.3 *)
lemma exc_hle_variance: 
  ∀O:half_ordered_set.∀a,b,a',b':O.a ≰≰ b → a ≤≤ a' → b' ≤≤ b → a' ≰≰ b'. 
intros (O a b a1 b1 Eab Laa1 Lb1b);
cases (hos_cotransitive ? a b a1 Eab) (H H); [cases (Laa1 H)]
cases (hos_cotransitive ? ?? b1 H) (H1 H1); [assumption]
cases (Lb1b H1);
qed.

notation "'exc_le_variance'" non associative with precedence 90 for @{'exc_le_variance}.
notation "'exc_ge_variance'" non associative with precedence 90 for @{'exc_ge_variance}.

interpretation "exc_le_variance" 'exc_le_variance = (exc_hle_variance (os_l ?)).
interpretation "exc_ge_variance" 'exc_ge_variance = (exc_hle_variance (os_r ?)).

definition square_exc ≝
 λO:half_ordered_set.λx,y:O×O.\fst x ≰≰ \fst y ∨ \snd x ≰≰ \snd y.

lemma square_half_ordered_set: half_ordered_set → half_ordered_set.
intro O;
apply (mk_half_ordered_set (O × O));
[1: apply (wloss O);
|2: intros; cases (wloss_prop O); [left|right] intros; apply H;
|3: apply (square_exc O); 
|4: intro x; cases (wloss_prop O); rewrite < (H  ?? (square_exc O) x x); clear H;
    cases x; clear x; unfold square_exc; intro H; cases H; clear H; simplify in H1;
    [1,3: apply (hos_coreflexive O h H1);
    |*: apply (hos_coreflexive O h1 H1);]
|5: intros 3 (x0 y0 z0); cases (wloss_prop O);
    do 3 rewrite < (H  ?? (square_exc O)); clear H; cases x0; cases y0; cases z0; clear x0 y0 z0;
    simplify; intro H; cases H; clear H;
    [1: cases (hos_cotransitive ? h h2 h4 H1); [left;left|right;left] assumption;
    |2: cases (hos_cotransitive ? h1 h3 h5 H1); [left;right|right;right] assumption;
    |3: cases (hos_cotransitive ? h2 h h4 H1); [right;left|left;left] assumption;
    |4: cases (hos_cotransitive ? h3 h1 h5 H1); [right;right|left;right] assumption;]]
qed.

lemma square_ordered_set: ordered_set → ordered_set.
intro O; constructor 1; apply (square_half_ordered_set (os_l O));
qed.

notation "s 2 \atop \nleq" non associative with precedence 90
  for @{ 'square_os $s }.
notation > "s 'squareO'" non associative with precedence 90
  for @{ 'squareO $s }.
interpretation "ordered set square" 'squareO s = (square_ordered_set s). 
interpretation "ordered set square" 'square_os s = (square_ordered_set s).

definition os_subset ≝ λO:ordered_set.λP,Q:O→Prop.∀x:O.P x → Q x.

interpretation "ordered set subset" 'subseteq a b = (os_subset ? a b). 

