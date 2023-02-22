include "logic/cprop_connectives.ma".
include "igft.ma".

axiom A: Type.
axiom S_: A → Ω^A.

inductive Unit : Type := unit : Unit.

definition axs: AxiomSet.
 constructor 1;
  [ apply A;
  | intro; apply Unit;
  | intros; apply (S_ a)]
qed.

definition S : axs → Ω^axs ≝ S_.

definition emptyset: Ω^axs ≝ {x | False}.

notation "∅︀" non associative with precedence 90 for @{'emptyset}.
interpretation "emptyset" 'emptyset = emptyset.
notation "∅" non associative with precedence 91 for @{'emptyset1}.
interpretation "emptyset1" 'emptyset1 = emptyset.

definition Z: Ω \sup axs ≝ {x | x ⊲ ∅}.

theorem cantor: ∀a:axs. ¬ (Z ⊆ S a ∧ S a ⊆ Z).
 intros 2; cases H; clear H;
 cut (a ⊲ S a);
  [2: apply infinity; [apply unit] change with (S a ⊲ S a); 
      intros 2; apply refl; apply H;]
 cut (a ⊲ ∅︀);
  [2: apply (trans (S a)); [ assumption ]
      intros 2; lapply (H2 ? H) as K;
      change in K with (x ⊲ ∅ );
      assumption;]
 cut (a ε S a);
  [2: apply H1; apply Hcut1;]
 generalize in match Hcut2; clear Hcut2;
 elim Hcut1 using covers_elim;
  [ intros 2; cases H;
  | intros; apply (H3 a1); [apply H4|apply H4]]
qed.
