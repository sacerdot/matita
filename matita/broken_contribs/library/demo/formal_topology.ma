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

include "logic/equality.ma".
include "logic/cprop_connectives.ma".

record powerset (A : Type) : Type ≝ { char : A → CProp }.

interpretation "char" 'subset p = (mk_powerset ? p).  

interpretation "pwset" 'powerset a = (powerset a). 

interpretation "in" 'mem a X = (char ? X a). 

definition subseteq ≝ λA.λu,v:\Omega \sup A.∀x.x ∈ u → x ∈ v.

interpretation "subseteq" 'subseteq u v = (subseteq ? u v).

definition overlaps ≝ λA.λU,V : Ω \sup A. exT2 ? (λx.x ∈ U) (λx.x ∈ V).

interpretation "overlaps" 'overlaps u v = (overlaps ? u v).

definition intersect ≝ λA.λu,v:Ω\sup A.{ y | y ∈ u ∧ y ∈ v }.

interpretation "intersect" 'intersects u v = (intersect ? u v). 

record axiom_set : Type ≝ { 
  A:> Type;
  i: A → Type;
  C: ∀a:A. i a → Ω \sup A
}.

inductive for_all (A: axiom_set) (U,V: Ω \sup A) (covers: A → CProp) : CProp ≝
   iter: (∀a:A.a ∈ V → covers a) → for_all A U V covers.

inductive covers (A: axiom_set) (U: \Omega \sup A) : A → CProp ≝
   refl: ∀a:A. a ∈ U → covers A U a
 | infinity: ∀a:A. ∀j: i ? a. for_all A U (C ? a j) (covers A U) → covers A U a.

notation "hvbox(a break ◃ b)" non associative with precedence 45
for @{ 'covers $a $b }. (* a \ltri b *)

interpretation "coversl" 'covers A U = (for_all ? U A (covers ? U)).
interpretation "covers" 'covers a U = (covers ? U a).

definition covers_elim ≝
 λA:axiom_set.λU: \Omega \sup A.λP:\Omega \sup A.
  λH1: U ⊆ P. 
   λH2:∀a:A.∀j:i ? a. C ? a j ◃ U → C ? a j ⊆ P → a ∈ P.
    let rec aux (a:A) (p:a ◃ U) on p : a ∈ P ≝
     match p return λaa.λ_:aa ◃ U.aa ∈ P with
      [ refl a q ⇒ H1 a q
      | infinity a j q ⇒
         H2 a j q
          match q return λ_:(C ? a j) ◃ U. C ? a j ⊆ P with
          [ iter f ⇒ λb.λr. aux b (f b r) ]]
    in
     aux.

inductive ex_such (A : axiom_set) (U,V : \Omega \sup A) (fish: A → CProp) : CProp ≝
 found : ∀a. a ∈ V → fish a → ex_such A U V fish.

coinductive fish (A:axiom_set) (U: \Omega \sup A) : A → CProp ≝
 mk_fish: ∀a:A. a ∈ U → (∀j: i ? a. ex_such A U (C ? a j) (fish A U)) → fish A U a.

notation "hvbox(a break ⋉ b)" non associative with precedence 45
for @{ 'fish $a $b }. (* a \ltimes b *)

interpretation "fishl" 'fish A U = (ex_such ? U A (fish ? U)).
interpretation "fish" 'fish a U = (fish ? U a).

let corec fish_rec (A:axiom_set) (U: \Omega \sup A)
 (P: Ω \sup A) (H1: P ⊆ U)
  (H2: ∀a:A. a ∈ P → ∀j: i ? a. C ? a j ≬ P):
   ∀a:A. ∀p: a ∈ P. a ⋉ U ≝
 λa,p.
  mk_fish A U a
   (H1 ? p)
   (λj: i ? a.
    match H2 a p j with
     [ ex_introT2 (y: A) (HyC : y ∈ C ? a j) (HyP : y ∈ P) ⇒
         found ???? y HyC (fish_rec A U P H1 H2 y HyP)
     ]).

theorem reflexivity: ∀A:axiom_set.∀a:A.∀V. a ∈ V → a ◃ V.
 intros;
 apply refl;
 assumption.
qed.

theorem transitivity: ∀A:axiom_set.∀a:A.∀U,V. a ◃ U → U ◃ V → a ◃ V.
 intros;
 apply (covers_elim ?? {a | a ◃ V} ??? H); simplify; intros;
  [ cases H1 in H2; apply H2;
  | apply infinity;
     [ assumption
     | constructor 1;
       assumption]]
qed.

theorem covers_elim2:
 ∀A: axiom_set. ∀U:Ω \sup A.∀P: A → CProp.
  (∀a:A. a ∈ U → P a) →
   (∀a:A.∀V:Ω \sup A. a ◃ V → V ◃ U → (∀y. y ∈ V → P y) → P a) →
     ∀a:A. a ◃ U → P a.
 intros;
 change with (a ∈ {a | P a});
 apply (covers_elim ?????? H2);
  [ intros 2; simplify; apply H; assumption
  | intros;
    simplify in H4 ⊢ %;
    apply H1;
     [ apply (C ? a1 j);
     | autobatch; 
     | assumption;
     | assumption]]
qed.

theorem coreflexivity: ∀A:axiom_set.∀a:A.∀V. a ⋉ V → a ∈ V.
 intros;
 cases H;
 assumption.
qed.

theorem cotransitivity:
 ∀A:axiom_set.∀a:A.∀U,V. a ⋉ U → (∀b:A. b ⋉ U → b ∈ V) → a ⋉ V.
 intros;
 apply (fish_rec ?? {a|a ⋉ U} ??? H); simplify; intros;
  [ apply H1; apply H2;
  | cases H2 in j; clear H2; intro i;
    cases (H4 i); clear H4; exists[apply a3] assumption]
qed.

theorem compatibility: ∀A:axiom_set.∀a:A.∀U,V. a ⋉ V → a ◃ U → U ⋉ V.
 intros;
 generalize in match H; clear H; 
 apply (covers_elim ?? {a|a ⋉ V → U ⋉ V} ??? H1);
 clear H1; simplify; intros;
  [ exists [apply x] assumption
  | cases H2 in j H H1; clear H2 a1; intros; 
    cases (H1 i); clear H1; apply (H3 a1); assumption]
qed.

definition leq ≝ λA:axiom_set.λa,b:A. a ◃ {y|b=y}.

interpretation "covered by one" 'leq a b = (leq ? a b).

theorem leq_refl: ∀A:axiom_set.∀a:A. a ≤ a.
 intros;
 apply refl;
 normalize;
 reflexivity.
qed.

theorem leq_trans: ∀A:axiom_set.∀a,b,c:A. a ≤ b → b ≤ c → a ≤ c.
 intros;
 unfold in H H1 ⊢ %;
 apply (transitivity ???? H);
 constructor 1;
 intros;
 normalize in H2;
 rewrite < H2;
 assumption.
qed.

definition uparrow ≝ λA:axiom_set.λa:A.mk_powerset ? (λb:A. a ≤ b).

interpretation "uparrow" 'uparrow a = (uparrow ? a).

definition downarrow ≝ λA:axiom_set.λU:Ω \sup A.mk_powerset ? (λa:A. (↑a) ≬ U).

interpretation "downarrow" 'downarrow a = (downarrow ? a).

definition fintersects ≝ λA:axiom_set.λU,V:Ω \sup A.↓U ∩ ↓V.

interpretation "fintersects" 'fintersects U V = (fintersects ? U V).

record convergent_generated_topology : Type ≝
 { AA:> axiom_set;
   convergence: ∀a:AA.∀U,V:Ω \sup AA. a ◃ U → a ◃ V → a ◃ (U ↓ V)
 }.
