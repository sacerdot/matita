
record powerset (A : Type) : Type := { content : A → CProp }.

notation > "Ω ^ A" non associative with precedence 55 for @{'P $A}.
notation "Ω \sup A" non associative with precedence 55 for @{'P $A}.
interpretation "Powerset" 'P A = (powerset A).

record AxiomSet : Type := {
  S :> Type;
  I_ : S → Type;
  C_ : ∀a.I_ a → Ω ^ S
}.

notation > "∀ident a∈A.P" right associative with precedence 20
for @{ ∀${ident a} : S $A. $P }.
notation > "λident a∈A.P" right associative with precedence 20
for @{ λ${ident a} : S $A. $P }.

notation "'I'" non associative with precedence 90 for @{'I}.
interpretation "I" 'I = (I_ ?).
notation < "'I' \lpar a \rpar" non associative with precedence 90 for @{'I1 $a}.
interpretation "I a" 'I1 a = (I_ ? a).
notation "'C'" non associative with precedence 90 for @{'C}.
interpretation "C" 'C = (C_ ?).
notation < "'C' \lpar a \rpar" non associative with precedence 90 for @{'C1 $a}.
interpretation "C a" 'C1 a = (C_ ? a).
notation < "'C' \lpar a , i \rpar" non associative with precedence 90 for @{'C2 $a $i}.
interpretation "C a i" 'C2 a i = (C_ ? a i).

definition in_subset :=
  λA:AxiomSet.λa∈A.λU:Ω^A.content A U a.
  
notation "hvbox(a break εU)" non associative with precedence 55 for 
@{'in_subset $a $U}.
interpretation "In subset" 'in_subset a U = (in_subset ? a U).

definition for_all ≝ λA:AxiomSet.λU:Ω^A.λP:A → CProp.∀x.xεU → P x.

inductive covers (A : AxiomSet) (U : Ω ^ A) : A → CProp :=
 | refl_ : ∀a.aεU → covers A U a
 | infinity_ : ∀a.∀i : I a. for_all A (C a i) (covers A U)  → covers A U a.
 
notation "'refl'" non associative with precedence 90 for @{'refl}. 
interpretation "refl" 'refl = (refl_ ? ? ?).

notation "'infinity'" non associative with precedence 90 for @{'infinity}.  
interpretation "infinity" 'infinity = (infinity_ ? ? ?).
 
notation "U ⊲ V" non associative with precedence 45
for @{ 'covers_subsets $U $V}.
interpretation "Covers subsets" 'covers_subsets U V = (for_all ? U (covers ? V)).
interpretation "Covers elem subset" 'covers_subsets U V = (covers ? V U).

definition subseteq := λA:AxiomSet.λU,V:Ω^A.∀x.xεU → xεV.

interpretation "subseteq" 'subseteq u v = (subseteq ? u v).


definition covers_elim_ ≝
 λA:AxiomSet.λU,P: Ω^A.λH1: U ⊆ P. 
  λH2:∀a∈A.∀j:I a. C a j ⊲ U → C a j ⊆ P → aεP.
    let rec aux (a:A) (p:a ⊲ U) on p : aεP ≝
     match p return λr.λ_:r ⊲ U.r ε P with
      [ refl_ a q ⇒ H1 a q
      | infinity_ a j q ⇒ H2 a j q (λb.λr. aux b (q b r))]
    in
     aux.
     
interpretation "char" 'subset p = (mk_powerset ? p).  
     
definition covers_elim : 
 ∀A:AxiomSet.∀U: Ω^A.∀P:A→CProp.∀H1: U ⊆ {x | P x}. 
  ∀H2:∀a∈A.∀j:I a. C a j ⊲ U → C a j ⊆ {x | P x} → P a.
   ∀a∈A.a ⊲ U → P a.
change in ⊢ (?→?→?→?→?→?→?→%) with (aε{x|P x});
intros 3; apply covers_elim_;
qed.

theorem trans_: ∀A:AxiomSet.∀a∈A.∀U,V. a ⊲ U → U ⊲ V → a ⊲ V.
 intros;
 elim H using covers_elim;
  [ intros 2; apply (H1 ? H2);
  | intros; apply (infinity j);
    intros 2; apply (H3 ? H4);]
qed.

notation "'trans'" non associative with precedence 90 for @{'trans}. 
interpretation "trans" 'trans = (trans_ ? ?).

