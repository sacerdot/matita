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

include "sets/categories2.ma".

(*
interpretation "unary morphism comprehension with no proof" 'comprehension T P = 
  (mk_unary_morphism T ? P ?).
interpretation "unary morphism1 comprehension with no proof" 'comprehension T P = 
  (mk_unary_morphism1 T ? P ?).

notation > "hvbox({ ident i ∈ s | term 19 p | by })" with precedence 90
for @{ 'comprehension_by $s (λ${ident i}. $p) $by}.
notation < "hvbox({ ident i ∈ s | term 19 p })" with precedence 90
for @{ 'comprehension_by $s (λ${ident i}:$_. $p) $by}.

interpretation "unary morphism comprehension with proof" 'comprehension_by s \eta.f p = 
  (mk_unary_morphism s ? f p).
interpretation "unary morphism1 comprehension with proof" 'comprehension_by s \eta.f p = 
  (mk_unary_morphism1 s ? f p).
*)

(* per il set-indexing vedere capitolo BPTools (foundational tools), Sect. 0.3.4 complete
   lattices, Definizione 0.9 *)
(* USARE L'ESISTENZIALE DEBOLE *)
nrecord OAlgebra : Type[2] := {
  oa_P :> setoid1;
  oa_leq : unary_morphism1 oa_P (unary_morphism1_setoid1 oa_P CPROP); (*CSC: dovrebbe essere CProp bug refiner*)
  oa_overlap: unary_morphism1 oa_P (unary_morphism1_setoid1 oa_P CPROP);
  binary_meet: unary_morphism1 oa_P (unary_morphism1_setoid1 oa_P oa_P);
(*CSC:  oa_join: ∀I:setoid.unary_morphism1 (setoid1_of_setoid … I ⇒ oa_P) oa_P;*)
  oa_one: oa_P;
  oa_zero: oa_P;
  oa_leq_refl: ∀a:oa_P. oa_leq a a; 
  oa_leq_antisym: ∀a,b:oa_P.oa_leq a b → oa_leq b a → a = b;
  oa_leq_trans: ∀a,b,c:oa_P.oa_leq a b → oa_leq b c → oa_leq a c;
  oa_overlap_sym: ∀a,b:oa_P.oa_overlap a b → oa_overlap b a;
(*CSC:  oa_join_sup: ∀I:setoid.∀p_i:I ⇒ oa_P.∀p:oa_P.oa_leq (oa_join I p_i) p = (∀i:I.oa_leq (p_i i) p);*)
  oa_zero_bot: ∀p:oa_P.oa_leq oa_zero p;
  oa_one_top: ∀p:oa_P.oa_leq p oa_one;
  oa_overlap_preservers_meet: ∀p,q:oa_P.oa_overlap p q → oa_overlap p (binary_meet p q);
(*CSC:  oa_join_split:
      ∀I:SET.∀p.∀q:I ⇒ oa_P.
       oa_overlap p (oa_join I q) = (∃i:I.oa_overlap p (q i));*)
  (*oa_base : setoid;
  1) enum non e' il nome giusto perche' non e' suriettiva
  2) manca (vedere altro capitolo) la "suriettivita'" come immagine di insiemi di oa_base
  oa_enum : ums oa_base oa_P;
  oa_density: ∀p,q.(∀i.oa_overlap p (oa_enum i) → oa_overlap q (oa_enum i)) → oa_leq p q
  *)
  oa_density: 
      ∀p,q.(∀r.oa_overlap p r → oa_overlap q r) → oa_leq p q
}.

interpretation "o-algebra leq" 'leq a b = (fun11 ?? (fun11 ?? (oa_leq ?) a) b).

notation "hovbox(a mpadded width -150% (>)< b)" non associative with precedence 45
for @{ 'overlap $a $b}.
interpretation "o-algebra overlap" 'overlap a b = (fun11 ?? (fun11 ?? (oa_overlap ?) a) b).

notation < "hovbox(mstyle scriptlevel 1 scriptsizemultiplier 1.7 (∧) \below (\emsp) \nbsp term 90 p)" 
non associative with precedence 55 for @{ 'oa_meet $p }.
notation < "hovbox(mstyle scriptlevel 1 scriptsizemultiplier 1.7 (∧) \below (ident i ∈  I) break term 90 p)" 
non associative with precedence 55 for @{ 'oa_meet_mk (λ${ident i}:$I.$p) }.

(*notation > "hovbox(∧ f)" non associative with precedence 65
for @{ 'oa_meet $f }.
interpretation "o-algebra meet" 'oa_meet f = 
  (fun12 ?? (oa_meet ??) f).
interpretation "o-algebra meet with explicit function" 'oa_meet_mk f = 
  (fun12 ?? (oa_meet ??) (mk_unary_morphism ?? f ?)).
*)
notation < "hovbox(mstyle scriptlevel 1 scriptsizemultiplier 1.7 (∨) \below (\emsp) \nbsp term 90 p)" 
non associative with precedence 55 for @{ 'oa_join $p }.
notation < "hovbox(mstyle scriptlevel 1 scriptsizemultiplier 1.7 (∨) \below (ident i ∈  I) break term 90 p)" 
non associative with precedence 55 for @{ 'oa_join_mk (λ${ident i}:$I.$p) }.

(*CSC
notation > "hovbox(∨ f)" non associative with precedence 65
for @{ 'oa_join $f }.
interpretation "o-algebra join" 'oa_join f = 
  (fun12 ?? (oa_join ??) f).
interpretation "o-algebra join with explicit function" 'oa_join_mk f = 
  (fun12 ?? (oa_join ??) (mk_unary_morphism ?? f ?)).
*)
(*definition binary_meet : ∀O:OAlgebra. binary_morphism1 O O O.
intros; split;
[ intros (p q); 
  apply (∧ { x ∈ BOOL | match x with [ true ⇒ p | false ⇒ q ] | IF_THEN_ELSE_p ? p q });
| intros; lapply (prop12 ? O (oa_meet O BOOL));
   [2: apply ({ x ∈ BOOL | match x with [ true ⇒ a | false ⇒ b ] | IF_THEN_ELSE_p ? a b });
   |3: apply ({ x ∈ BOOL | match x with [ true ⇒ a' | false ⇒ b' ] | IF_THEN_ELSE_p ? a' b' });
   | apply Hletin;]
  intro x; simplify; cases x; simplify; assumption;]
qed.*)

interpretation "o-algebra binary meet" 'and a b = 
  (fun11 ?? (fun11 ?? (binary_meet ?) a) b).

(*
prefer coercion Type1_OF_OAlgebra.

definition binary_join : ∀O:OAlgebra. binary_morphism1 O O O.
intros; split;
[ intros (p q); 
  apply (∨ { x ∈ BOOL | match x with [ true ⇒ p | false ⇒ q ] | IF_THEN_ELSE_p ? p q });
| intros; lapply (prop12 ? O (oa_join O BOOL));
   [2: apply ({ x ∈ BOOL | match x with [ true ⇒ a | false ⇒ b ] | IF_THEN_ELSE_p ? a b });
   |3: apply ({ x ∈ BOOL | match x with [ true ⇒ a' | false ⇒ b' ] | IF_THEN_ELSE_p ? a' b' });
   | apply Hletin;]
  intro x; simplify; cases x; simplify; assumption;]
qed.

interpretation "o-algebra binary join" 'or a b = 
  (fun21 ??? (binary_join ?) a b).
*)
(*
lemma oa_overlap_preservers_meet: ∀O:OAlgebra.∀p,q:O.p >< q → p >< (p ∧ q).
(* next change to avoid universe inconsistency *)
change in ⊢ (?→%→%→?) with (Type1_OF_OAlgebra O);
intros;  lapply (oa_overlap_preserves_meet_ O p q f);
lapply (prop21 O O CPROP (oa_overlap O) p p ? (p ∧ q) # ?);
[3: apply (if ?? (Hletin1)); apply Hletin;|skip] apply refl1;
qed.
*)
notation < "hovbox(mstyle scriptlevel 1 scriptsizemultiplier 1.7 (∨) \below (\emsp) \nbsp term 90 p)" 
non associative with precedence 49 for @{ 'oa_join $p }.
notation < "hovbox(mstyle scriptlevel 1 scriptsizemultiplier 1.7 (∨) \below (ident i ∈  I) break term 90 p)" 
non associative with precedence 49 for @{ 'oa_join_mk (λ${ident i}:$I.$p) }.
notation < "hovbox(a ∨ b)" left associative with precedence 49
for @{ 'oa_join_mk (λ${ident i}:$_.match $i with [ true ⇒ $a | false ⇒ $b ]) }.

notation > "hovbox(∨ f)" non associative with precedence 64
for @{ 'oa_join $f }.
notation > "hovbox(a ∨ b)" left associative with precedence 49
for @{ 'oa_join (mk_unary_morphism BOOL ? (λx__:bool.match x__ with [ true ⇒ $a | false ⇒ $b ]) (IF_THEN_ELSE_p ? $a $b)) }.

(*interpretation "o-algebra join" 'oa_join f = 
  (fun12 ?? (oa_join ??) f).
interpretation "o-algebra join with explicit function" 'oa_join_mk f = 
  (fun12 ?? (oa_join ??) (mk_unary_morphism ?? f ?)).
*)
nrecord ORelation (P,Q : OAlgebra) : Type[1] ≝ {
  or_f :> P ⇒ Q;
  or_f_minus_star : P ⇒ Q;
  or_f_star : Q ⇒ P;
  or_f_minus : Q ⇒ P;
  or_prop1 : ∀p,q. (or_f p ≤ q) = (p ≤ or_f_star q);
  or_prop2 : ∀p,q. (or_f_minus p ≤ q) = (p ≤ or_f_minus_star q);
  or_prop3 : ∀p,q. (or_f p >< q) = (p >< or_f_minus q)
}.
 
notation "r \sup *" non associative with precedence 90 for @{'OR_f_star $r}.
notation > "r *" non associative with precedence 90 for @{'OR_f_star $r}.

notation "r \sup (⎻* )" non associative with precedence 90 for @{'OR_f_minus_star $r}.
notation > "r⎻*" non associative with precedence 90 for @{'OR_f_minus_star $r}.

notation "r \sup ⎻" non associative with precedence 90 for @{'OR_f_minus $r}.
notation > "r⎻" non associative with precedence 90 for @{'OR_f_minus $r}.

interpretation "o-relation f⎻*" 'OR_f_minus_star r = (or_f_minus_star ? ? r).
interpretation "o-relation f⎻" 'OR_f_minus r = (or_f_minus ? ? r).
interpretation "o-relation f*" 'OR_f_star r = (or_f_star ? ? r).


ndefinition ORelation_setoid : OAlgebra → OAlgebra → setoid1.
#P; #Q; @ (ORelation P Q); @
 [ napply (λp,q.p = q)
 | #x; napply refl1
 | #x; #y; napply sym1
 | #x; #y; #z; napply trans1 ]
nqed.

unification hint 0 ≔ P, Q ;
  R ≟ (ORelation_setoid P Q)
(* -------------------------- *) ⊢
    carr1 R ≡ ORelation P Q.

ndefinition or_f_morphism1: ∀P,Q:OAlgebra.unary_morphism1 (ORelation_setoid P Q)
 (unary_morphism1_setoid1 P Q).
 #P; #Q; @
  [ napply or_f
  | #a; #a'; #e; nassumption]
nqed.

unification hint 0 ≔ P, Q, r;
 R ≟ (mk_unary_morphism1 … (or_f …) (prop11 … (or_f_morphism1 …)))
(* ------------------------ *) ⊢
  fun11 … R r ≡ or_f P Q r.

nlemma ORelation_eq_respects_leq_or_f_minus_:
 ∀P,Q:OAlgebra.∀r,r':ORelation P Q.
  r=r' → ∀x. r⎻ x ≤ r'⎻ x.
 #P; #Q; #a; #a'; #e; #x;
 napply oa_density; #r; #H;
 napply oa_overlap_sym;
 napply (. (or_prop3 … a' …)^-1); (*CSC: why a'? *)
 napply (. ?‡#)
  [##2: napply (a r)
  | napply (e^-1); //]
 napply (. (or_prop3 …));
 napply oa_overlap_sym;
 nassumption.
nqed.

nlemma ORelation_eq2:
 ∀P,Q:OAlgebra.∀r,r':ORelation P Q.
  r=r' → r⎻ = r'⎻.
 #P; #Q; #a; #a'; #e; #x; #x'; #Hx; napply (.= †Hx);
 napply oa_leq_antisym; napply ORelation_eq_respects_leq_or_f_minus_
  [ napply e | napply (e^-1)]
nqed.

ndefinition or_f_minus_morphism1: ∀P,Q:OAlgebra.unary_morphism1 (ORelation_setoid P Q)
 (unary_morphism1_setoid1 Q P).
 #P; #Q; @
  [ napply or_f_minus
  | napply ORelation_eq2]
nqed.

unification hint 0 ≔ P, Q, r;
 R ≟ (mk_unary_morphism1 … (or_f_minus …) (prop11 … (or_f_minus_morphism1 …)))
(* ------------------------ *) ⊢
  fun11 … R r ≡ or_f_minus P Q r.
  
naxiom daemon : False.

nlemma ORelation_eq_respects_leq_or_f_star_:
 ∀P,Q:OAlgebra.∀r,r':ORelation P Q.
  r=r' → ∀x. r* x ≤ r'* x.
 #P; #Q; #a; #a'; #e; #x; (*CSC: una schifezza *)
 ncases daemon.
 (*
 ngeneralize in match (. (or_prop1 P Q a' (a* x) x)^-1) in ⊢ %; #H; napply H;
 nchange with (or_f P Q a' (a* x) ≤ x);
 napply (. ?‡#)
  [##2: napply (a (a* x))
  | ngeneralize in match (a* x);
    nchange with (or_f P Q a' = or_f P Q a);
    napply (.= †e^-1); napply #]
 napply (. (or_prop1 …));
 napply oa_leq_refl.*)
nqed.

nlemma ORelation_eq3:
 ∀P,Q:OAlgebra.∀r,r':ORelation P Q.
  r=r' → r* = r'*.
 #P; #Q; #a; #a'; #e; #x; #x'; #Hx; napply (.= †Hx);
 napply oa_leq_antisym; napply ORelation_eq_respects_leq_or_f_star_
  [ napply e | napply (e^-1)]
nqed.

ndefinition or_f_star_morphism1: ∀P,Q:OAlgebra.unary_morphism1 (ORelation_setoid P Q)
 (unary_morphism1_setoid1 Q P).
 #P; #Q; @
  [ napply or_f_star
  | napply ORelation_eq3] 
nqed.

unification hint 0 ≔ P, Q, r;
 R ≟ (mk_unary_morphism1 … (or_f_star …) (prop11 … (or_f_star_morphism1 …)))
(* ------------------------ *) ⊢
  fun11 … R r ≡ or_f_star P Q r.

nlemma ORelation_eq_respects_leq_or_f_minus_star_:
 ∀P,Q:OAlgebra.∀r,r':ORelation P Q.
  r=r' → ∀x. r⎻* x ≤ r'⎻* x.
 #P; #Q; #a; #a'; #e; #x; (*CSC: una schifezza *)
 ncases daemon. (*
 ngeneralize in match (. (or_prop2 P Q a' (a⎻* x) x)^-1) in ⊢ %; #H; napply H;
 nchange with (or_f_minus P Q a' (a⎻* x) ≤ x);
 napply (. ?‡#)
  [##2: napply (a⎻ (a⎻* x))
  | ngeneralize in match (a⎻* x);
    nchange with (a'⎻ = a⎻);
    napply (.= †e^-1); napply #]
 napply (. (or_prop2 …));
 napply oa_leq_refl.*)
nqed.

nlemma ORelation_eq4:
 ∀P,Q:OAlgebra.∀r,r':ORelation P Q.
  r=r' → r⎻* = r'⎻*.
 #P; #Q; #a; #a'; #e; #x; #x'; #Hx; napply (.= †Hx);
 napply oa_leq_antisym; napply ORelation_eq_respects_leq_or_f_minus_star_
  [ napply e | napply (e^-1)]
nqed.

ndefinition or_f_minus_star_morphism1:
 ∀P,Q:OAlgebra.unary_morphism1 (ORelation_setoid P Q) (unary_morphism1_setoid1 P Q).
 #P; #Q; @
  [ napply or_f_minus_star
  | napply ORelation_eq4]
nqed.


unification hint 0 ≔ P, Q, r;
 R ≟ (mk_unary_morphism1 … (or_f_minus_star …) (prop11 … (or_f_minus_star_morphism1 …)))
(* ------------------------ *) ⊢
  fun11 … R r ≡ or_f_minus_star P Q r.
  
(* qui la notazione non va *)
(*CSC
nlemma leq_to_eq_join: ∀S:OAlgebra.∀p,q:S. p ≤ q → q = (binary_join ? p q).
 intros;
 apply oa_leq_antisym;
  [ apply oa_density; intros;
    apply oa_overlap_sym;
    unfold binary_join; simplify;
    apply (. (oa_join_split : ?));
    exists; [ apply false ]
    apply oa_overlap_sym;
    assumption
  | unfold binary_join; simplify;
    apply (. (oa_join_sup : ?)); intro;
    cases i; whd in ⊢ (? ? ? ? ? % ?);
     [ assumption | apply oa_leq_refl ]]
qed.

nlemma overlap_monotone_left: ∀S:OAlgebra.∀p,q,r:S. p ≤ q → p >< r → q >< r.
 #S; #p; #q; #r; #H1; #H2;
 apply (. (leq_to_eq_join : ?)‡#);
  [ apply f;
  | skip
  | apply oa_overlap_sym;
    unfold binary_join; simplify;
    apply (. (oa_join_split : ?));
    exists [ apply true ]
    apply oa_overlap_sym;
    assumption; ]
qed.*)

(* Part of proposition 9.9 *)
nlemma f_minus_image_monotone: ∀S,T.∀R:ORelation S T.∀p,q. p ≤ q → R⎻ p ≤ R⎻ q.
 #S; #T; #R; #p; #q; #H;
 napply (. (or_prop2 …));
 napply oa_leq_trans; ##[##2: napply H; ##| ##skip |
  napply (. (or_prop2 … q …)^ -1);(*CSC: why q?*) napply oa_leq_refl]
nqed.
 
(* Part of proposition 9.9 *)
nlemma f_minus_star_image_monotone: ∀S,T.∀R:ORelation S T.∀p,q. p ≤ q → R⎻* p ≤ R⎻* q.
 #S; #T; #R; #p; #q; #H;
 napply (. (or_prop2 … (R⎻* p) q)^ -1); (*CSC: why ?*)
 napply oa_leq_trans; ##[##3: napply H; ##| ##skip | napply (. (or_prop2 …)); napply oa_leq_refl]
nqed.

(* Part of proposition 9.9 *)
nlemma f_image_monotone: ∀S,T.∀R:ORelation S T.∀p,q. p ≤ q → R p ≤ R q.
 #S; #T; #R; #p; #q; #H;
 napply (. (or_prop1 …));
 napply oa_leq_trans; ##[##2: napply H; ##| ##skip | napply (. (or_prop1 … q …)^ -1); napply oa_leq_refl]
nqed.

(* Part of proposition 9.9 *)
nlemma f_star_image_monotone: ∀S,T.∀R:ORelation S T.∀p,q. p ≤ q → R* p ≤ R* q.
 #S; #T; #R; #p; #q; #H;
 napply (. (or_prop1 … (R* p) q)^ -1);
 napply oa_leq_trans; ##[##3: napply H; ##| ##skip | napply (. (or_prop1 …)); napply oa_leq_refl]
nqed.

nlemma lemma_10_2_a: ∀S,T.∀R:ORelation S T.∀p. p ≤ R⎻* (R⎻ p).
 #S; #T; #R; #p;
 napply (. (or_prop2 … p …)^-1);
 napply oa_leq_refl.
nqed.

nlemma lemma_10_2_b: ∀S,T.∀R:ORelation S T.∀p. R⎻ (R⎻* p) ≤ p.
 #S; #T; #R; #p;
 napply (. (or_prop2 …));
 napply oa_leq_refl.
nqed.

nlemma lemma_10_2_c: ∀S,T.∀R:ORelation S T.∀p. p ≤ R* (R p).
 #S; #T; #R; #p;
 napply (. (or_prop1 … p …)^-1);
 napply oa_leq_refl.
nqed.

nlemma lemma_10_2_d: ∀S,T.∀R:ORelation S T.∀p. R (R* p) ≤ p.
 #S; #T; #R; #p;
 napply (. (or_prop1 …));
 napply oa_leq_refl.
nqed.

nlemma lemma_10_3_a: ∀S,T.∀R:ORelation S T.∀p. R⎻ (R⎻* (R⎻ p)) = R⎻ p.
 #S; #T; #R; #p; napply oa_leq_antisym
  [ napply lemma_10_2_b
  | napply f_minus_image_monotone;
    napply lemma_10_2_a ]
nqed.

nlemma lemma_10_3_b: ∀S,T.∀R:ORelation S T.∀p. R* (R (R* p)) = R* p.
 #S; #T; #R; #p; napply oa_leq_antisym
  [ napply f_star_image_monotone;
    napply (lemma_10_2_d ?? R p)
  | napply lemma_10_2_c ]
nqed.

nlemma lemma_10_3_c: ∀S,T.∀R:ORelation S T.∀p. R (R* (R p)) = R p.
 #S; #T; #R; #p; napply oa_leq_antisym
  [ napply lemma_10_2_d
  | napply f_image_monotone;
    napply (lemma_10_2_c ?? R p) ]
nqed.

nlemma lemma_10_3_d: ∀S,T.∀R:ORelation S T.∀p. R⎻* (R⎻ (R⎻* p)) = R⎻* p.
 #S; #T; #R; #p; napply oa_leq_antisym
  [ napply f_minus_star_image_monotone;
    napply (lemma_10_2_b ?? R p)
  | napply lemma_10_2_a ]
nqed.

nlemma lemma_10_4_a: ∀S,T.∀R:ORelation S T.∀p. R⎻* (R⎻ (R⎻* (R⎻ p))) = R⎻* (R⎻ p).
 #S; #T; #R; #p; napply (†(lemma_10_3_a …)).
nqed.

nlemma lemma_10_4_b: ∀S,T.∀R:ORelation S T.∀p. R (R* (R (R* p))) = R (R* p).
 #S; #T; #R; #p; napply (†(lemma_10_3_b …));
nqed.

nlemma oa_overlap_sym': ∀o:OAlgebra.∀U,V:o. (U >< V) = (V >< U).
 #o; #U; #V; @; #H; napply oa_overlap_sym; nassumption.
nqed.

(******************* CATEGORIES **********************)

ninductive one : Type[0] ≝ unit : one.

ndefinition force : ∀S:Type[2]. S → ∀T:Type[2]. T → one → Type[2] ≝   
 λS,s,T,t,lock. match lock with [ unit => S ].

ndefinition enrich_as : 
 ∀S:Type[2].∀s:S.∀T:Type[2].∀t:T.∀lock:one.force S s T t lock ≝ 
 λS,s,T,t,lock. match lock return λlock.match lock with [ unit ⇒ S ] 
                    with [ unit ⇒ s ].

ncoercion enrich_as : ∀S:Type[2].∀s:S.∀T:Type[2].∀t:T.∀lock:one. force S s T t lock
 ≝ enrich_as on t: ? to force ? ? ? ? ?.

(* does not work here 
nlemma foo : ∀A,B,C:setoid1.∀f:B ⇒ C.∀g:A ⇒ B. unary_morphism1 A C.
#A; #B; #C; #f; #g; napply(f \circ g).
nqed.*)

(* This precise hint does not leave spurious metavariables *)
unification hint 0 ≔ A,B,C : setoid1, f:B ⇒ C, g: A ⇒ B;
   lock ≟ unit
(* --------------------------------------------------------------- *) ⊢
  (unary_morphism1 A C)
 ≡
  (force (unary_morphism1 A C) (comp1_unary_morphisms A B C f g)
   (carr1 A → carr1 C) (composition1 A B C f g)  lock)
  .

(* This uniform hint opens spurious metavariables
unification hint 0 ≔ A,B,C : setoid1, f:B ⇒ C, g: A ⇒ B, X;
   lock ≟ unit
(* --------------------------------------------------------------- *) ⊢
  (unary_morphism1 A C)
 ≡
  (force (unary_morphism1 A C) X (carr1 A → carr1 C) (fun11 … X)  lock)
  .
*)

nlemma foo : ∀A,B,C:setoid1.∀f:B ⇒ C.∀g:A ⇒ B. unary_morphism1 A C.
#A; #B; #C; #f; #g; napply(f ∘ g).
nqed.

(*

ndefinition uffa: ∀A,B. ∀U: unary_morphism1 A B. (A → B) → CProp[0].
 #A;#B;#_;#_; napply True.
nqed.
ndefinition mk_uffa: ∀A,B.∀U: unary_morphism1 A B. ∀f: (A → B). uffa A B U f.
 #A; #B; #U; #f; napply I.
nqed.

ndefinition coerc_to_unary_morphism1:
 ∀A,B. ∀U: unary_morphism1 A B. uffa A B U (fun11 … U) → unary_morphism1 A B.
 #A; #B; #U; #_; nassumption.
nqed.

ncheck (λA,B,C,f,g.coerc_to_unary_morphism1 ??? (mk_uffa ??? (composition1 A B C f g))). 
*)
ndefinition ORelation_composition : ∀P,Q,R. 
  unary_morphism1 (ORelation_setoid P Q)
   (unary_morphism1_setoid1 (ORelation_setoid Q R) (ORelation_setoid P R)).
#P; #Q; #R; napply mk_binary_morphism1
[ #F; #G; @
  [ napply (G ∘ F) (* napply (comp1_unary_morphisms … G F) (*CSC: was (G ∘ F);*) *)
  | napply (G⎻* ∘ F⎻* ) (* napply (comp1_unary_morphisms … G⎻* F⎻* ) (*CSC: was (G⎻* ∘ F⎻* );*)*)
  | napply (comp1_unary_morphisms … F* G* ) (*CSC: was (F* ∘ G* );*)
  | napply (comp1_unary_morphisms … F⎻ G⎻) (*CSC: was (F⎻ ∘ G⎻);*)
  | #p; #q; nnormalize;
    napply (.= (or_prop1 … G …)); (*CSC: it used to understand without G *)
    napply (or_prop1 …)
  | #p; #q; nnormalize;
    napply (.= (or_prop2 … F …));
    napply or_prop2
  | #p; #q; nnormalize;
    napply (.= (or_prop3 … G …));
    napply or_prop3
  ]
##| nnormalize; /3/]
nqed.

(*
ndefinition OA : category2.
split;
[ apply (OAlgebra);
| intros; apply (ORelation_setoid o o1);
| intro O; split;
  [1,2,3,4: apply id2;
  |5,6,7:intros; apply refl1;] 
| apply ORelation_composition;
| intros (P Q R S F G H); split;
   [ change with (H⎻* ∘ G⎻* ∘ F⎻* = H⎻* ∘ (G⎻* ∘ F⎻* ));
     apply (comp_assoc2 ????? (F⎻* ) (G⎻* ) (H⎻* ));
   | apply ((comp_assoc2 ????? (H⎻) (G⎻) (F⎻))^-1);
   | apply ((comp_assoc2 ????? F G H)^-1);
   | apply ((comp_assoc2 ????? H* G* F* ));]
| intros; split; unfold ORelation_composition; simplify; apply id_neutral_left2;
| intros; split; unfold ORelation_composition; simplify; apply id_neutral_right2;]
qed.

definition OAlgebra_of_objs2_OA: objs2 OA → OAlgebra ≝ λx.x.
coercion OAlgebra_of_objs2_OA.

definition ORelation_setoid_of_arrows2_OA: 
  ∀P,Q. arrows2 OA P Q → ORelation_setoid P Q ≝ λP,Q,c.c.
coercion ORelation_setoid_of_arrows2_OA.

prefer coercion Type_OF_objs2.
*)
(* alias symbol "eq" = "setoid1 eq". *)
