(* (C) 2014 Luca Bressan *)

include "notations.ma".

universe constraint Type[0] < Type[1].
universe constraint Type[1] < Type[2].

notation "'cl'" with precedence 90 for @{ Type[1] }.
notation "'st'" with precedence 90 for @{ Type[0] }.
notation "'prop'" with precedence 90 for @{ CProp[1] }.
notation "'props'" with precedence 90 for @{ CProp[0] }.

record Sigma (B: cl) (C: B → cl) : cl ≝
 { Sig1: B
 ; Sig2: C Sig1
 }.
interpretation "Strong Indexed Sum" 'sigma x = (Sigma ? x).
interpretation "Strong Indexed Sum constructor" 'mk_sigma x y = (mk_Sigma ?? x y).
interpretation "First projection of Strong Indexed Sum" 'sig1 x = (Sig1 ?? x).
interpretation "Second projection of Strong Indexed Sum" 'sig2 x = (Sig2 ?? x).

definition Times: cl → cl → cl ≝
 λB,C. Sigma B (λ_. C).
interpretation "Binary collection product" 'times B C = (Times B C).

inductive n0: st ≝ .

inductive n1: st ≝ 
 star: n1.
interpretation "Element of the singleton" 'star = star.

record sigma (B: st) (C : B → st) : st ≝
 { sig1: B
 ; sig2: C sig1
 }.
interpretation "Strong Indexed Sum set" 'sigma x = (sigma ? x).
interpretation "Strong Indexed Sum set constructor" 'mk_sigma x y = (mk_sigma ?? x y).
interpretation "First projection of Strong Indexed Sum set" 'sig1 x = (sig1 ?? x).
interpretation "Second projection of Strong Indexed Sum set" 'sig2 x = (sig2 ?? x).

definition times: st → st → st ≝
 λB,C. sigma B (λ_. C).
interpretation "Binary set product" 'times B C = (times B C).

inductive list (C: st) : st (*CSC: Type[0]*) ≝ 
   epsilon: list C
 | cons: list C → C → list C.
interpretation "Empty list" 'epsilon = (epsilon ?).
interpretation "List constructor" 'cons l c = (cons ? l c).

inductive plus (B: st) (C: st) : st ≝ 
   inl: B → plus B C
 | inr: C → plus B C.
interpretation "Disjoint Sum set" 'plus B C = (plus B C).  

inductive Falsum: prop ≝ .
interpretation "Falsum" 'falsum = Falsum.

inductive Disj (B: prop) (C: prop) : prop ≝ 
   lOr: B → Disj B C
 | rOr: C → Disj B C.
interpretation "Disjunction" 'disj B C = (Disj B C).

record Conj (B: prop) (C: prop) : prop ≝ 
 { Conj1: B
 ; Conj2: C
 }.
interpretation "Conjunction" 'conj B C = (Conj B C).

definition Implies: prop → prop → prop ≝
 λB,C: prop. B → C.
interpretation "Implication" 'implies B C = (Implies B C).

record Exists (B: cl) (C: B → prop) : prop ≝ 
 { Ex1: B
 ; Ex2: C Ex1
 }.
interpretation "Existential quantification" 'exists x = (Exists ? x).
interpretation "Existential quantification constructor" 'mk_exists x y = (mk_Exists ?? x y).

definition Forall: ∀B: cl. (B → prop) → prop ≝ λB,C. ∀b: B. C b.

inductive Id (A: cl) (a: A) : A → prop ≝
 Reflexivity: Id A a a.
interpretation "Propositional Equality" 'id a b = (Id ? a b).
interpretation "Reflexivity in Extensional Collections" 'rfl x = (Reflexivity ? x).

definition Verum: prop ≝ Implies Falsum Falsum.
interpretation "Verum" 'verum = Verum.

inductive falsum: props ≝ .
interpretation "Small Falsum" 'falsum = falsum.

inductive disj (B: props) (C: props) : props ≝ 
   lor: B → disj B C
 | ror: C → disj B C.
interpretation "Small Disjunction" 'disj B C = (disj B C).

record conj (B: props) (C: props) : props ≝ 
 { conj1: B
 ; conj2: C
 }.
interpretation "Small Conjunction" 'conj B C = (conj B C).

definition implies: props → props → props ≝
 λB,C. B → C.
interpretation "Small Implication" 'implies B C = (implies B C).

record exists (B: st) (C: B → props) : props ≝ 
 { exs1: B
 ; exs2: C exs1
 }.
interpretation "Small Existential quantification" 'exists x = (exists ? x).
interpretation "Small Existential quantification constructor" 'mk_exists x y = (mk_exists ?? x y).

definition forall: ∀B: st. (B → props) → props ≝ λB,C. ∀b: B. C b.

inductive id (A: st) (a: A) : A → props ≝
 reflexivity: id A a a.
interpretation "Small Propositional Equality" 'id a b = (id ? a b).
interpretation "Reflexivity in Extensional Sets" 'rfl x = (reflexivity ? x).

definition verum: props ≝ implies falsum falsum.
interpretation "Verum" 'verum = verum.

definition fun_to_props: st → cl ≝ λB. B → props.

lemma Symmetry: ∀A: cl. ∀x,x': A. x = x' → x' = x.
 #A #x #x' * %
qed.
interpretation "Symmetry in Intensional Collections" 'sym d = (Symmetry ??? d).

lemma Transitivity: ∀A: cl. ∀x,x',x'': A. x = x' → x' = x'' → x = x''.
 #A #x #x' #x'' * * %
qed.
interpretation "Transitivity in Intensional Collections" 'tra d = (Transitivity ???? d).

lemma rewrite_l: ∀A: st. ∀x: A. ∀P: A → props. P x → ∀y: A. x = y → P y.
 #A #x #P #h #y * @h
qed.

notation "hvbox(> h)" 
 non associative with precedence 45
 for @{ 'rewrite_l $h }.
interpretation "Rewrite left" 'rewrite_l h = (rewrite_l ????? h).

lemma symmetry: ∀A: st. ∀x,x': A. x = x' → x' = x.
 #A #x #x' * %
qed.
interpretation "Symmetry in Intensional Sets" 'sym d = (symmetry ??? d).

notation "hvbox(< h)" 
 non associative with precedence 45
 for @{ 'rewrite_r $h }.
interpretation "Rewrite right" 'rewrite_r h = (rewrite_l ????? (symmetry ??? h)).

lemma transitivity: ∀A: st. ∀x,x',x'': A. x = x' → x' = x'' → x = x''.
 #A #x #x' #x'' * * %
qed.
interpretation "Transitivity in Intensional Sets" 'tra d = (transitivity ???? d).

definition lift_to_list: ∀A,A': st. (A → A') → list A → list A' ≝ 
 λA,A',f. list_rect_Type0 … (λ_. list A') ϵ (λl,x,l'. ⌈l', f x⌉).

definition proj_l: ∀B,C: st. B → plus B C → B ≝ 
 λB,C,b'. plus_rect_Type0 B C (λ_. B) (λb. b) (λ_. b').

definition proj_r: ∀B,C: st. C → plus B C → C ≝ 
 λB,C,c'. plus_rect_Type0 B C (λ_. C) (λ_. c') (λc. c).

lemma injectivity_inl: ∀B,C: st. ∀x,x'. inl B C x = inl B C x' → x = x'.
 #B #C #x #x'
 @(rewrite_l … (inl … x) (λz. proj_l … x (inl … x) = proj_l … x z)
   (ı(proj_l … x (inl … x))) (inl … x'))
qed.

lemma injectivity_inr: ∀B,C: st. ∀y,y'. inr B C y = inr B C y' → y = y'.
 #B #C #y #y'
 @(rewrite_l … (inr … y) (λz. proj_r … y (inr … y) = proj_r … y z)
   (ı(proj_r … y (inr … y))) (inr … y'))
qed.

lemma injectivity_cons1: ∀C: st. ∀l,l': list C. ∀c,c': C. ⌈l, c⌉ = ⌈l', c'⌉ → l = l'.
 #C #l1 #l2 #c1 #c2
 @(rewrite_l … ⌈l1, c1⌉
   (list_rect_Type1 … (λ_. props) ⊥ (λl,c,h. l1 = l))
   (ı…) ⌈l2, c2⌉)
qed.

lemma injectivity_cons2: ∀C: st. ∀l,l': list C. ∀c,c': C. ⌈l, c⌉ = ⌈l', c'⌉ → c = c'.
 #C #l1 #l2 #c1 #c2
 @(rewrite_l … ⌈l1, c1⌉
   (list_rect_Type1 … (λ_. props) ⊥ (λl,c,h. c1 = c))
   (ı…) ⌈l2, c2⌉)
qed.

lemma plus_clash: ∀B,C: st. ∀b: B. ∀c: C. inl … b = inr … c → ⊥.
 #B #C #b #c #h
 @(rewrite_l … (inl … b) (plus_rect_Type1 … (λ_. props) (λ_. ⊤) (λ_. ⊥))
   (λx. x) … h)
qed.

lemma list_clash: ∀C: st. ∀l: list C. ∀c: C. ϵ = ⌈l, c⌉ → ⊥.
 #C #l #c #h
 @(rewrite_l … ϵ (list_rect_Type1 … (λ_. props) ⊤ (λ_,_,_. ⊥))
   (λx. x) … h)
qed.

definition nat: st ≝ list n1.
definition zero: nat ≝ ϵ.
definition succ: nat → nat ≝ λn. cons … n ⋆.
definition nat_rect_Type0: ∀Q: nat → st. Q zero → (∀n. Q n → Q (succ n)) → ∀n. Q n.
 #Q #h0 #hi @list_rect_Type0 [ @h0 | #n @n1_rect_Type0 @(hi n) ]
qed.
definition nat_rect_Type1: ∀Q: nat → cl. Q zero → (∀n. Q n → Q (succ n)) → ∀n. Q n.
 #Q #h0 #hi @list_rect_Type1 [ @h0 | #n @n1_rect_Type1 @(hi n) ]
qed.
definition nat_rect_CProp0: ∀Q: nat → props. Q zero → (∀n. Q n → Q (succ n)) → ∀n. Q n.
 #Q #h0 #hi @list_rect_CProp0 [ @h0 | #n @n1_rect_CProp0 @(hi n) ]
qed.
definition nat_rect_CProp1: ∀Q: nat → prop. Q zero → (∀n. Q n → Q (succ n)) → ∀n. Q n.
 #Q #h0 #hi @list_rect_CProp1 [ @h0 | #n @n1_rect_CProp1 @(hi n) ]
qed.

inductive De (I: st) : st ≝
 | c_unit: De I
 | c_ev: I → De I
 | c_times: De I → De I → De I
 | c_plus: De I → De I → De I.

definition int: ∀I: st. De I → (I → st) → st.
 #I @De_rect_Type1
 [ #_ @n1
 | #i #X @(X i)
 | #L #R #intL #intR #X @((intL X)×(intR X))
 | #L #R #intL #intR #X @((intL X)+(intR X))
 ]
qed.

definition napply: nat → (st → st) → st → st.
 @nat_rect_Type1
 [ #F #X @X
 | #_ #F' #F #X @(F' F X)
 ]
qed.

definition mu: ∀I: st. (I → De I) → I → st.
 #I #F #i @(Σn: nat. napply n (λX: st. int I (F i) (λ_. X)) n0)
qed.

definition is_c_unit: ∀I: st. ∀F: De I. props.
 #I * [ @verum | #_ @falsum | 3,4: #_ #_ @falsum ]
qed.

lemma De_clash_unit_ev: ∀I: st. ∀i: I. c_ev I i = c_unit I → falsum.
 #I #i #h
 @(rewrite_l (De I) (c_unit I) (is_c_unit I) (λx. x) (c_ev I i) h⁻¹)
qed.
lemma De_clash_unit_times: ∀I: st. ∀F,G: De I. c_times I F G = c_unit I → falsum.
 #I #F #G #h
 @(rewrite_l (De I) (c_unit I) (is_c_unit I) (λx. x) (c_times I F G) h⁻¹)
qed.
lemma De_clash_unit_plus: ∀I: st. ∀F,G: De I. c_plus I F G = c_unit I → falsum.
 #I #F #G #h
 @(rewrite_l (De I) (c_unit I) (is_c_unit I) (λx. x) (c_plus I F G) h⁻¹)
qed.

inductive mu_ (I: st) (F: I → De I) : I → De I → st ≝
   fold_unit: ∀i: I. mu_ I F i (c_unit I)
 | fold_ev: ∀i,i': I. mu_ I F i' (F i') → mu_ I F i (c_ev I i')
 | fold_times: ∀i: I. ∀G1,G2: De I. mu_ I F i G1 → mu_ I F i G2 → mu_ I F i (c_times I G1 G2)
 | fold_plusL: ∀i: I. ∀G1,G2: De I. mu_ I F i G1 → mu_ I F i (c_plus I G1 G2)
 | fold_plusR: ∀i: I. ∀G1,G2: De I. mu_ I F i G2 → mu_ I F i (c_plus I G1 G2).

