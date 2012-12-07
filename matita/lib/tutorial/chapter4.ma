(* 
Naif Set Theory

*)
include "basics/types.ma".
include "basics/bool.ma".
(* 
In this Chapter we shall develop a naif theory of sets represented as 
characteristic predicates over some universe A, that is as objects of type 
A→Prop. 
For instance the empty set is defined by the always false function: *)

definition empty_set ≝ λA:Type[0].λa:A.False.
notation "\emptyv" non associative with precedence 90 for @{'empty_set}.
interpretation "empty set" 'empty_set = (empty_set ?).

(* Similarly, a singleton set contaning containing an element a, is defined
by by the characteristic function asserting equality with a *)

definition singleton ≝ λA.λx,a:A.x=a.
(* notation "{x}" non associative with precedence 90 for @{'sing_lang $x}. *)
interpretation "singleton" 'singl x = (singleton ? x).

(* The membership relation between an element of type A and a set S:A →Prop is
simply the predicate resulting from the application of S to a.
The operations of union, intersection, complement and substraction 
are easily defined in terms of the propositional connectives of dijunction,
conjunction and negation *)

definition union : ∀A:Type[0].∀P,Q.A → Prop ≝ λA,P,Q,a.P a ∨ Q a.
interpretation "union" 'union a b = (union ? a b).

definition intersection : ∀A:Type[0].∀P,Q.A→Prop ≝ λA,P,Q,a.P a ∧ Q a.
interpretation "intersection" 'intersects a b = (intersection ? a b).

definition complement ≝ λU:Type[0].λA:U → Prop.λw.¬ A w.
interpretation "complement" 'not a = (complement ? a).

definition substraction := λU:Type[0].λA,B:U → Prop.λw.A w ∧ ¬ B w.
interpretation "substraction" 'minus a b = (substraction ? a b).

(* Finally, we use implication to define the inclusion relation between
sets *)

definition subset: ∀A:Type[0].∀P,Q:A→Prop.Prop ≝ λA,P,Q.∀a:A.(P a → Q a).
interpretation "subset" 'subseteq a b = (subset ? a b).

(* 
Set Equality

Two sets are equals if and only if they have the same elements, that is,
if the two characteristic functions are extensionally equivalent: *) 

definition eqP ≝ λA:Type[0].λP,Q:A → Prop.∀a:A.P a ↔ Q a.
notation "A =1 B" non associative with precedence 45 for @{'eqP $A $B}.
interpretation "extensional equality" 'eqP a b = (eqP ? a b).

(*
This notion of equality is different from the intensional equality of
functions; the fact it defines an equivalence relation must be explicitly 
proved: *)

lemma eqP_sym: ∀U.∀A,B:U →Prop. 
  A =1 B → B =1 A.
#U #A #B #eqAB #a @iff_sym @eqAB qed.
 
lemma eqP_trans: ∀U.∀A,B,C:U →Prop. 
  A =1 B → B =1 C → A =1 C.
#U #A #B #C #eqAB #eqBC #a @iff_trans // qed.

(* For the same reason, we must also prove that all the operations behave well
with respect to eqP: *)

lemma eqP_union_r: ∀U.∀A,B,C:U →Prop. 
  A =1 C  → A ∪ B =1 C ∪ B.
#U #A #B #C #eqAB #a @iff_or_r @eqAB qed.
  
lemma eqP_union_l: ∀U.∀A,B,C:U →Prop. 
  B =1 C  → A ∪ B =1 A ∪ C.
#U #A #B #C #eqBC #a @iff_or_l @eqBC qed.
  
lemma eqP_intersect_r: ∀U.∀A,B,C:U →Prop. 
  A =1 C  → A ∩ B =1 C ∩ B.
#U #A #B #C #eqAB #a @iff_and_r @eqAB qed.
  
lemma eqP_intersect_l: ∀U.∀A,B,C:U →Prop. 
  B =1 C  → A ∩ B =1 A ∩ C.
#U #A #B #C #eqBC #a @iff_and_l @eqBC qed.

lemma eqP_substract_r: ∀U.∀A,B,C:U →Prop. 
  A =1 C  → A - B =1 C - B.
#U #A #B #C #eqAB #a @iff_and_r @eqAB qed.
  
lemma eqP_substract_l: ∀U.∀A,B,C:U →Prop. 
  B =1 C  → A - B =1 A - C.
#U #A #B #C #eqBC #a @iff_and_l /2/ qed.

(* 
Simple properties of sets

We can now prove several properties of the previous set-theoretic operations. 
In particular, union is commutative and associative, and the empty set is an 
identity element: *)

lemma union_empty_r: ∀U.∀A:U→Prop. 
  A ∪ ∅ =1 A.
#U #A #w % [* // normalize #abs @False_ind /2/ | /2/]
qed.

lemma union_comm : ∀U.∀A,B:U →Prop. 
  A ∪ B =1 B ∪ A.
#U #A #B #a % * /2/ qed. 

lemma union_assoc: ∀U.∀A,B,C:U → Prop. 
  A ∪ B ∪ C =1 A ∪ (B ∪ C).
#S #A #B #C #w % [* [* /3/ | /3/ ] | * [/3/ | * /3/]
qed.   

(* In the same way we prove commutativity and associativity for set 
interesection *)

lemma cap_comm : ∀U.∀A,B:U →Prop. 
  A ∩ B =1 B ∩ A.
#U #A #B #a % * /2/ qed. 

lemma cap_assoc: ∀U.∀A,B,C:U→Prop.
  A ∩ (B ∩ C) =1 (A ∩ B) ∩ C.
#U #A #B #C #w % [ * #Aw * /3/ | * * /3/ ]
qed.

(* We can also easily prove idempotency for union and intersection *)

lemma union_idemp: ∀U.∀A:U →Prop. 
  A  ∪ A =1 A.
#U #A #a % [* // | /2/] qed. 

lemma cap_idemp: ∀U.∀A:U →Prop. 
  A ∩ A =1 A.
#U #A #a % [* // | /2/] qed. 

(* We conclude our examples with a couple of distributivity theorems, and a 
characterization of substraction in terms of interesection and complementation. *)

lemma distribute_intersect : ∀U.∀A,B,C:U→Prop. 
  (A ∪ B) ∩ C =1 (A ∩ C) ∪ (B ∩ C).
#U #A #B #C #w % [* * /3/ | * * /3/] 
qed.
  
lemma distribute_substract : ∀U.∀A,B,C:U→Prop. 
  (A ∪ B) - C =1 (A - C) ∪ (B - C).
#U #A #B #C #w % [* * /3/ | * * /3/] 
qed.

lemma substract_def:∀U.∀A,B:U→Prop. A-B =1 A ∩ ¬B.
#U #A #B #w normalize /2/
qed.

(* 
Bool vs. Prop

In several situation it is important to assume to have a decidable equality 
between elements of a set U, namely a boolean function eqb: U→U→bool such that
for any pair of elements a and b in U, (eqb x y) is true if and only if x=y. 
A set equipped with such an equality is called a DeqSet: *)

record DeqSet : Type[1] ≝ { carr :> Type[0];
   eqb: carr → carr → bool;
   eqb_true: ∀x,y. (eqb x y = true) ↔ (x = y)
}.

(* We use the notation == to denote the decidable equality, to distinguish it
from the propositional equality. In particular, a term of the form a==b is a 
boolean, while a=b is a proposition. *)

notation "a == b" non associative with precedence 45 for @{ 'eqb $a $b }.
interpretation "eqb" 'eqb a b = (eqb ? a b).

(* 
Small Scale Reflection

It is convenient to have a simple way to reflect a proof of the fact 
that (eqb a b) is true into a proof of the proposition (a = b); to this aim, 
we introduce two operators "\P" and "\b". *)

notation "\P H" non associative with precedence 90 
  for @{(proj1 … (eqb_true ???) $H)}. 

notation "\b H" non associative with precedence 90 
  for @{(proj2 … (eqb_true ???) $H)}. 
  
(* If H:eqb a b = true, then \P H: a = b, and conversely if h:a = b, then
\b h: eqb a b = true. Let us see an example of their use: the following 
statement asserts that we can reflect a proof that eqb a b is false into
a proof of the proposition a ≠ b. *)

lemma eqb_false: ∀S:DeqSet.∀a,b:S. 
  (eqb ? a b) = false ↔ a ≠ b.

(* We start the proof introducing the hypothesis, and then split the "if" and
"only if" cases *)
 
#S #a #b % #H 

(* The latter is easily reduced to prove the goal true=false under the assumption
H1: a = b *)
  [@(not_to_not … not_eq_true_false) #H1 
  
(* since by assumption H false is equal to (a==b), by rewriting we obtain the goal 
true=(a==b) that is just the boolean version of H1 *) 

  <H @sym_eq @(\b H1)

(* In the "if" case, we proceed by cases over the boolean equality (a==b); if 
(a==b) is false, the goal is trivial; the other case is absurd, since if (a==b) is
true, then by reflection a=b, while by hypothesis a≠b *)
  
 |cases (true_or_false (eqb ? a b)) // #H1 @False_ind @(absurd … (\P H1) H)
  ]
qed.
 
(* We also introduce two operators "\Pf" and "\bf" to reflect a proof
of (a==b)=false into a proof of a≠b, and vice-versa *) 

notation "\Pf H" non associative with precedence 90 
  for @{(proj1 … (eqb_false ???) $H)}. 

notation "\bf H" non associative with precedence 90 
  for @{(proj2 … (eqb_false ???) $H)}. 

(* The following statement proves that propositional equality in a 
DeqSet is decidable in the traditional sense, namely either a=b or a≠b *)

 lemma dec_eq: ∀S:DeqSet.∀a,b:S. a = b ∨ a ≠ b.
#S #a #b cases (true_or_false (eqb ? a b)) #H
  [%1 @(\P H) | %2 @(\Pf H)]
qed.

(* 
Unification Hints

A simple example of a set with a decidable equality is bool. We first define 
the boolean equality beqb, that is just the xand function, then prove that 
beqb b1 b2 is true if and only if b1=b2, and finally build the type DeqBool by 
instantiating the DeqSet record with the previous information *)

definition beqb ≝ λb1,b2.
  match b1 with [ true ⇒ b2 | false ⇒ notb b2].

notation < "a == b" non associative with precedence 45 for @{beqb $a $b }.

lemma beqb_true: ∀b1,b2. iff (beqb b1 b2 = true) (b1 = b2).
#b1 #b2 cases b1 cases b2 normalize /2/
qed. 

definition DeqBool ≝ mk_DeqSet bool beqb beqb_true.

(* At this point, we would expect to be able to prove things like the
following: for any boolean b, if b==false is true then b=false. 
Unfortunately, this would not work, unless we declare b of type 
DeqBool (change the type in the following statement and see what 
happens). *)

example exhint: ∀b:DeqBool. (b==false) = true → b=false.
#b #H @(\P H) 
qed.

(* The point is that == expects in input a pair of objects whose type must be the 
carrier of a DeqSet; bool is indeed the carrier of DeqBool, but the type inference 
system has no knowledge of it (it is an information that has been supplied by the 
user, and stored somewhere in the library). More explicitly, the type inference 
inference system, would face an unification problem consisting to unify bool 
against the carrier of something (a metavaribale) and it has no way to synthetize 
the answer. To solve this kind of situations, matita provides a mechanism to hint 
the system the expected solution. A unification hint is a kind of rule, whose rhd 
is the unification problem, containing some metavariables X1, ..., Xn, and whose 
left hand side is the solution suggested to the system, in the form of equations 
Xi=Mi. The hint is accepted by the system if and only the solution is correct, that
is, if it is a unifier for the given problem.
To make an example, in the previous case, the unification problem is bool = carr X,
and the hint is to take X= mk_DeqSet bool beqb true. The hint is correct, since 
bool is convertible with (carr (mk_DeqSet bool beb true)). *)

alias symbol "hint_decl" (instance 1) = "hint_decl_Type1".

unification hint  0 ≔ ; 
    X ≟ mk_DeqSet bool beqb beqb_true
(* ---------------------------------------- *) ⊢ 
    bool ≡ carr X.
    
unification hint  0 ≔ b1,b2:bool; 
    X ≟ mk_DeqSet bool beqb beqb_true
(* ---------------------------------------- *) ⊢ 
    beqb b1 b2 ≡ eqb X b1 b2.
    
(* After having provided the previous hints, we may rewrite example exhint 
declaring b of type bool. *)
 
example exhint1: ∀b:bool. (b == false) = true → b = false. 
#b #H @(\P H)
qed.

(* The cartesian product of two DeqSets is still a DeqSet. To prove
this, we must as usual define the boolen equality function, and prove
it correctly reflects propositional equality. *)

definition eq_pairs ≝
  λA,B:DeqSet.λp1,p2:A×B.(\fst p1 == \fst p2) ∧ (\snd p1 == \snd p2).

lemma eq_pairs_true: ∀A,B:DeqSet.∀p1,p2:A×B.
  eq_pairs A B p1 p2 = true ↔ p1 = p2.
#A #B * #a1 #b1 * #a2 #b2 %
  [#H cases (andb_true …H) normalize #eqa #eqb >(\P eqa) >(\P eqb) //
  |#H destruct normalize >(\b (refl … a2)) >(\b (refl … b2)) //
  ]
qed.

definition DeqProd ≝ λA,B:DeqSet.
  mk_DeqSet (A×B) (eq_pairs A B) (eq_pairs_true A B).

(* Having an unification problem of the kind T1×T2 = carr X, what kind 
of hint can we give to the system? We expect T1 to be the carrier of a
DeqSet C1, T2 to be the carrier of a DeqSet C2, and X to be DeqProd C1 C2.
This is expressed by the following hint: *)

unification hint  0 ≔ C1,C2; 
    T1 ≟ carr C1,
    T2 ≟ carr C2,
    X ≟ DeqProd C1 C2
(* ---------------------------------------- *) ⊢ 
    T1×T2 ≡ carr X.

unification hint  0 ≔ T1,T2,p1,p2; 
    X ≟ DeqProd T1 T2
(* ---------------------------------------- *) ⊢ 
    eq_pairs T1 T2 p1 p2 ≡ eqb X p1 p2.

example hint2: ∀b1,b2. 
  〈b1,true〉==〈false,b2〉=true → 〈b1,true〉=〈false,b2〉.
#b1 #b2 #H @(\P H).
qed-.