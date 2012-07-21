(*
Polymorphism and Higher Order

*)
include "tutorial/chapter2.ma".
include "basics/bool.ma".

(* Matita supports polymorphic data types. The most typical case are polymorphic
lists, parametric in the type of their elements: *)

inductive list (A:Type[0]) : Type[0] ≝
  | nil: list A
  | cons: A -> list A -> list A.

(* The type notation list A is the type of all lists with elements of type A: 
it is defined by two constructors: a polymorphic empty list (nil A) and a cons 
operation, adding a new head element of type A to a previous list. For instance, 
(list nat) and and (list bool) are lists of natural numbers and booleans, 
respectively. But we can also form more complex data types, like 
(list (list (nat → nat))), that is a list whose elements are lists of functions 
from natural numbers to natural numbers.

Typical elements in (list bool) are for instance,
  nil nat                                    - the empty list of type nat
  cons nat true (nil nat)                    - the list containing true
  cons nat false (cons nat (true (nil nat))) - the list containing false and true
and so on. 

Note that both constructos nil and cons are expecting in input the type parameter:
in this case, bool.
*)

(*
Defining your own notation

We now add a bit of notation, in order to make the syntax more readable. In 
particular, we would like to write [] instead of (nil A) and a::l instead of 
(cons A a l), leaving the system the burden to infer A, whenever possible.
*)

notation "hvbox(hd break :: tl)"
  right associative with precedence 47
  for @{'cons $hd $tl}.

notation "[ list0 x sep ; ]"
  non associative with precedence 90
  for ${fold right @'nil rec acc @{'cons $x $acc}}.

notation "hvbox(l1 break @ l2)"
  right associative with precedence 47
  for @{'append $l1 $l2 }.

interpretation "nil" 'nil = (nil ?).
interpretation "cons" 'cons hd tl = (cons ? hd tl).

(* 
Basic operations on lists

Let us define a few basic functions over lists. Our first example is the 
append function, concatenating two lists l1 and l2. The natural way is to proceed 
by recursion on l1: if it is empty the result is simply l2, while if l1 = hd::tl 
then we recursively append tl and l2 , and then add hd as first element. Note that 
the append function itself is polymorphic, and the first argument it takes in input 
is the type A of the elements of two lists l1 and l2. 
Moreover, since the append function takes in input several parameters, we must also 
specify in the its defintion on which one of them we are recurring: in this case l1.
If not othewise specified, recursion is supposed to act on the first argument of the
function.*)

let rec append A (l1: list A) l2 on l1 ≝ 
  match l1 with
  [ nil ⇒  l2
  | cons hd tl ⇒  hd :: append A tl l2 ].

interpretation "append" 'append l1 l2 = (append ? l1 l2).

(* As usual, the function is executable. For instance, (append A nil l) reduces to
l, as shown by the following example: *)

example nil_append: ∀A.∀l:list A. [] @ l = l.
#A #l normalize // qed.

(* Proving that l @ [] = l is just a bit more complex. The situation is exactly 
the same as for the addition operation of the previous chapter: since append is 
defined by recutsion over the first argument, the computation of l @ [] is stuck, 
and we must proceed by induction on l *) 

lemma append_nil: ∀A.∀l:list A.l @ [] = l.
#A #l (elim l) normalize // qed.

(* similarly, we can define the two functions head and tail. Since we can only define
total functions, we should decide what to do in case the input list is empty. 
For tl, it is natural to return the empty list; for hd, we take in input a default 
element d of type A to return in this case. *)

definition head ≝ λA.λl: list A.λd:A.
  match l with [ nil ⇒ d | cons a _ ⇒ a].

definition tail ≝  λA.λl: list A.
  match l with [ nil ⇒  [] | cons hd tl ⇒  tl].

example ex_head: ∀A.∀a,d,l. head A (a::l) d = a.
#A #a #d #l normalize // qed.

example ex_tail: tail ? (cons ? true []) = [].
normalize // qed.

theorem associative_append: 
∀A.∀l1,l2,l3: list A. (l1 @ l2) @ l3 = l1 @ (l2 @ l3).
#A #l1 #l2 #l3 (elim l1) normalize // qed.

(* Problemi con la notazione *)
lemma a_append: ∀A.∀a.∀l:list A. (a::[]) @ l = a::l.
// qed.

theorem append_cons:
∀A.∀a:A.∀l,l1: list A.l@(a::l1)= (l @ (cons ? a [])) @ l1.
// qed. 

(* Other typical functions over lists are those computing the length 
of a list, and the function returning the nth element *)

let rec length (A:Type[0]) (l:list A) on l ≝ 
match l with 
  [ nil ⇒ O
    | cons a tl ⇒ S (length A tl)].

let rec nth n (A:Type[0]) (l:list A) (d:A)  ≝  
  match n with
    [O ⇒ head A l d
    |S m ⇒ nth m A (tail A l) d].

example ex_length: length ? (cons ? O []) = S O.
normalize // qed.

example ex_nth: nth (S O) ? (cons ? (S O) (cons ? O [])) O = O.
normalize // qed.

(* Proving that the length of l1@l2 is the sum of the lengths of l1
and l2 just requires a trivial induction on the first list. *)

 lemma  length_add: ∀A.∀l1,l2:list A. 
  length ? (l1@l2) = add (length ? l1) (length ? l2).
#A #l1 elim l1 normalize // qed. 

(* 
Comparing Costructors

Let us come to a more interesting question. How can we prove that the empty 
list is different from any list with at least one element, that is from any list 
of the kind (a::l)? We start defining a simple predicate stating if a list is 
empty or not. The predicate is computed by inspection over the list *)

definition is_nil: ∀A:Type[0].list A → Prop ≝
λA.λl.match l with [ nil ⇒ l = [] | cons hd tl ⇒ (l ≠ [])].

(* Next we need a simple result about negation: if you wish to prove ¬P you are
authorized to add P to your hypothesis: *)

lemma neg_aux : ∀P:Prop. (P → ¬P) → ¬P.
#P #PtonegP % /3/ qed. 

theorem diff_cons_nil:
∀A:Type[0].∀l:list A.∀a:A. a::l ≠ [].
#A #l #a @neg_aux #Heq 
(* we start assuming the new hypothesis Heq of type a::l = [] using neg_aux. 
Next we use the change tactic to pass from the current goal a::l≠ [] to the 
expression is_nil a::l, convertible with it. *)
(change with (is_nil ? (a::l))) 
(* Now, we rewrite with Heq, obtaining (is_nil A []), that reduces to the trivial 
goal [] = [] *)
>Heq // qed.

(* As an application of the previous result let us prove that l1@l2 is empty if 
and only if both l1 and l2 are empty. 
The idea is to proceed by cases on l1: if l1=[] the statement is trivial; on the 
other side, if l1 = a::tl, then the hypothesis (a::tl)@l2 = [] is absurd, hence we 
can prove anything from it. 
When we know we can prove both A and ¬A, a sensible way to proceed is to apply 
False_ind: ∀P.False → P to the current goal, that breaks down to prove False, and 
then absurd: ∀A:Prop. A → ¬A → False to reduce to the contradictory cases. 
Usually, you may invoke automation to take care to solve the absurd case. *)

lemma nil_to_nil:  ∀A.∀l1,l2:list A.
  l1@l2 = [] → l1 = [] ∧ l2 = [].
#A #l1 cases l1 normalize /2/ #a #tl #l2 #H @False_ind /2/ qed. 

(* 
Higher Order Functionals

Let us come to some important, higher order, polymorphic functionals 
acting over lists. A typical example is the map function, taking a function
f:A → B, a list l = [a1; a2; ... ; an] and returning the list 
[f a1; f a2; ... ; f an]. *)

let rec map (A,B:Type[0]) (f: A → B) (l:list A) on l: list B ≝
 match l with [ nil ⇒ [] | cons x tl ⇒ f x :: (map A B f tl)].

(* Another major example is the fold function, that taken a list 
l = [a1; a2; ... ;an], a base value b:B, and a function f: A → B → B returns 
(f a1 (f a2 (... (f an b)...))). *)

let rec foldr (A,B:Type[0]) (f:A → B → B) (b:B) (l:list A) on l :B ≝  
  match l with [ nil ⇒ b | cons a l ⇒ f a (foldr A B f b l)].

(* As an example of application of foldr, let us use it to define a filter 
function that given a list l: list A and a boolean test p:A → bool returns the 
sublist of elements satisfying the test. In this case, the result type B of 
foldr should be (list A), the base value is [], and f: A → list A →list A is 
the function that taken x and l returns x::l, if x satisfies the test, and l 
otherwise. We use an if_then_else function included from bool.ma to this purpose. *)

definition filter ≝ 
  λT.λp:T → bool.
  foldr T (list T) (λx,l0. if p x then x::l0 else l0) [].

(* Here are a couple of simple lemmas on the behaviour of the filter function. 
It is often convenient to state such lemmas, in order to be able to use rewriting
as an alternative to reduction in proofs: reduction is a bit difficult to control.
*)

lemma filter_true : ∀A,l,a,p. p a = true → 
  filter A p (a::l) = a :: filter A p l.
#A #l #a #p #pa (elim l) normalize >pa // qed.

lemma filter_false : ∀A,l,a,p. p a = false → 
  filter A p (a::l) = filter A p l.
#A #l #a #p #pa (elim l) normalize >pa normalize // qed.

(* As another example, let us redefine the map function using foldr. The
result type B is (list B), the base value b is [], and the fold function 
of type A → list B → list B is the function mapping a and l to (f a)::l.
*)

definition map_again ≝ λA,B,f,l. foldr A (list B) (λa,l.f a::l) [] l.

(* 
Extensional equality

Can we prove that map_again is "the same" as map? We should first of all
clarify in which sense we expect the two functions to be equal. Equality in
Matita has an intentional meaning: it is the smallest predicate induced by 
convertibility, i.e. syntactical equality up to normalization. From an 
intentional point of view, map and map_again are not functions, but programs,
and they are clearly different. What we would like to say is that the two
programs behave in the same way: this is a different, extensional equality 
that can be defined in the following way. *)

definition ExtEq ≝ λA,B:Type[0].λf,g:A→B.∀a:A.f a = g a.

(* Proving that map and map_again are extentionally equal in the 
previous sense can be proved by a trivial structural induction on the list *)

lemma eq_maps: ∀A,B,f. ExtEq ?? (map A B f) (map_again A B f).
#A #B #f #n (elim n) normalize // qed. 

(* Let us make another remark about extensional equality. It is clear that,
if f is extensionally equal to g, then (map A B f) is extensionally equal to
(map A B g). Let us prove it. *)

theorem eq_map : ∀A,B,f,g. ExtEq A B f g → ExtEq ?? (map A B f) (map A B g).
#A #B #f #g #eqfg
 
(* the relevant point is that we cannot proceed by rewriting f with g via
eqfg, here. Rewriting only works with Matita intensional equality, while here
we are dealing with a different predicate, defined by the user. The right way 
to proceed is to unfold the definition of ExtEq, and work by induction on l, 
as usual when we want to prove extensional equality between functions over 
inductive types; again the rest of the proof is trivial. *)

#l (elim l) normalize // qed.

(*
Big Operators

Building a library of basic functions, it is important to achieve a 
good degree of abstraction and generality, in order to be able to reuse
suitable instances of the same function in different context. This has not
only the obvious benefit of factorizing code, but especially to avoid 
repeating proofs of generic properties over and over again.
A really convenient tool is the following combination of fold and filter,
that essentially allow you to iterate on every subset of a given enumerated
(finite) type, represented as a list. *) 

 let rec fold (A,B:Type[0]) (op:B→B→B) (b:B) (p:A→bool) (f:A→B) (l:list A) on l:B ≝  
 match l with 
  [ nil ⇒ b 
  | cons a l ⇒ if p a then op (f a) (fold A B op b p f l) else
      (fold A B op b p f l)].

(* It is also important to spend a few time to introduce some fancy notation
for these iterators. *)

 notation "\fold  [ op , nil ]_{ ident i ∈ l | p} f"
  with precedence 80
for @{'fold $op $nil (λ${ident i}. $p) (λ${ident i}. $f) $l}.

notation "\fold [ op , nil ]_{ident i ∈ l } f"
  with precedence 80
for @{'fold $op $nil (λ${ident i}.true) (λ${ident i}. $f) $l}.

interpretation "\fold" 'fold op nil p f l = (fold ? ? op nil p f l).

theorem fold_true: 
∀A,B.∀a:A.∀l.∀p.∀op:B→B→B.∀nil.∀f:A→B. p a = true → 
  \fold[op,nil]_{i ∈ a::l| p i} (f i) = 
    op (f a) \fold[op,nil]_{i ∈ l| p i} (f i). 
#A #B #a #l #p #op #nil #f #pa normalize >pa // qed.

theorem fold_false: 
∀A,B.∀a:A.∀l.∀p.∀op:B→B→B.∀nil.∀f.
p a = false → \fold[op,nil]_{i ∈ a::l| p i} (f i) = 
  \fold[op,nil]_{i ∈ l| p i} (f i).
#A #B #a #l #p #op #nil #f #pa normalize >pa // qed.

theorem fold_filter: 
∀A,B.∀a:A.∀l.∀p.∀op:B→B→B.∀nil.∀f:A →B.
  \fold[op,nil]_{i ∈ l| p i} (f i) = 
    \fold[op,nil]_{i ∈ (filter A p l)} (f i).
#A #B #a #l #p #op #nil #f elim l //  
#a #tl #Hind cases(true_or_false (p a)) #pa 
  [ >filter_true // > fold_true // >fold_true //
  | >filter_false // >fold_false // ]
qed.

record Aop (A:Type[0]) (nil:A) : Type[0] ≝
{op :2> A → A → A; 
  nill:∀a. op nil a = a; 
  nilr:∀a. op a nil = a;
  assoc: ∀a,b,c.op a (op b c) = op (op a b) c
}.

theorem fold_sum: ∀A,B. ∀I,J:list A.∀nil.∀op:Aop B nil.∀f:A → B.
 op (\fold[op,nil]_{i ∈ I} (f i)) (\fold[op,nil]_{i ∈ J} (f i)) = 
   \fold[op,nil]_{i ∈ (I@J)} (f i).
#A #B #I #J #nil #op #f (elim I) normalize 
  [>nill//|#a #tl #Hind <assoc //]
qed.