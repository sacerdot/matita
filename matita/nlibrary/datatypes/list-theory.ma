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

include "arithmetics/nat.ma".
include "datatypes/list.ma".

ntheorem nil_cons:
  ∀A:Type[0].∀l:list A.∀a:A. a::l ≠ [].
#A;#l;#a; @; #H; ndestruct;
nqed.

ntheorem append_nil: ∀A:Type.∀l:list A.l @ □ = l.
#A;#l;nelim l;//;
#a;#l1;#IH;nnormalize;//;
nqed.

ntheorem associative_append: ∀A:Type[0].associative (list A) (append A).
#A;#x;#y;#z;nelim x
##[//
##|#a;#x1;#H;nnormalize;//]
nqed.

ntheorem cons_append_commute:
  ∀A:Type[0].∀l1,l2:list A.∀a:A.
    a :: (l1 @ l2) = (a :: l1) @ l2.
//;
nqed.

nlemma append_cons: ∀A.∀a:A.∀l,l1. l@(a::l1)=(l@[a])@l1.
#A;#a;#l;#l1;nrewrite > (associative_append ????);//;
nqed.

(*ninductive permutation (A:Type) : list A -> list A -> Prop \def
  | refl : \forall l:list A. permutation ? l l
  | swap : \forall l:list A. \forall x,y:A. 
              permutation ? (x :: y :: l) (y :: x :: l)
  | trans : \forall l1,l2,l3:list A.
              permutation ? l1 l2 -> permut1 ? l2 l3 -> permutation ? l1 l3
with permut1 : list A -> list A -> Prop \def
  | step : \forall l1,l2:list A. \forall x,y:A. 
      permut1 ? (l1 @ (x :: y :: l2)) (l1 @ (y :: x :: l2)).*)

(*

definition x1 \def S O.
definition x2 \def S x1.
definition x3 \def S x2.
   
theorem tmp : permutation nat (x1 :: x2 :: x3 :: []) (x1 :: x3 :: x2 :: []).
  apply (trans ? (x1 :: x2 :: x3 :: []) (x1 :: x2 :: x3 :: []) ?).
  apply refl.
  apply (step ? (x1::[]) [] x2 x3).
  qed. 

theorem nil_append_nil_both:
  \forall A:Type.\forall l1,l2:list A.
    l1 @ l2 = [] \to l1 = [] \land l2 = [].

theorem test_notation: [O; S O; S (S O)] = O :: S O :: S (S O) :: []. 
reflexivity.
qed.

theorem test_append: [O;O;O;O;O;O] = [O;O;O] @ [O;O] @ [O].
simplify.
reflexivity.
qed.

*)

nlet rec nth A l d n on n ≝
  match n with
  [ O ⇒ match l with
        [ nil ⇒ d
        | cons (x : A) _ ⇒ x ]
  | S n' ⇒ nth A (tail ? l) d n'].

nlet rec map A B f l on l ≝
  match l with [ nil ⇒ nil B | cons (x:A) tl ⇒ f x :: map A B f tl ]. 

nlet rec foldr (A,B:Type[0]) (f : A → B → B) (b:B) l on l ≝ 
  match l with [ nil ⇒ b | cons (a:A) tl ⇒ f a (foldr A B f b tl) ].
   
ndefinition length ≝ λT:Type[0].λl:list T.foldr T nat (λx,c.S c) O l.

ndefinition filter ≝ 
  λT:Type[0].λl:list T.λp:T → bool.
  foldr T (list T) 
    (λx,l0.match (p x) with [ true => x::l0 | false => l0]) [] l.

ndefinition iota : nat → nat → list nat ≝
  λn,m. nat_rect_Type0 (λ_.list ?) (nil ?) (λx,acc.cons ? (n+x) acc) m.
  
(* ### induction principle for functions visiting 2 lists in parallel *)
nlemma list_ind2 : 
  ∀T1,T2:Type[0].∀l1:list T1.∀l2:list T2.∀P:list T1 → list T2 → Prop.
  length ? l1 = length ? l2 →
  (P (nil ?) (nil ?)) → 
  (∀tl1,tl2,hd1,hd2. P tl1 tl2 → P (hd1::tl1) (hd2::tl2)) → 
  P l1 l2.
#T1;#T2;#l1;#l2;#P;#Hl;#Pnil;#Pcons;
ngeneralize in match Hl; ngeneralize in match l2;
nelim l1
##[#l2;ncases l2;//;
   nnormalize;#t2;#tl2;#H;ndestruct;
##|#t1;#tl1;#IH;#l2;ncases l2
   ##[nnormalize;#H;ndestruct
   ##|#t2;#tl2;#H;napply Pcons;napply IH;nnormalize in H;ndestruct;//]
##]
nqed.

nlemma eq_map : ∀A,B,f,g,l. (∀x.f x = g x) → map A B f l = map A B g l.
#A;#B;#f;#g;#l;#Efg;
nelim l; nnormalize;//;
nqed.

nlemma le_length_filter : ∀A,l,p.length A (filter A l p) ≤ length A l.
#A;#l;#p;nelim l;nnormalize
##[//
##|#a;#tl;#IH;ncases (p a);nnormalize;
   ##[napply le_S_S;//;
   ##|@2;//]
##]
nqed.

nlemma length_append : ∀A,l,m.length A (l@m) = length A l + length A m.
#A;#l;#m;nelim l;
##[//
##|#H;#tl;#IH;nnormalize;nrewrite < IH;//]
nqed.

ninductive in_list (A:Type): A → (list A) → Prop ≝
| in_list_head : ∀ x,l.(in_list A x (x::l))
| in_list_cons : ∀ x,y,l.(in_list A x l) → (in_list A x (y::l)).

ndefinition incl : \forall A.(list A) \to (list A) →Prop \def
  \lambda A,l,m.\forall x.in_list A x l \to in_list A x m.
  
notation "hvbox(a break ∉ b)" non associative with precedence 45
for @{ 'notmem $a $b }. 
  
interpretation "list member" 'mem x l = (in_list ? x l).
interpretation "list not member" 'notmem x l = (Not (in_list ? x l)).
interpretation "list inclusion" 'subseteq l1 l2 = (incl ? l1 l2).
  
naxiom not_in_list_nil : \forall A,x.\lnot in_list A x [].
(*intros.unfold.intro.inversion H
  [intros;lapply (sym_eq ? ? ? H2);destruct Hletin
  |intros;destruct H4]
qed.*)

naxiom in_list_cons_case : \forall A,x,a,l.in_list A x (a::l) \to
                          x = a \lor in_list A x l.
(*intros;inversion H;intros
  [destruct H2;left;reflexivity
  |destruct H4;right;assumption]
qed.*)

naxiom in_list_tail : \forall l,x,y.
      in_list nat x (y::l) \to x \neq y \to in_list nat x l.
(*intros 4;elim (in_list_cons_case ? ? ? ? H)
  [elim (H2 H1)
  |assumption]
qed.*)

naxiom in_list_singleton_to_eq : \forall A,x,y.in_list A x [y] \to x = y.
(*intros;elim (in_list_cons_case ? ? ? ? H)
  [assumption
  |elim (not_in_list_nil ? ? H1)]
qed.*)

naxiom in_list_to_in_list_append_l: \forall A.\forall x:A.
\forall l1,l2.in_list ? x l1 \to in_list ? x (l1@l2).
(*intros.
elim H;simplify
  [apply in_list_head
  |apply in_list_cons;assumption
  ]
qed.*)

naxiom in_list_to_in_list_append_r: \forall A.\forall x:A.
\forall l1,l2. in_list ? x l2 \to in_list ? x (l1@l2).
(*intros 3.
elim l1;simplify
  [assumption
  |apply in_list_cons;apply H;assumption
  ]
qed.*)

naxiom in_list_append_to_or_in_list: \forall A:Type.\forall x:A.
\forall l,l1. in_list ? x (l@l1) \to in_list ? x l \lor in_list ? x l1.
(*intros 3.
elim l
  [right.apply H
  |simplify in H1.inversion H1;intros; destruct;
    [left.apply in_list_head
    | elim (H l2)
      [left.apply in_list_cons. assumption
      |right.assumption
      |assumption
      ]
    ]
  ]
qed.*)

nlet rec mem (A:Type) (eq: A → A → bool) x (l: list A) on l ≝
 match l with
  [ nil ⇒ false
  | (cons a l') ⇒
    match eq x a with
     [ true ⇒ true
     | false ⇒ mem A eq x l'
     ]
  ].
  
naxiom mem_true_to_in_list :
  \forall A,equ.
  (\forall x,y.equ x y = true \to x = y) \to
  \forall x,l.mem A equ x l = true \to in_list A x l.
(* intros 5.elim l
  [simplify in H1;destruct H1
  |simplify in H2;apply (bool_elim ? (equ x a))
     [intro;rewrite > (H ? ? H3);apply in_list_head
     |intro;rewrite > H3 in H2;simplify in H2;
      apply in_list_cons;apply H1;assumption]]
qed.*)

naxiom in_list_to_mem_true :
  \forall A,equ.
  (\forall x.equ x x = true) \to
  \forall x,l.in_list A x l \to mem A equ x l = true.
(*intros 5.elim l
  [elim (not_in_list_nil ? ? H1)
  |elim H2
    [simplify;rewrite > H;reflexivity
    |simplify;rewrite > H4;apply (bool_elim ? (equ a1 a2));intro;reflexivity]].
qed.*)

naxiom in_list_filter_to_p_true : \forall A,l,x,p.
in_list A x (filter A l p) \to p x = true.
(* intros 4;elim l
  [simplify in H;elim (not_in_list_nil ? ? H)
  |simplify in H1;apply (bool_elim ? (p a));intro;rewrite > H2 in H1;
   simplify in H1
     [elim (in_list_cons_case ? ? ? ? H1)
        [rewrite > H3;assumption
        |apply (H H3)]
     |apply (H H1)]]
qed.*)

naxiom in_list_filter : \forall A,l,p,x.in_list A x (filter A l p) \to in_list A x l.
(*intros 4;elim l
  [simplify in H;elim (not_in_list_nil ? ? H)
  |simplify in H1;apply (bool_elim ? (p a));intro;rewrite > H2 in H1;
   simplify in H1
     [elim (in_list_cons_case ? ? ? ? H1)
        [rewrite > H3;apply in_list_head
        |apply in_list_cons;apply H;assumption]
     |apply in_list_cons;apply H;assumption]]
qed.*)

naxiom in_list_filter_r : \forall A,l,p,x.
              in_list A x l \to p x = true \to in_list A x (filter A l p).
(* intros 4;elim l
  [elim (not_in_list_nil ? ? H)
  |elim (in_list_cons_case ? ? ? ? H1)
     [rewrite < H3;simplify;rewrite > H2;simplify;apply in_list_head
     |simplify;apply (bool_elim ? (p a));intro;simplify;
        [apply in_list_cons;apply H;assumption
        |apply H;assumption]]]
qed.*)

naxiom incl_A_A: ∀T,A.incl T A A.
(*intros.unfold incl.intros.assumption.
qed.*)

naxiom incl_append_l : ∀T,A,B.incl T A (A @ B).
(*unfold incl; intros;autobatch.
qed.*)

naxiom incl_append_r : ∀T,A,B.incl T B (A @ B).
(*unfold incl; intros;autobatch.
qed.*)

naxiom incl_cons : ∀T,A,B,x.incl T A B → incl T (x::A) (x::B).
(*unfold incl; intros;elim (in_list_cons_case ? ? ? ? H1);autobatch.
qed.*)

