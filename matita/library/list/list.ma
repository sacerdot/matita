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
include "datatypes/bool.ma".
include "higher_order_defs/functions.ma".
include "nat/plus.ma".
include "nat/orders.ma".

inductive list (A:Type) : Type :=
  | nil: list A
  | cons: A -> list A -> list A.

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

(* theorem test_notation: [O; S O; S (S O)] = O :: S O :: S (S O) :: []. *)

theorem nil_cons:
  \forall A:Type.\forall l:list A.\forall a:A. a::l ≠ [].
  intros;
  unfold Not;
  intros;
  destruct H.
qed.

let rec id_list A (l: list A) on l :=
  match l with
  [ nil => []
  | (cons hd tl) => hd :: id_list A tl ].

let rec append A (l1: list A) l2 on l1 :=
  match l1 with
  [ nil => l2
  | (cons hd tl) => hd :: append A tl l2 ].

definition tail := \lambda A:Type. \lambda l: list A.
  match l with
  [ nil => []
  | (cons hd tl) => tl].

interpretation "append" 'append l1 l2 = (append ? l1 l2).

theorem append_nil: \forall A:Type.\forall l:list A.l @ [] = l.
  intros;
  elim l;
  [ reflexivity;
  | simplify;
    rewrite > H;
    reflexivity;
  ]
qed.

theorem associative_append: \forall A:Type.associative (list A) (append A).
  intros; unfold; intros;
  elim x;
  [ simplify;
    reflexivity;
  | simplify;
    rewrite > H;
    reflexivity;
  ]
qed.

theorem cons_append_commute:
  \forall A:Type.\forall l1,l2:list A.\forall a:A.
    a :: (l1 @ l2) = (a :: l1) @ l2.
  intros;
  reflexivity;
qed.

lemma append_cons:\forall A.\forall a:A.\forall l,l1. 
l@(a::l1)=(l@[a])@l1.
intros.
rewrite > associative_append.
reflexivity.
qed.

inductive permutation (A:Type) : list A -> list A -> Prop \def
  | refl : \forall l:list A. permutation ? l l
  | swap : \forall l:list A. \forall x,y:A. 
              permutation ? (x :: y :: l) (y :: x :: l)
  | trans : \forall l1,l2,l3:list A.
              permutation ? l1 l2 -> permut1 ? l2 l3 -> permutation ? l1 l3
with permut1 : list A -> list A -> Prop \def
  | step : \forall l1,l2:list A. \forall x,y:A. 
      permut1 ? (l1 @ (x :: y :: l2)) (l1 @ (y :: x :: l2)).

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

definition nth ≝
  λA:Type.
    let rec nth l d n on n ≝
      match n with
      [ O ⇒
         match l with
         [ nil ⇒ d
         | cons (x : A) _ ⇒ x
         ]
      | S n' ⇒ nth (tail ? l) d n']
    in nth.
  
definition map ≝
  λA,B:Type.λf:A→B.
  let rec map (l : list A) on l : list B ≝
    match l with [ nil ⇒ nil ? | cons x tl ⇒ f x :: (map tl)]
  in map.
  
definition foldr ≝
  λA,B:Type.λf:A→B→B.λb:B.
  let rec foldr (l : list A) on l : B := 
    match l with [ nil ⇒ b | (cons a l) ⇒ f a (foldr l)]
  in foldr.
   
definition length ≝ λT:Type.λl:list T.foldr T nat (λx,c.S c) O l.

definition filter \def 
  \lambda T:Type.\lambda l:list T.\lambda p:T \to bool.
  foldr T (list T) 
    (\lambda x,l0.match (p x) with [ true => x::l0 | false => l0]) [] l.

definition iota : nat → nat → list nat ≝
  λn,m. nat_rect (λ_.list ?) (nil ?) (λx,acc.cons ? (n+x) acc) m.
  
(* ### induction principle for functions visiting 2 lists in parallel *)
lemma list_ind2 : 
  ∀T1,T2:Type.∀l1:list T1.∀l2:list T2.∀P:list T1 → list T2 → Prop.
  length ? l1 = length ? l2 →
  (P (nil ?) (nil ?)) → 
  (∀tl1,tl2,hd1,hd2. P tl1 tl2 → P (hd1::tl1) (hd2::tl2)) → 
  P l1 l2.
intros (T1 T2 l1 l2 P Hl Pnil Pcons);
elim l1 in Hl l2 ⊢ % 1 (l2 x1); [ cases l2; intros (Hl); [assumption| simplify in Hl; destruct Hl]]
intros 3 (tl1 IH l2); cases l2; [1: simplify; intros 1 (Hl); destruct Hl] 
intros 1 (Hl); apply Pcons; apply IH; simplify in Hl; destruct Hl; assumption;
qed.

lemma eq_map : ∀A,B,f,g,l. (∀x.f x = g x) → map A B f l = map A B g l.
intros (A B f g l Efg); elim l; simplify; [1: reflexivity ];
rewrite > (Efg a); rewrite > H; reflexivity;  
qed.

lemma le_length_filter : \forall A,l,p.length A (filter A l p) \leq length A l.
intros;elim l
  [simplify;apply le_n
  |simplify;apply (bool_elim ? (p a));intro
     [simplify;apply le_S_S;assumption
     |simplify;apply le_S;assumption]]
qed.

lemma length_append : ∀A,l,m.length A (l@m) = length A l + length A m.
intros;elim l
[reflexivity
|simplify;rewrite < H;reflexivity]
qed.
