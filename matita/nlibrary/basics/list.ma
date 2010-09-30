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

include "basics/eq.ma".
include "basics/bool.ma".

ninductive list (A:Type) : Type :=
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

ndefinition not_nil: ∀A:Type.list A → Prop ≝
 λA.λl.match l with [ nil ⇒ True | cons hd tl ⇒ False ].

ntheorem nil_cons:
  ∀A:Type.∀l:list A.∀a:A. a::l ≠ [].
  #A; #l; #a; napply nmk; #Heq; nchange with (not_nil ? (a::l));
  nrewrite > Heq; //;
nqed.

(*
let rec id_list A (l: list A) on l :=
  match l with
  [ nil => []
  | (cons hd tl) => hd :: id_list A tl ]. *)

nlet rec append A (l1: list A) l2 on l1 :=
  match l1 with
  [ nil ⇒  l2
  | cons hd tl ⇒  hd :: append A tl l2 ].

ndefinition hd ≝ λA:Type.λl: list A.λd:A.
  match l with 
  [ nil ⇒ d
  | cons a _ ⇒ a].

ndefinition tail ≝  λA:Type.λl: list A.
  match l with
  [ nil ⇒  []
  | cons hd tl ⇒  tl].

interpretation "append" 'append l1 l2 = (append ? l1 l2).

ntheorem append_nil: ∀A:Type.∀l:list A.l @ [] = l.
#A; #l; nelim l; nnormalize;//; nqed.

ntheorem associative_append: 
 ∀A:Type.associative (list A) (append A).
#A; #l1; #l2; #l3; nelim l1; nnormalize; //; nqed.

(* deleterio per auto 
ntheorem cons_append_commute:
  ∀A:Type.∀l1,l2:list A.∀a:A.
    a :: (l1 @ l2) = (a :: l1) @ l2.
//; nqed. *)

ntheorem append_cons:∀A.∀a:A.∀l,l1.l@(a::l1)=(l@[a])@l1.
#A; #a; #l; #l1; napply sym_eq.
napply associative_append.
(* /2/; *) nqed.

ntheorem nil_append_elim: ∀A.∀l1,l2: list A.∀P: list A → list A → Prop. 
  l1@l2 = [] → P (nil A) (nil A) → P l1 l2.
#A;#l1; #l2; #P; ncases l1; nnormalize;//;
#a; #l3; #heq; ndestruct;
nqed.

ntheorem nil_to_nil:  ∀A.∀l1,l2:list A.
  l1@l2 = [] → l1 = [] ∧ l2 = [].
#A; #l1; #l2; #isnil; napply (nil_append_elim A l1 l2);/2/;
nqed.

(* ierators *)

nlet rec map (A,B:Type) (f: A → B) (l:list A) on l: list B ≝
 match l with [ nil ⇒ nil ? | cons x tl ⇒ f x :: (map A B f tl)].
  
nlet rec foldr (A,B:Type) (f:A → B → B) (b:B) (l:list A) on l :B ≝  
 match l with [ nil ⇒ b | cons a l ⇒ f a (foldr A B f b l)].
   
ndefinition filter ≝ 
  λT:Type.λl:list T.λp:T → bool.
  foldr T (list T) (λx,l0.if_then_else ? (p x) (x::l0) l0).
  
ntheorem eq_map : ∀A,B,f,g,l. (∀x.f x = g x) → map A B f l = map A B g l.
#A; #B; #f; #g; #l; #eqfg; nelim l; nnormalize; //; nqed.

