(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_______________________________________________________________ *)

include "basics/types.ma".
include "arithmetics/nat.ma".

inductive list (A:Type[0]) : Type[0] :=
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

definition not_nil: ∀A:Type[0].list A → Prop ≝
 λA.λl.match l with [ nil ⇒ True | cons hd tl ⇒ False ].

theorem nil_cons:
  ∀A:Type[0].∀l:list A.∀a:A. a::l ≠ [].
  #A #l #a @nmk #Heq (change with (not_nil ? (a::l))) >Heq //
qed.

(*
let rec id_list A (l: list A) on l :=
  match l with
  [ nil => []
  | (cons hd tl) => hd :: id_list A tl ]. *)

let rec append A (l1: list A) l2 on l1 ≝ 
  match l1 with
  [ nil ⇒  l2
  | cons hd tl ⇒  hd :: append A tl l2 ].

definition hd ≝ λA.λl: list A.λd:A.
  match l with [ nil ⇒ d | cons a _ ⇒ a].

definition tail ≝  λA.λl: list A.
  match l with [ nil ⇒  [] | cons hd tl ⇒  tl].

interpretation "append" 'append l1 l2 = (append ? l1 l2).

theorem append_nil: ∀A.∀l:list A.l @ [] = l.
#A #l (elim l) normalize // qed.

theorem associative_append: 
 ∀A.associative (list A) (append A).
#A #l1 #l2 #l3 (elim l1) normalize // qed.

(* deleterio per auto 
ntheorem cons_append_commute:
  ∀A:Type.∀l1,l2:list A.∀a:A.
    a :: (l1 @ l2) = (a :: l1) @ l2.
//; nqed. *)

theorem append_cons:∀A.∀a:A.∀l,l1.l@(a::l1)=(l@[a])@l1.
#A #a #l #l1 >associative_append // qed.

theorem nil_append_elim: ∀A.∀l1,l2: list A.∀P:?→?→Prop. 
  l1@l2=[] → P (nil A) (nil A) → P l1 l2.
#A #l1 #l2 #P (cases l1) normalize //
#a #l3 #heq destruct
qed.

theorem nil_to_nil:  ∀A.∀l1,l2:list A.
  l1@l2 = [] → l1 = [] ∧ l2 = [].
#A #l1 #l2 #isnil @(nil_append_elim A l1 l2) /2/
qed.

(* iterators *)

let rec map (A,B:Type[0]) (f: A → B) (l:list A) on l: list B ≝
 match l with [ nil ⇒ nil ? | cons x tl ⇒ f x :: (map A B f tl)].
  
let rec foldr (A,B:Type[0]) (f:A → B → B) (b:B) (l:list A) on l :B ≝  
 match l with [ nil ⇒ b | cons a l ⇒ f a (foldr A B f b l)].
 
definition filter ≝ 
  λT.λp:T → bool.
  foldr T (list T) (λx,l0.if_then_else ? (p x) (x::l0) l0) (nil T).

(* compose f [a1;...;an] [b1;...;bm] = 
  [f a1 b1; ... ;f an b1; ... ;f a1 bm; f an bm] *)
 
definition compose ≝ λA,B,C.λf:A→B→C.λl1,l2.
    foldr ?? (λi,acc.(map ?? (f i) l2)@acc) [ ] l1.

lemma filter_true : ∀A,l,a,p. p a = true → 
  filter A p (a::l) = a :: filter A p l.
#A #l #a #p #pa (elim l) normalize >pa normalize // qed.

lemma filter_false : ∀A,l,a,p. p a = false → 
  filter A p (a::l) = filter A p l.
#A #l #a #p #pa (elim l) normalize >pa normalize // qed.

theorem eq_map : ∀A,B,f,g,l. (∀x.f x = g x) → map A B f l = map A B g l.
#A #B #f #g #l #eqfg (elim l) normalize // qed.

let rec dprodl (A:Type[0]) (f:A→Type[0]) (l1:list A) (g:(∀a:A.list (f a))) on l1 ≝
match l1 with
  [ nil ⇒ nil ?
  | cons a tl ⇒ (map ??(dp ?? a) (g a)) @ dprodl A f tl g
  ].

(**************************** length ******************************)

let rec length (A:Type[0]) (l:list A) on l ≝ 
  match l with 
    [ nil ⇒ 0
    | cons a tl ⇒ S (length A tl)].

notation "|M|" non associative with precedence 60 for @{'norm $M}.
interpretation "norm" 'norm l = (length ? l).

lemma length_append: ∀A.∀l1,l2:list A. 
  |l1@l2| = |l1|+|l2|.
#A #l1 elim l1 // normalize /2/
qed.

(****************************** nth ********************************)
let rec nth n (A:Type[0]) (l:list A) (d:A)  ≝  
  match n with
    [O ⇒ hd A l d
    |S m ⇒ nth m A (tail A l) d].

lemma nth_nil: ∀A,a,i. nth i A ([]) a = a.
#A #a #i elim i normalize //
qed.

(**************************** fold *******************************)

let rec fold (A,B:Type[0]) (op:B → B → B) (b:B) (p:A→bool) (f:A→B) (l:list A) on l :B ≝  
 match l with 
  [ nil ⇒ b 
  | cons a l ⇒ if_then_else ? (p a) (op (f a) (fold A B op b p f l))
      (fold A B op b p f l)].
      
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

theorem fold_sum: ∀A,B. ∀I,J:list A.∀nil.∀op:Aop B nil.∀f.
  op (\fold[op,nil]_{i∈I} (f i)) (\fold[op,nil]_{i∈J} (f i)) =
    \fold[op,nil]_{i∈(I@J)} (f i).
#A #B #I #J #nil #op #f (elim I) normalize 
  [>nill //|#a #tl #Hind <assoc //]
qed.

(********************** lhd and ltl ******************************)

let rec lhd (A:Type[0]) (l:list A) n on n ≝ match n with
   [ O   ⇒ nil …
   | S n ⇒ match l with [ nil ⇒ nil … | cons a l ⇒ a :: lhd A l n ]
   ].

let rec ltl (A:Type[0]) (l:list A) n on n ≝ match n with
   [ O   ⇒ l
   | S n ⇒ ltl A (tail … l) n
   ].

lemma lhd_nil: ∀A,n. lhd A ([]) n = [].
#A #n elim n //
qed.

lemma ltl_nil: ∀A,n. ltl A ([]) n = [].
#A #n elim n normalize //
qed.

lemma lhd_cons_ltl: ∀A,n,l. lhd A l n @ ltl A l n = l.
#A #n elim n -n //
#n #IHn #l elim l normalize //
qed.

lemma length_ltl: ∀A,n,l. |ltl A l n| = |l| - n.
#A #n elim n -n /2/
#n #IHn *; normalize /2/
qed.
