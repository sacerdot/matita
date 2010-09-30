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

include "datatypes/bool.ma".
include "datatypes/constructors.ma".
include "list/list.ma".

inductive in_list (A:Type): A → (list A) → Prop ≝
| in_list_head : ∀ x,l.(in_list A x (x::l))
| in_list_cons : ∀ x,y,l.(in_list A x l) → (in_list A x (y::l)).

definition incl : \forall A.(list A) \to (list A) \to Prop \def
  \lambda A,l,m.\forall x.in_list A x l \to in_list A x m.
  
notation "hvbox(a break ∉ b)" non associative with precedence 45
for @{ 'notmem $a $b }. 
  
interpretation "list member" 'mem x l = (in_list ? x l).
interpretation "list not member" 'notmem x l = (Not (in_list ? x l)).
interpretation "list inclusion" 'subseteq l1 l2 = (incl ? l1 l2).
  
lemma not_in_list_nil : \forall A,x.\lnot in_list A x [].
intros.unfold.intro.inversion H
  [intros;lapply (sym_eq ? ? ? H2);destruct Hletin
  |intros;destruct H4]
qed.

lemma in_list_cons_case : \forall A,x,a,l.in_list A x (a::l) \to
                          x = a \lor in_list A x l.
intros;inversion H;intros
  [destruct H2;left;reflexivity
  |destruct H4;right;assumption]
qed.

lemma in_list_tail : \forall l,x,y.
      in_list nat x (y::l) \to x \neq y \to in_list nat x l.
intros 4;elim (in_list_cons_case ? ? ? ? H)
  [elim (H2 H1)
  |assumption]
qed.

lemma in_list_singleton_to_eq : \forall A,x,y.in_list A x [y] \to x = y.
intros;elim (in_list_cons_case ? ? ? ? H)
  [assumption
  |elim (not_in_list_nil ? ? H1)]
qed.

lemma in_list_to_in_list_append_l: \forall A.\forall x:A.
\forall l1,l2.in_list ? x l1 \to in_list ? x (l1@l2).
intros.
elim H;simplify
  [apply in_list_head
  |apply in_list_cons;assumption
  ]
qed.

lemma in_list_to_in_list_append_r: \forall A.\forall x:A.
\forall l1,l2. in_list ? x l2 \to in_list ? x (l1@l2).
intros 3.
elim l1;simplify
  [assumption
  |apply in_list_cons;apply H;assumption
  ]
qed.

theorem in_list_append_to_or_in_list: \forall A:Type.\forall x:A.
\forall l,l1. in_list ? x (l@l1) \to in_list ? x l \lor in_list ? x l1.
intros 3.
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
qed.

let rec mem (A:Type) (eq: A → A → bool) x (l: list A) on l ≝
 match l with
  [ nil ⇒ false
  | (cons a l') ⇒
    match eq x a with
     [ true ⇒ true
     | false ⇒ mem A eq x l'
     ]
  ].
  
lemma mem_true_to_in_list :
  \forall A,equ.
  (\forall x,y.equ x y = true \to x = y) \to
  \forall x,l.mem A equ x l = true \to in_list A x l.
intros 5.elim l
  [simplify in H1;destruct H1
  |simplify in H2;apply (bool_elim ? (equ x a))
     [intro;rewrite > (H ? ? H3);apply in_list_head
     |intro;rewrite > H3 in H2;simplify in H2;
      apply in_list_cons;apply H1;assumption]]
qed.

lemma in_list_to_mem_true :
  \forall A,equ.
  (\forall x.equ x x = true) \to
  \forall x,l.in_list A x l \to mem A equ x l = true.
intros 5.elim l
  [elim (not_in_list_nil ? ? H1)
  |elim H2
    [simplify;rewrite > H;reflexivity
    |simplify;rewrite > H4;apply (bool_elim ? (equ a1 a2));intro;reflexivity]].
qed.

lemma in_list_filter_to_p_true : \forall l,x,p.
in_list nat x (filter nat l p) \to p x = true.
intros 3;elim l
  [simplify in H;elim (not_in_list_nil ? ? H)
  |simplify in H1;apply (bool_elim ? (p a));intro;rewrite > H2 in H1;
   simplify in H1
     [elim (in_list_cons_case ? ? ? ? H1)
        [rewrite > H3;assumption
        |apply (H H3)]
     |apply (H H1)]]
qed.

lemma in_list_filter : \forall l,p,x.in_list nat x (filter nat l p) \to in_list nat x l.
intros 3;elim l
  [simplify in H;elim (not_in_list_nil ? ? H)
  |simplify in H1;apply (bool_elim ? (p a));intro;rewrite > H2 in H1;
   simplify in H1
     [elim (in_list_cons_case ? ? ? ? H1)
        [rewrite > H3;apply in_list_head
        |apply in_list_cons;apply H;assumption]
     |apply in_list_cons;apply H;assumption]]
qed.

lemma in_list_filter_r : \forall l,p,x.
              in_list nat x l \to p x = true \to in_list nat x (filter nat l p).
intros 3;elim l
  [elim (not_in_list_nil ? ? H)
  |elim (in_list_cons_case ? ? ? ? H1)
     [rewrite < H3;simplify;rewrite > H2;simplify;apply in_list_head
     |simplify;apply (bool_elim ? (p a));intro;simplify;
        [apply in_list_cons;apply H;assumption
        |apply H;assumption]]]
qed.

lemma incl_A_A: ∀T,A.incl T A A.
intros.unfold incl.intros.assumption.
qed.

lemma incl_append_l : ∀T,A,B.incl T A (A @ B).
unfold incl; intros;autobatch.
qed.

lemma incl_append_r : ∀T,A,B.incl T B (A @ B).
unfold incl; intros;autobatch.
qed.

lemma incl_cons : ∀T,A,B,x.incl T A B → incl T (x::A) (x::B).
unfold incl; intros;elim (in_list_cons_case ? ? ? ? H1);autobatch.
qed.

