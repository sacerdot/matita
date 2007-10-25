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

set "baseuri" "cic:/matita/Fsub/util".
include "logic/equality.ma".
include "nat/compare.ma".
include "list/list.ma".

(*** useful definitions and lemmas not really related to Fsub ***)

definition max \def 
\lambda m,n.
  match (leb m n) with
     [true \Rightarrow n
     |false \Rightarrow m]. 
     
lemma le_n_max_m_n: \forall m,n:nat. n \le max m n.
intros.
unfold max.
apply (leb_elim m n)
  [simplify.intros.apply le_n
  |simplify.intros.autobatch
  ]
qed.
  
lemma le_m_max_m_n: \forall m,n:nat. m \le max m n.
intros.
unfold max.
apply (leb_elim m n)
  [simplify.intro.assumption
  |simplify.intros.autobatch
  ]
qed.  

inductive in_list (A:Type): A → (list A) → Prop ≝
| in_Base : ∀ x,l.(in_list A x (x::l))
| in_Skip : ∀ x,y,l.(in_list A x l) → (in_list A x (y::l)).

notation > "hvbox(x ∈ l)"
  non associative with precedence 30 for @{ 'inlist $x $l }.
notation < "hvbox(x \nbsp ∈ \nbsp l)"
  non associative with precedence 30 for @{ 'inlist $x $l }.
interpretation "item in list" 'inlist x l =
  (cic:/matita/Fsub/util/in_list.ind#xpointer(1/1) _ x l).

definition incl : \forall A.(list A) \to (list A) \to Prop \def
  \lambda A,l,m.\forall x.(in_list A x l) \to (in_list A x m).               
              
(* FIXME: use the map in library/list (when there will be one) *)
definition map : \forall A,B,f.((list A) \to (list B)) \def
  \lambda A,B,f.let rec map (l : (list A)) : (list B) \def
    match l in list return \lambda l0:(list A).(list B) with
      [nil \Rightarrow (nil B)
      |(cons (a:A) (t:(list A))) \Rightarrow 
        (cons B (f a) (map t))] in map.

lemma in_list_nil : \forall A,x.\lnot (in_list A x []).
intros.unfold.intro.inversion H
  [intros;lapply (sym_eq ? ? ? H2);destruct Hletin
  |intros;destruct H4]
qed.

lemma in_cons_case : ∀A.∀x,h:A.∀t:list A.x ∈ h::t → x = h ∨ (x ∈ t).
intros;inversion H;intros
  [destruct H2;left;symmetry;assumption
  |destruct H4;right;applyS H1]
qed.

lemma append_nil:\forall A:Type.\forall l:list A. l@[]=l.
intros.
elim l;intros;autobatch.
qed.

lemma append_cons:\forall A.\forall a:A.\forall l,l1. 
l@(a::l1)=(l@[a])@l1.
intros.
rewrite > associative_append.
reflexivity.
qed.

lemma in_list_append1: \forall A.\forall x:A.
\forall l1,l2. x \in l1 \to x \in l1@l2.
intros.
elim H
  [simplify.apply in_Base
  |simplify.apply in_Skip.assumption
  ]
qed.

lemma in_list_append2: \forall A.\forall x:A.
\forall l1,l2. x \in l2 \to x \in l1@l2.
intros 3.
elim l1
  [simplify.assumption
  |simplify.apply in_Skip.apply H.assumption
  ]
qed.

theorem append_to_or_in_list: \forall A:Type.\forall x:A.
\forall l,l1. x \in l@l1 \to (x \in l) \lor (x \in l1).
intros 3.
elim l
  [right.apply H
  |simplify in H1.inversion H1;intros
    [destruct H3.left.rewrite < Hcut.
     apply in_Base
    |destruct H5.
     elim (H l2)
      [left.apply in_Skip.
       rewrite < H4.assumption
      |right.rewrite < H4.assumption
      |rewrite > Hcut1.rewrite > H4.assumption
      ]
    ]
  ]
qed.

lemma max_case : \forall m,n.(max m n) = match (leb m n) with
      [ true \Rightarrow n
      | false \Rightarrow m ].
intros;elim m;simplify;reflexivity;
qed.

lemma incl_A_A: ∀T,A.incl T A A.
intros.unfold incl.intros.assumption.
qed.