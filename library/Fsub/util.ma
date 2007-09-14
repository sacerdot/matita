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
| in_Skip : ∀ x,y,l.(in_list A x l) → (x ≠ y) → (in_list A x (y::l)).

notation > "hvbox(x ∈ l)"
  non associative with precedence 30 for @{ 'inlist $x $l }.
notation < "hvbox(x \nbsp ∈ \nbsp l)"
  non associative with precedence 30 for @{ 'inlist $x $l }.
interpretation "item in list" 'inlist x l =
  (cic:/matita/Fsub/util/in_list.ind#xpointer(1/1) _ x l).

lemma in_Skip2 : ∀x,y,l.(in_list nat x l) → (in_list nat x (y::l)).
intros;elim (decidable_eq_nat x y)
  [rewrite > H1;apply in_Base
  |apply (in_Skip ? ? ? ? H H1)]
qed.

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
  |intros;destruct H5]
qed.

lemma in_cons_case : ∀A.∀x,h:A.∀t:list A.x ∈ h::t → x = h ∨ (x ≠ h ∧ (x ∈ t)).
intros;inversion H;intros
  [destruct H2;left;symmetry;assumption
  |destruct H5;right;split [rewrite > Hcut|rewrite > Hcut1] assumption ]
qed.

lemma max_case : \forall m,n.(max m n) = match (leb m n) with
      [ false \Rightarrow n
      | true \Rightarrow m ].
intros;elim m;simplify;reflexivity;
qed.