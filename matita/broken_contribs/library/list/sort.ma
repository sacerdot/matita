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
include "list/in.ma".

inductive sorted (A:Type) (P:A \to A \to Prop): list A \to Prop \def
| sort_nil : sorted A P []
| sort_cons : \forall x,l.sorted A P l \to (\forall y.in_list ? y l \to P x y)
              \to sorted A P (x::l).
              
lemma sorted_cons_to_sorted : \forall A,P,x,l.sorted A P (x::l) \to sorted A P l.
intros;inversion H;intros
  [destruct H1
  |destruct H4;assumption]
qed.

lemma sorted_to_minimum : \forall A,P,x,l.sorted A P (x::l) \to 
                          \forall y.in_list ? y l \to P x y.
intros;inversion H;intros;
  [destruct H2
  |destruct H5;apply H4;assumption]
qed.


let rec ordered (A:Type) (le: A → A → bool) (l: list A) on l ≝
 match l with
  [ nil ⇒ true
  | (cons x l') ⇒
     match l' with
      [ nil ⇒ true
      | (cons y l'') ⇒
          le x y \land ordered A le l'
      ]
  ].
  
lemma sorted_to_eq_sorted_b_true :
      \forall A,ord,ordb.
      (\forall x,y.ord x y \to ordb x y = true) \to 
      \forall l.sorted A ord l \to ordered A ordb l = true.
intros 5;elim l
  [reflexivity
  |simplify;rewrite > H1;generalize in match H2;cases l1;intros
     [reflexivity
     |simplify;rewrite > H
        [reflexivity
        |apply (sorted_to_minimum ? ? ? ? H3);apply in_list_head]
     |apply sort_nil
     |apply (sorted_cons_to_sorted ? ? ? ? H3)]]
qed.

(* 
   TODO
   per far funzionare questa dimostrazione bisogna appoggiarsi a un
   eqb (e utilizzare quindi in_list <-> mem), oppure modificare la definizione 
   di sorted in modo che non si appoggi più a in_list:
   sorted []
   sorted [x] per ogni x
   sorted x::y::l se ord x y e sorted y::l

lemma eq_sorted_b_true_to_sorted :
      \forall A,ord,ordb.
      (\forall x,y.ordb x y = true \to ord x y) \to
      \forall l.ordered A ordb l = true \to sorted A ord l.
intros 5;elim l
  [apply sort_nil
  |apply sort_cons
     [apply H1;simplify in H2;generalize in match H2;cases l1;intros
        [reflexivity
        |simplify in H3;simplify;apply (andb_true_true_r ? ? H3)]
     |intros;apply H;generalize in match H2;
      generalize in match (in_list_to_mem_true ? ? ? ? H
        [
*)

let rec insert (A:Type) (le: A → A → bool) x (l: list A) on l ≝
 match l with
  [ nil ⇒ [x]
  | (cons he l') ⇒
      match le x he with
       [ true ⇒ x::l
       | false ⇒ he::(insert A le x l')
       ]
  ].

lemma insert_ind :
 ∀A:Type. ∀le: A → A → bool. ∀x.
  ∀P:(list A → list A → Prop).
   ∀H:(∀l: list A. l=[] → P [] [x]).
    ∀H2:
    (∀l: list A. ∀he. ∀l'. P l' (insert ? le x l') →
      le x he = false → l=he::l' → P (he::l') (he::(insert ? le x l'))).
     ∀H3:
     (∀l: list A. ∀he. ∀l'. P l' (insert ? le x l') →
       le x he = true → l=he::l' → P (he::l') (x::he::l')).
    ∀l:list A. P l (insert ? le x l).
  intros.
  apply (
    let rec insert_ind (l: list A) \def
    match l in list
    return
      λli.
       l = li → P li (insert ? le x li)
    with
     [ nil ⇒ H l
     | (cons he l') ⇒
         match le x he
         return
          λb. le x he = b → l = he::l' →
           P (he::l')
            (match b with 
              [ true ⇒ x::he::l'
              | false ⇒ he::(insert ? le x l') ])
         with
          [ true ⇒ H2 l he l' (insert_ind l')
          | false ⇒ H1 l he l' (insert_ind l')
          ]
         (refl_eq ? (le x he))
     ] (refl_eq ? l) in insert_ind l).
qed.


let rec insertionsort (A:Type) (le: A → A → bool) (l: list A) on l ≝
 match l with
  [ nil ⇒ []
  | (cons he l') ⇒
      let l'' ≝ insertionsort A le l' in
       insert A le he l''
  ].

lemma ordered_injective:
  ∀A:Type. ∀le:A → A → bool.
   ∀l:list A. ordered A le l = true → ordered A le (tail A l) = true.
  intros 3 (A le l).
  elim l
  [ simplify; reflexivity;
  | simplify;
    elim l1 in H1 ⊢ %;
    [ simplify; reflexivity;
    | cut ((le a a1 \land ordered A le (a1::l2)) = true);
      [ generalize in match Hcut; 
        apply andb_elim;
        elim (le a a1);
        [ simplify;
          fold simplify (ordered ? le (a1::l2));
          intros; assumption;
        | simplify;
          intros (Habsurd);
          apply False_ind;
          apply (not_eq_true_false);
          symmetry;
          assumption
        ]
      | exact H2;
      ]
    ]
  ].
qed.

lemma insert_sorted:
  \forall A:Type. \forall le:A\to A\to bool.
  (\forall a,b:A. le a b = false \to le b a = true) \to
  \forall l:list A. \forall x:A.
    ordered A le l = true \to ordered A le (insert A le x l) = true.
 intros 5 (A le H l x).
 apply (insert_ind ? ? ? (λl,il. ordered ? le l = true → ordered ? le il = true));
 clear l; intros; simplify; intros;
  [2: rewrite > H1;
    [ generalize in match (H ? ? H2); clear H2; intro;
      elim l' in H4 ⊢ %; simplify;
      [ rewrite > H5;
        reflexivity
      | elim (le x a); simplify;
        [ rewrite > H5;
          reflexivity
        | simplify in H4;
          rewrite > (andb_true_true ? ? H4);
          reflexivity
        ]
      ]
    | apply (ordered_injective ? ? ? H4)
    ]
  | reflexivity
  | rewrite > H2;
    rewrite > H4;
    reflexivity
  ].
qed.
  
theorem insertionsort_sorted:
  ∀A:Type.
  ∀le:A → A → bool.∀eq:A → A → bool.
  (∀a,b:A. le a b = false → le b a = true) \to
  ∀l:list A.
  ordered A le (insertionsort A le l) = true.
  intros 5 (A le eq le_tot l).
  elim l;
  [ simplify;
    reflexivity;
  | apply (insert_sorted ? ? le_tot (insertionsort ? le l1) a);
    assumption;
  ]
qed.