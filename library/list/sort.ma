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

set "baseuri" "cic:/matita/list/sort/".

include "datatypes/bool.ma".
include "datatypes/constructors.ma".
include "list/list.ma".

let rec mem (A:Type) (eq: A → A → bool) x (l: list A) on l ≝
 match l with
  [ nil ⇒ false
  | (cons a l') ⇒
    match eq x a with
     [ true ⇒ true
     | false ⇒ mem A eq x l'
     ]
  ].
  
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
    generalize in match H1;
    clear H1;
    elim l1;
    [ simplify; reflexivity;
    | cut ((le t t1 \land ordered A le (t1::l2)) = true);
      [ generalize in match Hcut; 
        apply andb_elim;
        elim (le t t1);
        [ simplify;
          fold simplify (ordered ? le (t1::l2));
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
      generalize in match H4; clear H4;
      elim l'; simplify;
      [ rewrite > H5;
        reflexivity
      | elim (le x t); simplify;
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
  | apply (insert_sorted ? ? le_tot (insertionsort ? le l1) t);
    assumption;
  ]
qed.