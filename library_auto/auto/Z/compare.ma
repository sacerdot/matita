(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

set "baseuri" "cic:/matita/library_autobatch/Z/compare".

include "auto/Z/orders.ma".
include "auto/nat/compare.ma".

(* boolean equality *)
definition eqZb : Z \to Z \to bool \def
\lambda x,y:Z.
  match x with
  [ OZ \Rightarrow 
      match y with
        [ OZ \Rightarrow true
        | (pos q) \Rightarrow false
        | (neg q) \Rightarrow false]
  | (pos p) \Rightarrow 
      match y with
        [ OZ \Rightarrow false
        | (pos q) \Rightarrow eqb p q
        | (neg q) \Rightarrow false]     
  | (neg p) \Rightarrow 
      match y with
        [ OZ \Rightarrow false
        | (pos q) \Rightarrow false
        | (neg q) \Rightarrow eqb p q]].

theorem eqZb_to_Prop: 
\forall x,y:Z. 
match eqZb x y with
[ true \Rightarrow x=y
| false \Rightarrow x \neq y].
intros.
elim x
[ elim y
  [ simplify.
    reflexivity
  | simplify.
    apply not_eq_OZ_pos
  | simplify.
    apply not_eq_OZ_neg
  ]
| elim y
  [ simplify.
    unfold Not.
    intro.
    apply (not_eq_OZ_pos n).
    autobatch
    (*apply sym_eq.
    assumption*)
  | simplify.
    apply eqb_elim
    [ intro.    
      simplify.
      autobatch
      (*apply eq_f.
      assumption*)
    | intro.
      simplify.
      unfold Not.
      intro.
      autobatch
      (*apply H.
      apply inj_pos.
      assumption*)
    ]
  | simplify.
    apply not_eq_pos_neg
  ]
| elim y
  [ simplify.
    unfold Not.
    intro.
    apply (not_eq_OZ_neg n).
    autobatch
    (*apply sym_eq.
    assumption*)
  | simplify.
    unfold Not.
    intro.
    apply (not_eq_pos_neg n1 n).
    autobatch
    (*apply sym_eq.
    assumption*)
  | simplify.  
    apply eqb_elim
    [ intro.
      simplify.
      autobatch
      (*apply eq_f.
      assumption*)
    | intro.
      simplify.
      unfold Not.
      intro.
      autobatch
      (*apply H.
      apply inj_neg.
      assumption*)
    ]
  ]
]
qed.

theorem eqZb_elim: \forall x,y:Z.\forall P:bool \to Prop.
(x=y \to (P true)) \to (x \neq y \to (P false)) \to P (eqZb x y).
intros.
cut 
(match (eqZb x y) with
[ true \Rightarrow x=y
| false \Rightarrow x \neq y] \to P (eqZb x y))
[ apply Hcut.
  (*NB qui autobatch non chiude il goal*)
  apply eqZb_to_Prop
| elim (eqZb)
  [ (*NB qui autobatch non chiude il goal*)
    apply (H H2)
  | (*NB qui autobatch non chiude il goal*)
    apply (H1 H2)
  ]
]
qed.

definition Z_compare : Z \to Z \to compare \def
\lambda x,y:Z.
  match x with
  [ OZ \Rightarrow 
    match y with 
    [ OZ \Rightarrow EQ
    | (pos m) \Rightarrow LT
    | (neg m) \Rightarrow GT ]
  | (pos n) \Rightarrow 
    match y with 
    [ OZ \Rightarrow GT
    | (pos m) \Rightarrow (nat_compare n m)
    | (neg m) \Rightarrow GT]
  | (neg n) \Rightarrow 
    match y with 
    [ OZ \Rightarrow LT
    | (pos m) \Rightarrow LT
    | (neg m) \Rightarrow nat_compare m n ]].

theorem Z_compare_to_Prop : 
\forall x,y:Z. match (Z_compare x y) with
[ LT \Rightarrow x < y
| EQ \Rightarrow x=y
| GT \Rightarrow y < x]. 
intros.
elim x 
[ elim y
  [ simplify.
    apply refl_eq
  | simplify.
    exact I
  | simplify.
    exact I
  ]
| elim y
  [ simplify.
    exact I
  | simplify.
    cut (match (nat_compare n n1) with
    [ LT \Rightarrow n<n1
    | EQ \Rightarrow n=n1
    | GT \Rightarrow n1<n] \to 
    match (nat_compare n n1) with
    [ LT \Rightarrow (S n) \leq n1
    | EQ \Rightarrow pos n = pos n1
    | GT \Rightarrow (S n1) \leq n]) 
    [ apply Hcut.
      (*NB qui autobatch non chiude il goal*)
      apply nat_compare_to_Prop 
    | elim (nat_compare n n1)
      [ simplify.
        (*NB qui autobatch non chiude il goal*)
        exact H
      | simplify.
        apply eq_f.
        (*NB qui autobatch non chiude il goal*)
        exact H
      | simplify.
        (*NB qui autobatch non chiude il goal*)
        exact H
      ]
    ]
  | simplify.
    exact I    
  ]
| elim y
  [ simplify.
    exact I
  | simplify.
    exact I
  | simplify.
    cut (match (nat_compare n1 n) with
    [ LT \Rightarrow n1<n
    | EQ \Rightarrow n1=n
    | GT \Rightarrow n<n1] \to 
    match (nat_compare n1 n) with
    [ LT \Rightarrow (S n1) \leq n
    | EQ \Rightarrow neg n = neg n1
    | GT \Rightarrow (S n) \leq n1])
    [ apply Hcut.
      (*NB qui autobatch non chiude il goal*) 
      apply nat_compare_to_Prop
    | elim (nat_compare n1 n)
      [ simplify.
        (*NB qui autobatch non chiude il goal*)
        exact H
      | simplify.
        apply eq_f.
        apply sym_eq.
        (*NB qui autobatch non chiude il goal*)
        exact H
      | simplify.
        (*NB qui autobatch non chiude il goal*)
        exact H
      ]
    ]
  ]
]
qed.
