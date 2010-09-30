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

include "Z/z.ma".
include "nat/orders.ma".

definition Zle : Z \to Z \to Prop \def
\lambda x,y:Z.
  match x with
  [ OZ \Rightarrow 
    match y with 
    [ OZ \Rightarrow True
    | (pos m) \Rightarrow True
    | (neg m) \Rightarrow False ]
  | (pos n) \Rightarrow 
    match y with 
    [ OZ \Rightarrow False
    | (pos m) \Rightarrow n \leq m
    | (neg m) \Rightarrow False ]
  | (neg n) \Rightarrow 
    match y with 
    [ OZ \Rightarrow True
    | (pos m) \Rightarrow True
    | (neg m) \Rightarrow m \leq n ]].

interpretation "integer 'less or equal to'" 'leq x y = (Zle x y).
interpretation "integer 'neither less nor equal to'" 'nleq x y = (Not (Zle x y)).

definition Zlt : Z \to Z \to Prop \def
\lambda x,y:Z.
  match x with
  [ OZ \Rightarrow 
    match y with 
    [ OZ \Rightarrow False
    | (pos m) \Rightarrow True
    | (neg m) \Rightarrow False ]
  | (pos n) \Rightarrow 
    match y with 
    [ OZ \Rightarrow False
    | (pos m) \Rightarrow n<m
    | (neg m) \Rightarrow False ]
  | (neg n) \Rightarrow 
    match y with 
    [ OZ \Rightarrow True
    | (pos m) \Rightarrow True
    | (neg m) \Rightarrow m<n ]].
    
interpretation "integer 'less than'" 'lt x y = (Zlt x y).
interpretation "integer 'not less than'" 'nless x y = (Not (Zlt x y)).

theorem irreflexive_Zlt: irreflexive Z Zlt.
unfold irreflexive.unfold Not.
intro.elim x.exact H.
cut (neg n < neg n \to False).
apply Hcut.apply H.simplify.unfold lt.apply not_le_Sn_n.
cut (pos n < pos n \to False).
apply Hcut.apply H.simplify.unfold lt.apply not_le_Sn_n.
qed.

(* transitivity *)
theorem transitive_Zle : transitive Z Zle.
unfold transitive.
intros 3.
elim x 0
[ (* x = OZ *)
  elim y 0
  [ intros. assumption 
  | intro.
    elim z
    [ simplify. apply I 
    | simplify. apply I
    | simplify. simplify in H1. assumption
    ]
  | intro.
    elim z
    [ simplify. apply I
    | simplify. apply I
    | simplify. simplify in H. assumption
    ]
  ]
| (* x = (pos n) *)
  intro.
  elim y 0
  [ intros. apply False_ind. apply H
  | intros 2. 
    elim z 0
    [ simplify. intro. assumption
    | intro. generalize in match H. simplify. apply trans_le 
    | intro. simplify. intro. assumption
    ]
  | intros 2. apply False_ind. apply H
  ]
| (* x = (neg n) *)
  intro.
  elim y 0
  [ elim z 0
    [ simplify. intros. assumption
    | intro. simplify. intros. assumption
    | intro. simplify. intros. apply False_ind. apply H1
    ]
  | intros 2.
    elim z
    [ apply False_ind. apply H1 
    | simplify. apply I
    | apply False_ind. apply H1
    ]
  | intros 2.
    elim z 0
    [ simplify. intro. assumption
    | intro. simplify. intro. assumption
    | intros. simplify. simplify in H. simplify in H1. 
      generalize in match H. generalize in match H1. apply trans_le
    ]
  ]
]
qed.

variant trans_Zle: transitive Z Zle
\def transitive_Zle.

theorem transitive_Zlt: transitive Z Zlt.
unfold.
intros 3.
elim x 0
[ (* x = OZ *)
  elim y 0
  [ intros. apply False_ind. apply H 
  | intro.
    elim z
    [ simplify. apply H1 
    | simplify. apply I
    | simplify. apply H1
    ]
  | intros 2. apply False_ind. apply H
  ]
| (* x = (pos n) *)
  intro.
  elim y 0
  [ intros. apply False_ind. apply H
  | intros 2. 
    elim z 0
    [ simplify. intro. assumption
    | intro. generalize in match H. simplify. apply trans_lt 
    | intro. simplify. intro. assumption
    ]
  | intros 2. apply False_ind. apply H
  ]
| (* x = (neg n) *)
  intro.
  elim y 0
  [ elim z 0
    [ intros. simplify. apply I
    | intro. simplify. intros. assumption
    | intro. simplify. intros. apply False_ind. apply H1
    ]
  | intros 2.
    elim z
    [ apply False_ind. apply H1 
    | simplify. apply I
    | apply False_ind. apply H1
    ]
  | intros 2.
    elim z 0
    [ simplify. intro. assumption
    | intro. simplify. intro. assumption
    | intros. simplify. simplify in H. simplify in H1. 
      generalize in match H. generalize in match H1. apply trans_lt
    ]
  ]
]
qed.

variant trans_Zlt: transitive Z Zlt
\def transitive_Zlt.
theorem irrefl_Zlt: irreflexive Z Zlt
\def irreflexive_Zlt.

theorem Zlt_neg_neg_to_lt: 
\forall n,m:nat. neg n < neg m \to m < n.
intros.apply H.
qed.

theorem lt_to_Zlt_neg_neg: \forall n,m:nat.m < n \to neg n < neg m. 
intros.
simplify.apply H.
qed.

theorem Zlt_pos_pos_to_lt: 
\forall n,m:nat. pos n < pos m \to n < m.
intros.apply H.
qed.

theorem lt_to_Zlt_pos_pos: \forall n,m:nat.n < m \to pos n < pos m. 
intros.
simplify.apply H.
qed.

theorem Zlt_to_Zle: \forall x,y:Z. x < y \to Zsucc x \leq y.
intros 2.
elim x.
(* goal: x=OZ *)
  cut (OZ < y \to Zsucc OZ \leq y).
    apply Hcut. assumption.
    simplify.elim y. 
      simplify.exact H1.
      simplify.apply le_O_n.
      simplify.exact H1.
(* goal: x=pos *)      
  exact H.
(* goal: x=neg *)      
  cut (neg n < y \to Zsucc (neg n) \leq y).
    apply Hcut. assumption.
    elim n.
      cut (neg O < y \to Zsucc (neg O) \leq y).
        apply Hcut. assumption.
        simplify.elim y.
          simplify.exact I.
          simplify.exact I.
          simplify.apply (not_le_Sn_O n1 H2).
      cut (neg (S n1) < y \to (Zsucc (neg (S n1))) \leq y).
        apply Hcut. assumption.simplify.
        elim y.
          simplify.exact I.
          simplify.exact I.
          simplify.apply (le_S_S_to_le n2 n1 H3).
qed.
