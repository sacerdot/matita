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

set "baseuri" "cic:/matita/library_autobatch/Z/orders".

include "auto/Z/z.ma".
include "auto/nat/orders.ma".

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
unfold irreflexive.
unfold Not.
intro.
elim x
[ (*qui autobatch non chiude il goal*)
  exact H
| cut (neg n < neg n \to False)
  [ apply Hcut.
    (*qui autobatch non chiude il goal*)
    apply H
  | autobatch
    (*simplify.
    unfold lt.
    apply not_le_Sn_n*)
  ]
| cut (pos n < pos n \to False)
  [ apply Hcut.
    (*qui autobatch non chiude il goal*)
    apply H
  | autobatch
    (*simplify.
    unfold lt.
    apply not_le_Sn_n*)
  ]
]
qed.

theorem irrefl_Zlt: irreflexive Z Zlt
\def irreflexive_Zlt.

theorem Zlt_neg_neg_to_lt: 
\forall n,m:nat. neg n < neg m \to m < n.
intros.
(*qui autobatch non chiude il goal*)
apply H.
qed.

theorem lt_to_Zlt_neg_neg: \forall n,m:nat.m < n \to neg n < neg m. 
intros.
simplify.
apply H.
qed.

theorem Zlt_pos_pos_to_lt: 
\forall n,m:nat. pos n < pos m \to n < m.
intros.
(*qui autobatch non chiude il goal*)
apply H.
qed.

theorem lt_to_Zlt_pos_pos: \forall n,m:nat.n < m \to pos n < pos m. 
intros.
simplify.
apply H.
qed.

theorem Zlt_to_Zle: \forall x,y:Z. x < y \to Zsucc x \leq y.
intros 2.
elim x
[ (* goal: x=OZ *)
  cut (OZ < y \to Zsucc OZ \leq y)
  [ autobatch
    (*apply Hcut. 
    assumption*)
  | simplify.
    elim y 
    [ simplify.
      (*qui autobatch non chiude il goal*)
      exact H1
    | simplify.
      apply le_O_n
    | simplify.
      (*qui autobatch non chiude il goal*)    
      exact H1
    ]
  ]
| (* goal: x=pos *)      
  exact H
| (* goal: x=neg *)      
  cut (neg n < y \to Zsucc (neg n) \leq y)
  [ autobatch
    (*apply Hcut. 
    assumption*)
  | elim n
    [ cut (neg O < y \to Zsucc (neg O) \leq y)
      [ autobatch
        (*apply Hcut. 
        assumption*)
      | simplify.
        elim y
        [ simplify.
          exact I
        | simplify.
          exact I
        | simplify.
          (*qui autobatch non chiude il goal*)
          apply (not_le_Sn_O n1 H2)
        ]
      ]
    | cut (neg (S n1) < y \to (Zsucc (neg (S n1))) \leq y)
      [ autobatch
        (*apply Hcut. 
        assumption*)
      | simplify.
        elim y
        [ simplify.
          exact I
        | simplify.
          exact I
        | simplify.
          (*qui autobatch non chiude il goal*)
          apply (le_S_S_to_le n2 n1 H3)
        ]
      ] 
    ]
  ]
]
qed.
