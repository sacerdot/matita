(**************************************************************************)
(*       ___	                                                          *)
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

set "baseuri" "cic:/matita/library_autobatch/nat/compare".

include "datatypes/bool.ma".
include "datatypes/compare.ma".
include "auto/nat/orders.ma".

let rec eqb n m \def 
match n with 
  [ O \Rightarrow 
     match m with 
     [ O \Rightarrow true
	   | (S q) \Rightarrow false] 
  | (S p) \Rightarrow
	   match m with 
     [ O \Rightarrow false
	   | (S q) \Rightarrow eqb p q]].
	   
theorem eqb_to_Prop: \forall n,m:nat. 
match (eqb n m) with
[ true  \Rightarrow n = m 
| false \Rightarrow n \neq m].
intros.
apply (nat_elim2
(\lambda n,m:nat.match (eqb n m) with
[ true  \Rightarrow n = m 
| false \Rightarrow n \neq m]))
[ intro.
  elim n1;simplify;autobatch
  (*[ simplify
    reflexivity
  | simplify.
    apply not_eq_O_S
  ]*)
| intro.
  simplify.
  unfold Not.
  intro.
  apply (not_eq_O_S n1).
  autobatch
  (*apply sym_eq.
  assumption*)
| intros.
  simplify.
  generalize in match H.
  elim ((eqb n1 m1));simplify
  [ apply eq_f.    
    apply H1
  | unfold Not.
    intro.
    apply H1.
    autobatch
    (*apply inj_S.
    assumption*)
  ]
]
qed.

theorem eqb_elim : \forall n,m:nat.\forall P:bool \to Prop.
(n=m \to (P true)) \to (n \neq m \to (P false)) \to (P (eqb n m)). 
intros.
cut 
(match (eqb n m) with
[ true  \Rightarrow n = m
| false \Rightarrow n \neq m] \to (P (eqb n m)))
[ apply Hcut.
  (* qui autobatch non conclude il goal*)
  apply eqb_to_Prop
| elim (eqb n m)
  [ (*qui autobatch non conclude il goal*)
    apply ((H H2))
  | (*qui autobatch non conclude il goal*)
    apply ((H1 H2))
  ]
]
qed.

theorem eqb_n_n: \forall n. eqb n n = true.
intro.
elim n;simplify;autobatch.
(*[ simplify.reflexivity
| simplify.assumption.
]*)
qed.

theorem eqb_true_to_eq: \forall n,m:nat.
eqb n m = true \to n = m.
intros.
change with 
match true with
[ true  \Rightarrow n = m 
| false \Rightarrow n \neq m].
rewrite < H.
(*qui autobatch non conclude il goal*)
apply eqb_to_Prop. 
qed.

theorem eqb_false_to_not_eq: \forall n,m:nat.
eqb n m = false \to n \neq m.
intros.
change with 
match false with
[ true  \Rightarrow n = m 
| false \Rightarrow n \neq m].
rewrite < H.
(*qui autobatch non conclude il goal*)
apply eqb_to_Prop. 
qed.

theorem eq_to_eqb_true: \forall n,m:nat.
n = m \to eqb n m = true.
intros.
autobatch.
(*apply (eqb_elim n m)
[ intros. reflexivity
| intros.apply False_ind.apply (H1 H)
]*)
qed.

theorem not_eq_to_eqb_false: \forall n,m:nat.
\lnot (n = m) \to eqb n m = false.
intros.apply (eqb_elim n m);intros
[ apply False_ind.
  apply (H H1)
| reflexivity
]
qed.

let rec leb n m \def 
match n with 
    [ O \Rightarrow true
    | (S p) \Rightarrow
	match m with 
        [ O \Rightarrow false
	| (S q) \Rightarrow leb p q]].
	
theorem leb_to_Prop: \forall n,m:nat. 
match (leb n m) with
[ true  \Rightarrow n \leq m 
| false \Rightarrow n \nleq m].
intros.
apply (nat_elim2
(\lambda n,m:nat.match (leb n m) with
[ true  \Rightarrow n \leq m 
| false \Rightarrow n \nleq m]))
[ simplify.
  exact le_O_n
| simplify.
  exact not_le_Sn_O
| intros 2.
  simplify.
  elim ((leb n1 m1));simplify
  [ apply le_S_S.
     (*qui autobatch non conclude il goal*)
    apply H
  | unfold Not.
    intros.
    apply H.
    autobatch
    (*apply le_S_S_to_le.
    assumption*)
  ]
]
qed.

theorem leb_elim: \forall n,m:nat. \forall P:bool \to Prop. 
(n \leq m \to (P true)) \to (n \nleq m \to (P false)) \to
P (leb n m).
intros.
cut 
(match (leb n m) with
[ true  \Rightarrow n \leq m
| false \Rightarrow n \nleq m] \to (P (leb n m)))
[ apply Hcut.
  (*qui autobatch non conclude il goal*)
  apply leb_to_Prop
| elim (leb n m)
  [ (*qui autobatch non conclude il goal*)
    apply ((H H2))
  | (*qui autobatch non conclude il goal*)
    apply ((H1 H2))
  ]
]
qed.

let rec nat_compare n m: compare \def
match n with
[ O \Rightarrow 
    match m with 
      [ O \Rightarrow EQ
      | (S q) \Rightarrow LT ]
| (S p) \Rightarrow 
    match m with 
      [ O \Rightarrow GT
      | (S q) \Rightarrow nat_compare p q]].
(**********)
theorem nat_compare_n_n: \forall n:nat. nat_compare n n = EQ.
intro.elim n
[ autobatch
  (*simplify.
  reflexivity*)
| simplify.
  assumption
]
qed.

theorem nat_compare_S_S: \forall n,m:nat. 
nat_compare n m = nat_compare (S n) (S m).
intros.autobatch.
(*simplify.reflexivity.*)
qed.

theorem S_pred: \forall n:nat.lt O n \to eq nat n (S (pred n)).
intro.
elim n;autobatch.
(*[ apply False_ind.
  exact (not_le_Sn_O O H)
| apply eq_f.
  apply pred_Sn
]*)
qed.

theorem nat_compare_pred_pred: 
\forall n,m:nat.lt O n \to lt O m \to 
eq compare (nat_compare n m) (nat_compare (pred n) (pred m)).
intros.
apply (lt_O_n_elim n H).
apply (lt_O_n_elim m H1).
intros.
autobatch.
(*simplify.reflexivity.*)
qed.

theorem nat_compare_to_Prop: \forall n,m:nat. 
match (nat_compare n m) with
  [ LT \Rightarrow n < m
  | EQ \Rightarrow n=m
  | GT \Rightarrow m < n ].
intros.
apply (nat_elim2 (\lambda n,m.match (nat_compare n m) with
  [ LT \Rightarrow n < m
  | EQ \Rightarrow n=m
  | GT \Rightarrow m < n ]))
[ intro.
  elim n1;simplify;autobatch
  (*[ reflexivity
  | unfold lt.
    apply le_S_S.
    apply le_O_n
  ]*)
| intro.
  simplify.
  autobatch
  (*unfold lt.
  apply le_S_S. 
  apply le_O_n*)
| intros 2.
  simplify.
  elim ((nat_compare n1 m1));simplify
  [ unfold lt.
    apply le_S_S.
    (*qui autobatch non chiude il goal*)
    apply H
  | apply eq_f.
    (*qui autobatch non chiude il goal*)
    apply H
  | unfold lt.
    apply le_S_S.
    (*qui autobatch non chiude il goal*)
    apply H
  ]
]
qed.

theorem nat_compare_n_m_m_n: \forall n,m:nat. 
nat_compare n m = compare_invert (nat_compare m n).
intros. 
apply (nat_elim2 (\lambda n,m. nat_compare n m = compare_invert (nat_compare m n)));intros
[ elim n1;autobatch(*;simplify;reflexivity*)
| elim n1;autobatch(*;simplify;reflexivity*)  
| autobatch
  (*simplify.elim H.reflexivity*)
]
qed.
     
theorem nat_compare_elim : \forall n,m:nat. \forall P:compare \to Prop.
(n < m \to P LT) \to (n=m \to P EQ) \to (m < n \to P GT) \to 
(P (nat_compare n m)).
intros.
cut (match (nat_compare n m) with
[ LT \Rightarrow n < m
| EQ \Rightarrow n=m
| GT \Rightarrow m < n] \to
(P (nat_compare n m)))
[ apply Hcut.
  (*autobatch non chiude il goal*)
  apply nat_compare_to_Prop
| elim ((nat_compare n m))
  [ (*autobatch non chiude il goal*)
    apply ((H H3))
  | (*autobatch non chiude il goal*)
    apply ((H1 H3))
  | (*autobatch non chiude il goal*)
    apply ((H2 H3))
  ]
]
qed.
