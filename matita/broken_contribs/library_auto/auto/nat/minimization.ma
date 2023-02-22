(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        Matita is distributed under the terms of the          *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

set "baseuri" "cic:/matita/library_autobatch/nat/minimization".

include "auto/nat/minus.ma".

let rec max i f \def
  match (f i) with 
  [ true \Rightarrow i
  | false \Rightarrow 
      match i with 
      [ O \Rightarrow O
      | (S j) \Rightarrow max j f ]].

theorem max_O_f : \forall f: nat \to bool. max O f = O.
intro. simplify.
elim (f O); autobatch.
(*[ simplify.
  reflexivity
| simplify.
  reflexivity
]*)
qed. 

theorem max_S_max : \forall f: nat \to bool. \forall n:nat.
(f (S n) = true \land max (S n) f = (S n)) \lor 
(f (S n) = false \land max (S n) f = max n f).
intros.simplify.elim (f (S n));autobatch.
(*[ simplify.
  left.
  split;reflexivity
| simplify.
  right.
  split;reflexivity.
]*)
qed.

theorem le_max_n : \forall f: nat \to bool. \forall n:nat.
max n f \le n.
intros.
elim n
[ rewrite > max_O_f.
  apply le_n
| simplify.
  elim (f (S n1));simplify;autobatch.
  (*[ simplify.
    apply le_n
  | simplify.
    apply le_S.
    assumption
  ]*)
]
qed.

theorem le_to_le_max : \forall f: nat \to bool. \forall n,m:nat.
n\le m  \to max n f \le max m f.
intros.
elim H
[ apply le_n
| apply (trans_le ? (max n1 f))
  [ apply H2
  | cut ((f (S n1) = true \land max (S n1) f = (S n1)) \lor 
    (f (S n1) = false \land max (S n1) f = max n1 f))
    [ elim Hcut;elim H3;rewrite > H5;autobatch
      (*[ elim H3.
        rewrite > H5.
        apply le_S.
        apply le_max_n.
      | elim H3.
        rewrite > H5.
        apply le_n.
      ]*)
    | apply max_S_max.
    ]
  ]
]
qed.

theorem f_m_to_le_max: \forall f: nat \to bool. \forall n,m:nat.
m\le n \to f m = true \to m \le max n f.
intros 3.
elim n
[ autobatch.
  (*apply (le_n_O_elim m H).
  apply le_O_n.*)
| apply (le_n_Sm_elim m n1 H1);intro
  [ apply (trans_le ? (max n1 f)); autobatch
    (*[ apply H
      [apply le_S_S_to_le.
        assumption
      | assumption
      ]
    | apply le_to_le_max.
      apply le_n_Sn.
    ]*)
  | simplify.
    rewrite < H3.
    rewrite > H2.
    autobatch
    (*simplify.
    apply le_n.*)
  ]
]
qed.


definition max_spec \def \lambda f:nat \to bool.\lambda n: nat.
\exists i. (le i n) \land (f i = true) \to
(f n) = true \land (\forall i. i < n \to (f i = false)).

theorem f_max_true : \forall f:nat \to bool. \forall n:nat.
(\exists i:nat. le i n \land f i = true) \to f (max n f) = true. 
intros 2.
elim n
[ elim H.
  elim H1.
  generalize in match H3.
  apply (le_n_O_elim a H2).
  autobatch
  (*intro.
  simplify.
  rewrite > H4.
  simplify.
  assumption.*)
| simplify.
  apply (bool_ind (\lambda b:bool.
  (f (S n1) = b) \to (f (match b in bool with
  [ true \Rightarrow (S n1)
  | false  \Rightarrow (max n1 f)])) = true))
  
  [ autobatch
    (*simplify.
    intro.
    assumption.*)
  | simplify.
    intro.
    apply H.
    elim H1.
    elim H3.
    generalize in match H5.
    apply (le_n_Sm_elim a n1 H4)
    [ intros.
      apply (ex_intro nat ? a).
      autobatch
      (*split
      [ apply le_S_S_to_le.
        assumption.
      | assumption.
      ]*)
    | intros.
      (* una chiamata di autobatch in questo punto genera segmentation fault*)
      apply False_ind.
      (* una chiamata di autobatch in questo punto genera segmentation fault*)
      apply not_eq_true_false.
      (* una chiamata di autobatch in questo punto genera segmentation fault*)
      rewrite < H2.
      (* una chiamata di autobatch in questo punto genera segmentation fault*)
      rewrite < H7.
      (* una chiamata di autobatch in questo punto genera segmentation fault*)
      rewrite > H6. 
      reflexivity.
    ]
  | reflexivity.
  ]
]
qed.

theorem lt_max_to_false : \forall f:nat \to bool. 
\forall n,m:nat. (max n f) < m \to m \leq n \to f m = false.
intros 2.
elim n
[ absurd (le m O);autobatch
  (*[ assumption
  | cut (O < m)
    [ apply (lt_O_n_elim m Hcut).
      exact not_le_Sn_O.
    | rewrite < (max_O_f f).
      assumption.
    ]
  ]*)
| generalize in match H1.
  elim (max_S_max f n1)
  [ elim H3.
    absurd (m \le S n1)
    [ assumption
    | apply lt_to_not_le.
      rewrite < H6.
      assumption
    ]
  | elim H3.
    apply (le_n_Sm_elim m n1 H2)
    [ intro.
      apply H;autobatch
      (*[ rewrite < H6.
        assumption
      | apply le_S_S_to_le.
        assumption
      ]*)
    | intro.
      autobatch
      (*rewrite > H7.
      assumption*)
    ]
  ]
]qed.

let rec min_aux off n f \def
  match f (n-off) with 
  [ true \Rightarrow (n-off)
  | false \Rightarrow 
      match off with
      [ O \Rightarrow n
      | (S p) \Rightarrow min_aux p n f]].

definition min : nat \to (nat \to bool) \to nat \def
\lambda n.\lambda f. min_aux n n f.

theorem min_aux_O_f: \forall f:nat \to bool. \forall i :nat.
min_aux O i f = i.
intros.simplify.
(*una chiamata di autobatch a questo punto porta ad un'elaborazione molto lunga (forse va
  in loop): dopo circa 3 minuti non era ancora terminata.
 *)
rewrite < minus_n_O.
(*una chiamata di autobatch a questo punto porta ad un'elaborazione molto lunga (forse va
  in loop): dopo circa 3 minuti non era ancora terminata.
 *)
elim (f i); autobatch.
(*[ reflexivity.
  simplify
| reflexivity
]*)
qed.

theorem min_O_f : \forall f:nat \to bool.
min O f = O.
intro.
(* una chiamata di autobatch a questo punto NON conclude la dimostrazione*)
apply (min_aux_O_f f O).
qed.

theorem min_aux_S : \forall f: nat \to bool. \forall i,n:nat.
(f (n -(S i)) = true \land min_aux (S i) n f = (n - (S i))) \lor 
(f (n -(S i)) = false \land min_aux (S i) n f = min_aux i n f).
intros.simplify.elim (f (n - (S i)));autobatch.
(*[ simplify.
  left.
  split;reflexivity.
| simplify.
  right.
  split;reflexivity.
]*)
qed.

theorem f_min_aux_true: \forall f:nat \to bool. \forall off,m:nat.
(\exists i. le (m-off) i \land le i m \land f i = true) \to
f (min_aux off m f) = true. 
intros 2.
elim off
[ elim H.
  elim H1.
  elim H2.
  cut (a = m)
  [ autobatch.
    (*rewrite > (min_aux_O_f f).
    rewrite < Hcut.
    assumption*)
  | apply (antisym_le a m)
    [ assumption
    | rewrite > (minus_n_O m).
      assumption
    ]
  ]
| simplify.
  apply (bool_ind (\lambda b:bool.
  (f (m-(S n)) = b) \to (f (match b in bool with
  [ true \Rightarrow m-(S n)
  | false  \Rightarrow (min_aux n m f)])) = true))
  [ autobatch
    (*simplify.
    intro.
    assumption.*)
  | simplify.
    intro.
    apply H.
    elim H1.
    elim H3.
    elim H4.
    elim (le_to_or_lt_eq (m-(S n)) a H6)
    [ apply (ex_intro nat ? a).
      split;autobatch
      (*[ autobatch.split
        [ apply lt_minus_S_n_to_le_minus_n.
          assumption
        | assumption
        ]
      | assumption
      ]*)
    | absurd (f a = false)
      [ (* una chiamata di autobatch in questo punto genera segmentation fault*)
        rewrite < H8.
        assumption.
      | rewrite > H5.
        apply not_eq_true_false
      ]
    ]
  | reflexivity.
  ]
]
qed.

theorem lt_min_aux_to_false : \forall f:nat \to bool. 
\forall n,off,m:nat. (n-off) \leq m \to m < (min_aux off n f) \to f m = false.
intros 3.
elim off
[absurd (le n m)
  [ rewrite > minus_n_O.
    assumption
  | apply lt_to_not_le.
    rewrite < (min_aux_O_f f n).
    assumption
  ]
| generalize in match H1.
  elim (min_aux_S f n1 n)
  [ elim H3.
    absurd (n - S n1 \le m)
    [ assumption
    | apply lt_to_not_le.
      rewrite < H6.
      assumption
    ]
  | elim H3.
    elim (le_to_or_lt_eq (n -(S n1)) m)
    [ apply H
      [ autobatch
        (*apply lt_minus_S_n_to_le_minus_n.
        assumption*)
      | rewrite < H6.
        assumption
      ]
    | rewrite < H7.
      assumption
    | assumption
    ]
  ]
]
qed.

theorem le_min_aux : \forall f:nat \to bool. 
\forall n,off:nat. (n-off) \leq (min_aux off n f).
intros 3.
elim off
[ rewrite < minus_n_O.
  autobatch
  (*rewrite > (min_aux_O_f f n).
  apply le_n.*)
| elim (min_aux_S f n1 n)
  [ elim H1.
    autobatch
    (*rewrite > H3.
    apply le_n.*)
  | elim H1.
    rewrite > H3.
    autobatch
    (*apply (trans_le (n-(S n1)) (n-n1))
    [ apply monotonic_le_minus_r.
      apply le_n_Sn.
    | assumption.
    ]*)
  ]
]
qed.

theorem le_min_aux_r : \forall f:nat \to bool. 
\forall n,off:nat. (min_aux off n f) \le n.
intros.
elim off
[ simplify.
  rewrite < minus_n_O.
  elim (f n);autobatch
  (*[simplify.
    apply le_n.
  | simplify.
    apply le_n.
  ]*)
| simplify.
  elim (f (n -(S n1)));simplify;autobatch
  (*[ apply le_plus_to_minus.
    rewrite < sym_plus.
    apply le_plus_n
  | assumption
  ]*)
]
qed.
