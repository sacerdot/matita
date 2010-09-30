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

include "nat/minus.ma".

let rec max i f \def
  match (f i) with 
  [ true \Rightarrow i
  | false \Rightarrow 
      match i with 
      [ O \Rightarrow O
      | (S j) \Rightarrow max j f ]].

theorem max_O_f : \forall f: nat \to bool. max O f = O.
intro. simplify.
elim (f O).
simplify.reflexivity.
simplify.reflexivity.
qed. 

theorem max_S_max : \forall f: nat \to bool. \forall n:nat.
(f (S n) = true \land max (S n) f = (S n)) \lor 
(f (S n) = false \land max (S n) f = max n f).
intros.simplify.elim (f (S n)).
simplify.left.split.reflexivity.reflexivity.
simplify.right.split.reflexivity.reflexivity.
qed.

theorem le_max_n : \forall f: nat \to bool. \forall n:nat.
max n f \le n.
intros.elim n.rewrite > max_O_f.apply le_n.
simplify.elim (f (S n1)).simplify.apply le_n.
simplify.apply le_S.assumption.
qed.

theorem le_to_le_max : \forall f: nat \to bool. \forall n,m:nat.
n\le m  \to max n f \le max m f.
intros.elim H.
apply le_n.
apply (trans_le ? (max n1 f)).apply H2.
cut ((f (S n1) = true \land max (S n1) f = (S n1)) \lor 
(f (S n1) = false \land max (S n1) f = max n1 f)).
elim Hcut.elim H3.
rewrite > H5.
apply le_S.apply le_max_n.
elim H3.rewrite > H5.apply le_n.
apply max_S_max.
qed.

theorem f_m_to_le_max: \forall f: nat \to bool. \forall n,m:nat.
m\le n \to f m = true \to m \le max n f.
intros 3.elim n.apply (le_n_O_elim m H).
apply le_O_n.
apply (le_n_Sm_elim m n1 H1).
intro.apply (trans_le ? (max n1 f)).
apply H.apply le_S_S_to_le.assumption.assumption.
apply le_to_le_max.apply le_n_Sn.
intro.simplify.rewrite < H3. 
rewrite > H2.simplify.apply le_n.
qed.

theorem max_f_g: \forall f,g,n. (\forall i. i \le n \to f i = g i) \to
max n f = max n g.
intros 3.
elim n
  [simplify.
   rewrite > (H O)
    [reflexivity
    |apply le_n
    ]
  |simplify.
   rewrite > H
    [rewrite > H1
      [reflexivity
      |apply le_n
      ]
    |intros.
     apply H1.
     apply le_S.
     assumption
    ]
  ]
qed.

theorem le_max_f_max_g: \forall f,g,n. (\forall i. i \le n \to f i = true \to g i =true) \to
max n f \le max n g.
intros 3.
elim n
  [simplify.
   elim (f O);apply le_O_n
  |simplify.
   apply (bool_elim ? (f (S n1)));intro
    [rewrite > (H1 (S n1) ? H2)
      [apply le_n
      |apply le_n
      ]
    |cases (g(S n1))
      [simplify.
       apply le_S.
       apply le_max_n
      |simplify.
       apply H.
       intros.
       apply H1
        [apply le_S.assumption
        |assumption
        ]
      ]
    ]
  ]
qed.


theorem max_O : \forall f:nat \to bool. \forall n:nat.
(\forall i:nat. le i n \to f i = false) \to max n f = O.
intros 2.elim n
  [simplify.rewrite > H
    [reflexivity
    |apply le_O_n
    ]
  |simplify.rewrite > H1
    [simplify.apply H.
     intros.
     apply H1.
     apply le_S.
     assumption
    |apply le_n
    ]
  ]
qed.

theorem f_max_true : \forall f:nat \to bool. \forall n:nat.
(\exists i:nat. le i n \land f i = true) \to f (max n f) = true. 
intros 2.
elim n.elim H.elim H1.generalize in match H3.
apply (le_n_O_elim a H2).intro.simplify.rewrite > H4.
simplify.assumption.
simplify.
apply (bool_ind (\lambda b:bool.
(f (S n1) = b) \to (f (match b in bool with
[ true \Rightarrow (S n1)
| false  \Rightarrow (max n1 f)])) = true)).
simplify.intro.assumption.
simplify.intro.apply H.
elim H1.elim H3.generalize in match H5.
apply (le_n_Sm_elim a n1 H4).
intros.
apply (ex_intro nat ? a).
split.apply le_S_S_to_le.assumption.assumption.
intros.apply False_ind.apply not_eq_true_false.
rewrite < H2.rewrite < H7.rewrite > H6. reflexivity.
reflexivity.
qed.

theorem exists_forall_le:\forall f,n. 
(\exists i. i \le n \land f i = true) \lor
(\forall i. i \le n \to f i = false).
intros.
elim n
  [apply (bool_elim ? (f O));intro
    [left.apply (ex_intro ? ? O).
     split[apply le_n|assumption]
    |right.intros.
     apply (le_n_O_elim ? H1).
     assumption
    ]
  |elim H
    [elim H1.elim H2.
     left.apply (ex_intro ? ? a).
     split[apply le_S.assumption|assumption]
    |apply (bool_elim ? (f (S n1)));intro
      [left.apply (ex_intro ? ? (S n1)).
       split[apply le_n|assumption]
      |right.intros.
       elim (le_to_or_lt_eq ? ? H3)
        [apply H1.
         apply le_S_S_to_le.
         apply H4
        |rewrite > H4.
         assumption
        ]
      ]
    ]
  ]
qed.
     
theorem exists_max_forall_false:\forall f,n. 
((\exists i. i \le n \land f i = true) \land (f (max n f) = true))\lor
((\forall i. i \le n \to f i = false) \land (max n f) = O).
intros.
elim (exists_forall_le f n)
  [left.split
    [assumption
    |apply f_max_true.assumption
    ]
  |right.split
    [assumption
    |apply max_O.assumption
    ]
  ]
qed.

theorem false_to_lt_max: \forall f,n,m.O < n \to
f n = false \to max m f \le n \to max m f < n.
intros.
elim (le_to_or_lt_eq ? ? H2)
  [assumption
  |elim (exists_max_forall_false f m)
    [elim H4.
     apply False_ind.
     apply not_eq_true_false.
     rewrite < H6.
     rewrite > H3.
     assumption
    |elim H4.
     rewrite > H6.
     assumption
    ]
  ]
qed.

theorem lt_max_to_false : \forall f:nat \to bool. 
\forall n,m:nat. (max n f) < m \to m \leq n \to f m = false.
intros 2.
elim n.absurd (le m O).assumption.
cut (O < m).apply (lt_O_n_elim m Hcut).exact not_le_Sn_O.
rewrite < (max_O_f f).assumption.
elim (max_S_max f n1) in H1 ⊢ %.
elim H1.
absurd (m \le S n1).assumption.
apply lt_to_not_le.rewrite < H5.assumption.
elim H1.
apply (le_n_Sm_elim m n1 H2).
intro.
apply H.rewrite < H5.assumption.
apply le_S_S_to_le.assumption.
intro.rewrite > H6.assumption.
qed.

theorem f_false_to_le_max: \forall f,n,p. (∃i:nat.i≤n∧f i=true) \to
(\forall m. p < m \to f m = false)
\to max n f \le p.
intros.
apply not_lt_to_le.intro.
apply not_eq_true_false.
rewrite < (H1 ? H2).
apply sym_eq.
apply f_max_true.
assumption.
qed.

definition max_spec \def \lambda f:nat \to bool.\lambda n,m: nat.
m \le n \land (f m)=true \land (\forall i. m < i \to i \le n \to (f i = false)).

theorem max_spec_to_max: \forall f:nat \to bool.\forall n,m:nat.
max_spec f n m \to max n f = m.
intros 2.
elim n
  [elim H.elim H1.apply (le_n_O_elim ? H3).
   apply max_O_f
  |elim H1.
   elim (max_S_max f n1)
    [elim H4.
     rewrite > H6.
     apply le_to_le_to_eq
      [apply not_lt_to_le.
       unfold Not.intro.
       apply not_eq_true_false.
       rewrite < H5.
       apply H3
        [assumption|apply le_n]
      |elim H2.assumption
      ]
    |elim H4.
     rewrite > H6.
     apply H.
     elim H2.
     split
      [split
        [elim (le_to_or_lt_eq ? ? H7)
          [apply le_S_S_to_le.assumption
          |apply False_ind.
           apply not_eq_true_false.
           rewrite < H8.
           rewrite > H9.
           assumption
          ]
        |assumption
        ]
      |intros.
       apply H3
        [assumption|apply le_S.assumption]
      ]
    ]
  ]
qed.
 
let rec min_aux off n f \def
  match f n with 
  [ true \Rightarrow n
  | false \Rightarrow 
      match off with
      [ O \Rightarrow n
      | (S p) \Rightarrow min_aux p (S n) f]].

definition min : nat \to (nat \to bool) \to nat \def
\lambda n.\lambda f. min_aux n O f.

theorem min_aux_O_f: \forall f:nat \to bool. \forall i :nat.
min_aux O i f = i.
intros.simplify.
elim (f i).reflexivity.
simplify.reflexivity.
qed.

theorem min_O_f : \forall f:nat \to bool.
min O f = O.
intro.apply (min_aux_O_f f O).
qed.

theorem min_aux_S : \forall f: nat \to bool. \forall i,n:nat.
((f n) = true \land min_aux (S i) n f = n) \lor 
((f n) = false \land min_aux (S i) n f = min_aux i (S n) f).
intros.simplify.elim (f n).
simplify.left.split.reflexivity.reflexivity.
simplify.right.split.reflexivity.reflexivity.
qed.

theorem f_min_aux_true: \forall f:nat \to bool. \forall off,m:nat.
(\exists i. le m i \land le i (off + m) \land f i = true) \to
f (min_aux off m f) = true. 
intros 2.
elim off.elim H.elim H1.elim H2.
cut (a = m).
rewrite > (min_aux_O_f f).rewrite < Hcut.assumption.
apply (antisym_le a m).assumption.assumption.
simplify.
apply (bool_ind (\lambda b:bool.
(f m = b) \to (f (match b in bool with
[ true \Rightarrow m
| false  \Rightarrow (min_aux n (S m) f)])) = true)).
intro; assumption.
intro. apply H.
elim H1.elim H3.elim H4.
elim (le_to_or_lt_eq ? a H6). 
apply (ex_intro nat ? a).
split.split.
assumption.
rewrite < plus_n_Sm; assumption.
assumption.
absurd (f a = false).rewrite < H8.assumption.
rewrite > H5.
apply not_eq_true_false.
reflexivity.
qed.

theorem f_min_true: \forall f:nat \to bool. \forall m:nat.
(\exists i. le i m \land f i = true) \to
f (min m f) = true.
intros.unfold min.
apply f_min_aux_true.
elim H.clear H.elim H1.clear H1.
apply (ex_intro ? ? a).
split
  [split
    [apply le_O_n
    |rewrite < plus_n_O.assumption
    ]
  |assumption
  ]
qed.

theorem lt_min_aux_to_false : \forall f:nat \to bool. 
\forall n,off,m:nat. n \leq m \to m < (min_aux off n f) \to f m = false.
intros 3.
generalize in match n; clear n;
elim off.absurd (le n1 m).assumption.
apply lt_to_not_le.rewrite < (min_aux_O_f f n1).assumption.
elim (le_to_or_lt_eq ? ? H1);
 [ unfold lt in H3;
   apply (H (S n1));
   [ assumption
   | elim (min_aux_S f n n1);
     [ elim H4;
       elim (not_le_Sn_n n1);
       rewrite > H6 in H2;
       apply (lt_to_le (S n1) n1 ?).
       apply (le_to_lt_to_lt (S n1) m n1 ? ?);
        [apply (H3).
        |apply (H2).
        ]
     | elim H4;
       rewrite < H6;
       assumption
     ]
   ]
 | rewrite < H3 in H2 ⊢ %.
   elim (min_aux_S f n n1);
    [ elim H4;
      rewrite > H6 in H2;
      unfold lt in H2;
      elim (not_le_Sn_n ? H2)
    | elim H4;
      assumption
    ]
 ]
qed.


lemma le_min_aux : \forall f:nat \to bool. 
\forall n,off:nat. n \leq (min_aux off n f).
intros 3.
elim off in n ⊢ %.
rewrite > (min_aux_O_f f n1).apply le_n.
elim (min_aux_S f n n1).
elim H1.rewrite > H3.apply le_n.
elim H1.rewrite > H3.
apply (transitive_le ? (S n1));
 [ apply le_n_Sn
 | apply (H (S n1))
 ]
qed.

theorem le_min_aux_r : \forall f:nat \to bool. 
\forall n,off:nat. (min_aux off n f) \le n+off.
intros.
elim off in n ⊢ %.simplify.
elim (f n1).simplify.rewrite < plus_n_O.apply le_n.
simplify.rewrite < plus_n_O.apply le_n.
simplify.elim (f n1).
simplify.
apply (le_plus_n_r (S n) n1).
simplify.rewrite < plus_n_Sm.
apply (H (S n1)).
qed.