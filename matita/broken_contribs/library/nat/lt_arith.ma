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

include "nat/div_and_mod.ma".

(* plus *)
theorem monotonic_lt_plus_r: 
\forall n:nat.monotonic nat lt (\lambda m.n+m).
simplify.intros.
elim n.simplify.assumption.
simplify.unfold lt.
apply le_S_S.assumption.
qed.

variant lt_plus_r: \forall n,p,q:nat. p < q \to n + p < n + q \def
monotonic_lt_plus_r.

theorem monotonic_lt_plus_l: 
\forall n:nat.monotonic nat lt (\lambda m.m+n).
simplify.
intros.
rewrite < sym_plus. rewrite < (sym_plus n).
apply lt_plus_r.assumption.
qed.

variant lt_plus_l: \forall n,p,q:nat. p < q \to p + n < q + n \def
monotonic_lt_plus_l.

theorem lt_plus: \forall n,m,p,q:nat. n < m \to p < q \to n + p < m + q.
intros.
apply (trans_lt ? (n + q)).
apply lt_plus_r.assumption.
apply lt_plus_l.assumption.
qed.

theorem lt_plus_to_lt_l :\forall n,p,q:nat. p+n < q+n \to p<q.
intro.elim n.
rewrite > plus_n_O.
rewrite > (plus_n_O q).assumption.
apply H.
unfold lt.apply le_S_S_to_le.
rewrite > plus_n_Sm.
rewrite > (plus_n_Sm q).
exact H1.
qed.

theorem lt_plus_to_lt_r :\forall n,p,q:nat. n+p < n+q \to p<q.
intros.apply (lt_plus_to_lt_l n). 
rewrite > sym_plus.
rewrite > (sym_plus q).assumption.
qed.

theorem le_to_lt_to_plus_lt: \forall a,b,c,d:nat.
a \le c \to b \lt d \to (a + b) \lt (c+d).
intros.
cut (a \lt c \lor a = c)
[ elim Hcut
  [ apply (lt_plus );
      assumption
  | rewrite > H2.
    apply (lt_plus_r c b d).
    assumption
  ]
| apply le_to_or_lt_eq.
  assumption
]
qed.


(* times and zero *)
theorem lt_O_times_S_S: \forall n,m:nat.O < (S n)*(S m).
intros.simplify.unfold lt.apply le_S_S.apply le_O_n.
qed.

theorem lt_times_eq_O: \forall a,b:nat.
O \lt a \to (a * b) = O \to b = O.
intros.
apply (nat_case1 b)
[ intros.
  reflexivity
| intros.
  rewrite > H2 in H1.
  rewrite > (S_pred a) in H1
  [ apply False_ind.
    apply (eq_to_not_lt O ((S (pred a))*(S m)))
    [ apply sym_eq.
      assumption
    | apply lt_O_times_S_S
    ]
  | assumption
  ]
]
qed.

theorem O_lt_times_to_O_lt: \forall a,c:nat.
O \lt (a * c) \to O \lt a.
intros.
apply (nat_case1 a)
[ intros.
  rewrite > H1 in H.
  simplify in H.
  assumption
| intros.
  apply lt_O_S
]
qed.

lemma lt_times_to_lt_O: \forall i,n,m:nat. i < n*m \to O < m.
intros.
elim (le_to_or_lt_eq O ? (le_O_n m))
  [assumption
  |apply False_ind.
   rewrite < H1 in H.
   rewrite < times_n_O in H.
   apply (not_le_Sn_O ? H)
  ]
qed.

(* times *)
theorem monotonic_lt_times_r: 
\forall n:nat.monotonic nat lt (\lambda m.(S n)*m).
simplify.
intros.elim n.
simplify.rewrite < plus_n_O.rewrite < plus_n_O.assumption.
apply lt_plus.assumption.assumption.
qed.

(* a simple variant of the previus monotionic_lt_times *)
theorem monotonic_lt_times_variant: \forall c:nat.
O \lt c \to monotonic nat lt (\lambda t.(t*c)).
intros.
apply (increasing_to_monotonic).
unfold increasing.
intros.
simplify.
rewrite > sym_plus.
rewrite > plus_n_O in \vdash (? % ?).
apply lt_plus_r.
assumption.
qed.

theorem lt_times_r: \forall n,p,q:nat. p < q \to (S n) * p < (S n) * q
\def monotonic_lt_times_r.

theorem monotonic_lt_times_l: 
\forall m:nat.monotonic nat lt (\lambda n.n * (S m)).
simplify.
intros.
rewrite < sym_times.rewrite < (sym_times (S m)).
apply lt_times_r.assumption.
qed.

variant lt_times_l: \forall n,p,q:nat. p<q \to p*(S n) < q*(S n)
\def monotonic_lt_times_l.

theorem lt_times:\forall n,m,p,q:nat. n<m \to p<q \to n*p < m*q.
intro.
elim n.
apply (lt_O_n_elim m H).
intro.
cut (lt O q).
apply (lt_O_n_elim q Hcut).
intro.change with (O < (S m1)*(S m2)).
apply lt_O_times_S_S.
apply (ltn_to_ltO p q H1).
apply (trans_lt ? ((S n1)*q)).
apply lt_times_r.assumption.
cut (lt O q).
apply (lt_O_n_elim q Hcut).
intro.
apply lt_times_l.
assumption.
apply (ltn_to_ltO p q H2).
qed.

theorem lt_times_r1: 
\forall n,m,p. O < n \to m < p \to n*m < n*p.
intros.
elim H;apply lt_times_r;assumption.
qed.

theorem lt_times_l1: 
\forall n,m,p. O < n \to m < p \to m*n < p*n.
intros.
elim H;apply lt_times_l;assumption.
qed.

theorem lt_to_le_to_lt_times : 
\forall n,n1,m,m1. n < n1 \to m \le m1 \to O < m1 \to n*m < n1*m1.
intros.
apply (le_to_lt_to_lt ? (n*m1))
  [apply le_times_r.assumption
  |apply lt_times_l1
    [assumption|assumption]
  ]
qed.

theorem lt_times_to_lt_l: 
\forall n,p,q:nat. p*(S n) < q*(S n) \to p < q.
intros.
cut (p < q \lor p \nlt q).
elim Hcut.
assumption.
absurd (p * (S n) < q * (S n)).
assumption.
apply le_to_not_lt.
apply le_times_l.
apply not_lt_to_le.
assumption.
exact (decidable_lt p q).
qed.

theorem lt_times_n_to_lt: 
\forall n,p,q:nat. O < n \to p*n < q*n \to p < q.
intro.
apply (nat_case n)
  [intros.apply False_ind.apply (not_le_Sn_n ? H)
  |intros 4.apply lt_times_to_lt_l
  ]
qed.

theorem lt_times_to_lt_r: 
\forall n,p,q:nat. (S n)*p < (S n)*q \to lt p q.
intros.
apply (lt_times_to_lt_l n).
rewrite < sym_times.
rewrite < (sym_times (S n)).
assumption.
qed.

theorem lt_times_n_to_lt_r: 
\forall n,p,q:nat. O < n \to n*p < n*q \to lt p q.
intro.
apply (nat_case n)
  [intros.apply False_ind.apply (not_le_Sn_n ? H)
  |intros 4.apply lt_times_to_lt_r
  ]
qed.



theorem nat_compare_times_l : \forall n,p,q:nat. 
nat_compare p q = nat_compare ((S n) * p) ((S n) * q).
intros.apply nat_compare_elim.intro.
apply nat_compare_elim.
intro.reflexivity.
intro.absurd (p=q).
apply (inj_times_r n).assumption.
apply lt_to_not_eq. assumption.
intro.absurd (q<p).
apply (lt_times_to_lt_r n).assumption.
apply le_to_not_lt.apply lt_to_le.assumption.
intro.rewrite < H.rewrite > nat_compare_n_n.reflexivity.
intro.apply nat_compare_elim.intro.
absurd (p<q).
apply (lt_times_to_lt_r n).assumption.
apply le_to_not_lt.apply lt_to_le.assumption.
intro.absurd (q=p).
symmetry.
apply (inj_times_r n).assumption.
apply lt_to_not_eq.assumption.
intro.reflexivity.
qed.

(* times and plus *)
theorem lt_times_plus_times: \forall a,b,n,m:nat. 
a < n \to b < m \to a*m + b < n*m.
intros 3.
apply (nat_case n)
  [intros.apply False_ind.apply (not_le_Sn_O ? H)
  |intros.simplify.
   rewrite < sym_plus.
   unfold.
   change with (S b+a*m1 \leq m1+m*m1).
   apply le_plus
    [assumption
    |apply le_times
      [apply le_S_S_to_le.assumption
      |apply le_n
      ]
    ]
  ]
qed.

(* div *) 

theorem eq_mod_O_to_lt_O_div: \forall n,m:nat. O < m \to O < n\to n \mod m = O \to O < n / m. 
intros 4.apply (lt_O_n_elim m H).intros.
apply (lt_times_to_lt_r m1).
rewrite < times_n_O.
rewrite > (plus_n_O ((S m1)*(n / (S m1)))).
rewrite < H2.
rewrite < sym_times.
rewrite < div_mod.
rewrite > H2.
assumption.
unfold lt.apply le_S_S.apply le_O_n.
qed.

theorem lt_div_n_m_n: \forall n,m:nat. (S O) < m \to O < n \to n / m \lt n.
intros.
apply (nat_case1 (n / m)).intro.
assumption.intros.rewrite < H2.
rewrite > (div_mod n m) in \vdash (? ? %).
apply (lt_to_le_to_lt ? ((n / m)*m)).
apply (lt_to_le_to_lt ? ((n / m)*(S (S O)))).
rewrite < sym_times.
rewrite > H2.
simplify.unfold lt.
rewrite < plus_n_O.
rewrite < plus_n_Sm.
apply le_S_S.
apply le_S_S.
apply le_plus_n.
apply le_times_r.
assumption.
rewrite < sym_plus.
apply le_plus_n.
apply (trans_lt ? (S O)).
unfold lt. apply le_n.assumption.
qed.

theorem eq_div_div_div_times: \forall n,m,q. O < n \to O < m \to
q/n/m = q/(n*m).
intros.
apply (div_mod_spec_to_eq q (n*m) ? (q\mod n+n*(q/n\mod m)) ? (mod q (n*m)))
  [apply div_mod_spec_intro
    [apply (lt_to_le_to_lt ? (n*(S (q/n\mod m))))
      [rewrite < times_n_Sm.
       apply lt_plus_l.
       apply lt_mod_m_m.
       assumption
      |apply le_times_r.
       apply lt_mod_m_m.
       assumption
      ]
    |rewrite > sym_times in ⊢ (? ? ? (? (? ? %) ?)).
     rewrite < assoc_times.
     rewrite > (eq_times_div_minus_mod ? ? H1).
     rewrite > sym_times.
     rewrite > distributive_times_minus.
     rewrite > sym_times.
     rewrite > (eq_times_div_minus_mod ? ? H).
     rewrite < sym_plus in ⊢ (? ? ? (? ? %)).
     rewrite < assoc_plus.
     rewrite < plus_minus_m_m
      [rewrite < plus_minus_m_m
        [reflexivity
        |apply (eq_plus_to_le ? ? ((q/n)*n)).
         rewrite < sym_plus.
         apply div_mod.
         assumption
        ]
      |apply (trans_le ? (n*(q/n)))
        [apply le_times_r.
         apply (eq_plus_to_le ? ? ((q/n)/m*m)).
         rewrite < sym_plus.
         apply div_mod.
         assumption
        |rewrite > sym_times.
         rewrite > eq_times_div_minus_mod
          [apply le_n
          |assumption
          ]
        ]
      ]
    ]
  |apply div_mod_spec_div_mod.
   rewrite > (times_n_O O).
   apply lt_times;assumption
  ]
qed.

theorem eq_div_div_div_div: \forall n,m,q. O < n \to O < m \to
q/n/m = q/m/n.
intros.
apply (trans_eq ? ? (q/(n*m)))
  [apply eq_div_div_div_times;assumption
  |rewrite > sym_times.
   apply sym_eq.
   apply eq_div_div_div_times;assumption
  ]
qed.

theorem SSO_mod: \forall n,m. O < m \to (S(S O))*n/m = (n/m)*(S(S O)) + mod ((S(S O))*n/m) (S(S O)).
intros.
rewrite < (lt_O_to_div_times n (S(S O))) in ⊢ (? ? ? (? (? (? % ?) ?) ?))
  [rewrite > eq_div_div_div_div
    [rewrite > sym_times in ⊢ (? ? ? (? (? (? (? % ?) ?) ?) ?)).
     apply div_mod.
     apply lt_O_S
    |apply lt_O_S
    |assumption
    ]
  |apply lt_O_S
  ]
qed.
(* Forall a,b : N. 0 < b \to b * (a/b) <= a < b * (a/b +1) *)
(* The theorem is shown in two different parts: *)

theorem lt_to_div_to_and_le_times_lt_S: \forall a,b,c:nat.
O \lt b \to a/b = c \to (b*c \le a \land a \lt b*(S c)).
intros.
split
[ rewrite < H1.
  rewrite > sym_times.
  rewrite > eq_times_div_minus_mod
  [ apply (le_minus_m a (a \mod b))
  | assumption
  ]
| rewrite < (times_n_Sm b c).
  rewrite < H1.
  rewrite > sym_times.
  rewrite > (div_mod a b) in \vdash (? % ?)
  [ rewrite > (sym_plus b ((a/b)*b)).
    apply lt_plus_r.
    apply lt_mod_m_m.
    assumption
  | assumption
  ]
]
qed.

theorem lt_to_le_times_to_lt_S_to_div: \forall a,c,b:nat.
O \lt b \to (b*c) \le a \to a \lt (b*(S c)) \to a/b = c.
intros.
apply (le_to_le_to_eq)
[ apply (leb_elim (a/b) c);intros
  [ assumption
  | cut (c \lt (a/b))
    [ apply False_ind.
      apply (lt_to_not_le (a \mod b) O)
      [ apply (lt_plus_to_lt_l ((a/b)*b)).
        simplify.
        rewrite < sym_plus.
        rewrite < div_mod
        [ apply (lt_to_le_to_lt ? (b*(S c)) ?)
          [ assumption
          | rewrite > (sym_times (a/b) b).
            apply le_times_r.
            assumption
          ]
        | assumption
        ]
      | apply le_O_n
      ]
    | apply not_le_to_lt.
      assumption
    ]
  ]
| apply (leb_elim c (a/b));intros
  [ assumption
  | cut((a/b) \lt c) 
    [ apply False_ind.
      apply (lt_to_not_le (a \mod b) b)
      [ apply (lt_mod_m_m).
        assumption
      | apply (le_plus_to_le ((a/b)*b)).
        rewrite < (div_mod a b)
        [ apply (trans_le ? (b*c) ?)
          [ rewrite > (sym_times (a/b) b).
            rewrite > (times_n_SO b) in \vdash (? (? ? %) ?).
            rewrite < distr_times_plus.
            rewrite > sym_plus.
            simplify in \vdash (? (? ? %) ?).
            apply le_times_r.
            assumption
          | assumption
          ]
        | assumption
        ]
      ]
    | apply not_le_to_lt. 
      assumption
    ]
  ]
]
qed.


theorem lt_to_lt_to_eq_div_div_times_times: \forall a,b,c:nat. 
O \lt c \to O \lt b \to (a/b) = (a*c)/(b*c).
intros.
apply sym_eq.
cut (b*(a/b) \le a \land a \lt b*(S (a/b)))
[ elim Hcut.
  apply lt_to_le_times_to_lt_S_to_div
  [ rewrite > (S_pred b)
    [ rewrite > (S_pred c)
      [ apply (lt_O_times_S_S)
      | assumption
      ]
    | assumption
    ]
  | rewrite > assoc_times.
    rewrite > (sym_times c (a/b)).
    rewrite < assoc_times.
    rewrite > (sym_times (b*(a/b)) c).
    rewrite > (sym_times a c).
    apply (le_times_r c (b*(a/b)) a).
    assumption
  | rewrite > (sym_times a c).
    rewrite > (assoc_times ).
    rewrite > (sym_times c (S (a/b))).
    rewrite < (assoc_times).
    rewrite > (sym_times (b*(S (a/b))) c).
    apply (lt_times_r1 c a (b*(S (a/b))));
      assumption    
  ]
| apply (lt_to_div_to_and_le_times_lt_S)
  [ assumption
  | reflexivity
  ]
]
qed.

theorem times_mod: \forall a,b,c:nat.
O \lt c \to O \lt b \to ((a*c) \mod (b*c)) = c*(a\mod b).
intros.
apply (div_mod_spec_to_eq2 (a*c) (b*c) (a/b) ((a*c) \mod (b*c)) (a/b) (c*(a \mod b)))
[ rewrite > (lt_to_lt_to_eq_div_div_times_times a b c)
  [ apply div_mod_spec_div_mod.
    rewrite > (S_pred b)
    [ rewrite > (S_pred c)
      [ apply lt_O_times_S_S
      | assumption
      ]
    | assumption
    ]
  | assumption
  | assumption
  ]
| apply div_mod_spec_intro
  [ rewrite > (sym_times b c).
    apply (lt_times_r1 c)
    [ assumption
    | apply (lt_mod_m_m).
      assumption
    ]
  | rewrite < (assoc_times (a/b) b c).
    rewrite > (sym_times a c).
    rewrite > (sym_times ((a/b)*b) c).
    rewrite < (distr_times_plus c ? ?).
    apply eq_f.
    apply (div_mod a b).
    assumption
  ]
]
qed.




(* general properties of functions *)
theorem monotonic_to_injective: \forall f:nat\to nat.
monotonic nat lt f \to injective nat nat f.
unfold injective.intros.
apply (nat_compare_elim x y).
intro.apply False_ind.apply (not_le_Sn_n (f x)).
rewrite > H1 in \vdash (? ? %).
change with (f x < f y).
apply H.apply H2.
intros.assumption.
intro.apply False_ind.apply (not_le_Sn_n (f y)).
rewrite < H1 in \vdash (? ? %).
change with (f y < f x).
apply H.apply H2.
qed.

theorem increasing_to_injective: \forall f:nat\to nat.
increasing f \to injective nat nat f.
intros.apply monotonic_to_injective.
apply increasing_to_monotonic.assumption.
qed.

