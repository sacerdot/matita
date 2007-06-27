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

set "baseuri" "cic:/matita/nat/propr_div_mod_lt_le_totient1_aux/".

include "nat/iteration2.ma".

(*this part of the library contains some properties useful to prove
  the main theorem in totient1.ma, and some new properties about gcd
  (see gcd_properties1.ma).
  These theorems are saved separately from the other part of the library
  in order to avoid to create circular dependences in it.
 *)

(* some basic properties of and - or*)
theorem andb_sym: \forall A,B:bool.
(A \land B) = (B \land A).
intros.
elim A;
  elim B;
    simplify;
    reflexivity.
qed.

theorem andb_assoc: \forall A,B,C:bool.
(A \land (B \land C)) = ((A \land B) \land C).
intros.
elim A;
  elim B;
    elim C;
      simplify;
      reflexivity.
qed.

theorem orb_sym: \forall A,B:bool.
(A \lor B) = (B \lor A).
intros.
elim A;
  elim B;
    simplify;
    reflexivity.
qed.

theorem andb_t_t_t: \forall A,B,C:bool.
A = true \to B = true \to C = true \to (A \land (B \land C)) = true.
intros.
rewrite > H.
rewrite > H1.
rewrite > H2.
reflexivity.
qed.

(*properties about relational operators*)

theorem Sa_le_b_to_O_lt_b: \forall a,b:nat.
(S a) \le b \to O \lt b.
intros.
elim H;
  apply lt_O_S.
qed.

theorem n_gt_Uno_to_O_lt_pred_n: \forall n:nat.
(S O) \lt n \to O \lt (pred n).
intros.
elim H
[ simplify.
  apply (lt_O_S O)
| rewrite < (pred_Sn n1).
  apply (lt_to_le_to_lt O (S (S O)) n1)
  [ apply le_S.
    apply (le_n (S O))
  | assumption
  ]
]
qed.


theorem NdivM_times_M_to_N: \forall n,m:nat.
O \lt m \to m \divides n \to (n / m) * m = n.
intros.
rewrite > plus_n_O.
apply sym_eq.
cut (O = n \mod m)
[ rewrite > Hcut.
  apply div_mod.
  assumption
| apply sym_eq.
  apply divides_to_mod_O;
    assumption.
  
]
qed.

theorem lt_to_divides_to_div_le:  \forall a,c:nat.
O \lt c \to c \divides a \to a/c \le a.
intros.
apply (le_times_to_le c (a/c) a)
[ assumption
| rewrite > (sym_times c (a/c)).
  rewrite > (NdivM_times_M_to_N a c) in \vdash (? % ?)
  [ rewrite < (sym_times a c).
    apply (O_lt_const_to_le_times_const).
    assumption
  | assumption
  | assumption
  ]
]
qed.


theorem bTIMESc_le_a_to_c_le_aDIVb: \forall a,b,c:nat.
O \lt b \to (b*c) \le a \to c \le (a /b).
intros.
rewrite > (div_mod a b) in H1
[ apply (le_times_to_le b ? ?)
  [ assumption
  | cut ( (c*b) \le ((a/b)*b) \lor ((a/b)*b) \lt (c*b))
    [ elim Hcut
      [ rewrite < (sym_times c b).
        rewrite < (sym_times (a/b) b).
        assumption
      | cut (a/b \lt c)
        [ change in Hcut1 with ((S (a/b)) \le c).
          cut( b*(S (a/b)) \le b*c)
          [ rewrite > (sym_times b (S (a/b))) in Hcut2.
            simplify in Hcut2.
            cut ((b + (a/b)*b) \le ((a/b)*b + (a \mod b)))
            [ cut (b \le (a \mod b))
              [ apply False_ind.
                apply (lt_to_not_le (a \mod b) b)
                [ apply (lt_mod_m_m).
                  assumption
                | assumption
                ]
              | apply (le_plus_to_le ((a/b)*b)).
                rewrite > sym_plus.
                assumption.
              ]
            | apply (trans_le ? (b*c) ?);
                assumption
            ]
          | apply (le_times_r b ? ?).
            assumption
          ]
        | apply (lt_times_n_to_lt b (a/b) c)
          [ assumption
          | assumption
          ]
        ]
      ]
    | apply (leb_elim (c*b) ((a/b)*b))
      [ intros.
        left.
        assumption
      | intros.
        right.
        apply cic:/matita/nat/orders/not_le_to_lt.con. 
        assumption        
      ]
    ]
  ]
| assumption
] 
qed.

theorem lt_O_a_lt_O_b_a_divides_b_to_lt_O_aDIVb:
\forall a,b:nat.
O \lt a \to O \lt b \to a \divides b \to O \lt (b/a).
intros.
elim H2.
cut (O \lt n2)
[ rewrite > H3.
  rewrite > (sym_times a n2).
  rewrite > (div_times_ltO n2 a);
    assumption  
| apply (divides_to_lt_O n2 b)
  [ assumption
  | apply (witness n2 b a).
    rewrite > sym_times.
    assumption
  ] 
]
qed.

(* some properties of div operator between natural numbers *)

theorem separazioneFattoriSuDivisione: \forall a,b,c:nat.
O \lt b \to c \divides b \to a * (b /c) = (a*b)/c.
intros.
elim H1.
rewrite > H2.
rewrite > (sym_times c n2).
cut(O \lt c)
[ rewrite > (div_times_ltO n2 c)
  [ rewrite < assoc_times.
    rewrite > (div_times_ltO (a *n2) c)
    [ reflexivity
    | assumption
    ]
  | assumption
  ]  
| apply (divides_to_lt_O c b);
    assumption.
]
qed.


theorem div_times_to_eqSO: \forall a,d:nat.
O \lt d \to a*d = d \to a = (S O).
intros.
rewrite > (plus_n_O d) in H1:(? ? ? %).
cut (a*d -d = O)
[ rewrite  > sym_times in Hcut.
  rewrite > times_n_SO in Hcut:(? ? (? ? %) ?).
  rewrite < distr_times_minus in Hcut.
  cut ((a - (S O)) = O)
  [ apply (minus_to_plus a (S O) O)
    [ apply (nat_case1 a)
      [ intros.
        rewrite > H2 in H1.
        simplify in H1.
        rewrite < (plus_n_O d) in H1.
        rewrite < H1 in H.
        apply False_ind.
        change in H with ((S O) \le O).
        apply (not_le_Sn_O O H)
      | intros.
        apply (le_S_S O m).
        apply (le_O_n m)
      ]
    | assumption
    ]
  | apply (lt_times_eq_O d (a - (S O)));
      assumption
  ]
| apply (plus_to_minus ).
  assumption
]
qed.

theorem div_mod_minus:
\forall a,b:nat. O \lt b \to
(a /b)*b = a - (a \mod b).
intros.
apply sym_eq.
apply (inj_plus_r (a \mod b)).
rewrite > (sym_plus (a \mod b) ?).
rewrite < (plus_minus_m_m a (a \mod b))
[ rewrite > sym_plus.
  apply div_mod.
  assumption
| rewrite > (div_mod a b) in \vdash (? ? %)
  [ rewrite > plus_n_O in \vdash (? % ?).
    rewrite > sym_plus.
    apply cic:/matita/nat/le_arith/le_plus_n.con
  | assumption
  ]
]
qed.

theorem sum_div_eq_div: \forall a,b,c:nat.
O \lt c \to b \lt c \to c \divides a \to (a+b) /c = a/c.
intros.
elim H2.
rewrite > H3.
rewrite > (sym_times c n2).
rewrite > (div_plus_times c n2 b)
[ rewrite > (div_times_ltO n2 c)
  [ reflexivity
  | assumption
  ]
| assumption
]
qed.


(* A corollary to the division theorem (between natural numbers).
 *
 * Forall a,b,c: Nat, b > O,
 *  a/b = c iff (b*c <= a && a < b*(c+1)
 *
 * two parts of the theorem are proved separately
 *  - (=>) th_div_interi_2
 *  - (<=) th_div_interi_1
 *)

theorem th_div_interi_2: \forall a,b,c:nat.
O \lt b \to a/b = c \to (b*c \le a \land a \lt b*(S c)).
intros.
split
[ rewrite < H1.
  rewrite > sym_times.
  rewrite > div_mod_minus
  [ apply (le_minus_m a (a \mod b))
  | assumption
  ]
| rewrite < (times_n_Sm b c).
  rewrite < H1.
  rewrite > sym_times.
  rewrite > div_mod_minus
  [ rewrite < (eq_minus_plus_plus_minus b a (a \mod b))
    [ rewrite < (sym_plus a b).
      rewrite > (eq_minus_plus_plus_minus a b (a \mod b))
      [ rewrite > (plus_n_O a) in \vdash (? % ?).
        apply (le_to_lt_to_plus_lt)
        [ apply (le_n a)
        | apply cic:/matita/nat/minus/lt_to_lt_O_minus.con.      
          apply cic:/matita/nat/div_and_mod/lt_mod_m_m.con.
          assumption
        ]
      | apply lt_to_le.
        apply lt_mod_m_m.
        assumption
      ]
    | rewrite > (div_mod a b) in \vdash (? ? %)
      [ rewrite > plus_n_O in \vdash (? % ?).
        rewrite > sym_plus.
        apply cic:/matita/nat/le_arith/le_plus_n.con
      | assumption
      ]
    ]
  | assumption
  ]
]
qed.

theorem th_div_interi_1: \forall a,c,b:nat.
O \lt b \to (b*c) \le a \to a \lt (b*(S c)) \to a/b = c.
intros.
apply (le_to_le_to_eq)
[ cut (a/b \le c \lor c \lt a/b)
  [ elim Hcut
    [ assumption
    | change in H3 with ((S c) \le (a/b)).
      cut (b*(S c) \le (b*(a/b)))
      [ rewrite > (sym_times b (S c)) in Hcut1.
        cut (a \lt (b * (a/b)))
        [ rewrite > (div_mod a b) in Hcut2:(? % ?)
          [ rewrite > (plus_n_O (b*(a/b))) in Hcut2:(? ? %).
            cut ((a \mod b) \lt O)
            [ apply False_ind.
              apply (lt_to_not_le (a \mod b) O)
              [ assumption
              | apply le_O_n
              ]              
            | apply (lt_plus_to_lt_r ((a/b)*b)).
              rewrite > (sym_times b (a/b)) in Hcut2:(? ? (? % ?)).
              assumption 
            ]
          | assumption
          ]
        | apply (lt_to_le_to_lt ? (b*(S c)) ?)
          [ assumption
          | rewrite > (sym_times b (S c)).
            assumption
          ]
        ]
      | apply le_times_r.
        assumption
      ]
    ]
  | apply (leb_elim (a/b) c)
    [ intros.
      left.
      assumption
    | intros.
      right.
      apply cic:/matita/nat/orders/not_le_to_lt.con. 
      assumption
    ]
  ] 
| apply (bTIMESc_le_a_to_c_le_aDIVb);
    assumption
]
qed.

theorem times_numerator_denominator_aux: \forall a,b,c,d:nat.
O \lt c \to O \lt b \to d = (a/b) \to d= (a*c)/(b*c).
intros.
apply sym_eq.
cut (b*d \le a \land a \lt b*(S d))
[ elim Hcut.
  apply th_div_interi_1
  [ rewrite > (S_pred b)
    [ rewrite > (S_pred c)
      [ apply (lt_O_times_S_S)
      | assumption
      ]
    | assumption
    ]
  | rewrite > assoc_times.
    rewrite > (sym_times c d).
    rewrite < assoc_times.
    rewrite > (sym_times (b*d) c).
    rewrite > (sym_times a c).
    apply (le_times_r c (b*d) a).
    assumption
  | rewrite > (sym_times a c).
    rewrite > (assoc_times ).
    rewrite > (sym_times c (S d)).
    rewrite < (assoc_times).
    rewrite > (sym_times (b*(S d)) c).
    apply (lt_times_r1 c a (b*(S d)));
      assumption    
  ]
| apply (th_div_interi_2)
  [ assumption
  | apply sym_eq.
    assumption
  ]
]
qed.

theorem times_numerator_denominator: \forall a,b,c:nat. 
O \lt c \to O \lt b \to (a/b) = (a*c)/(b*c).
intros.
apply (times_numerator_denominator_aux a b c (a/b))
[ assumption
| assumption
| reflexivity
]
qed.

theorem times_mod: \forall a,b,c:nat.
O \lt c \to O \lt b \to ((a*c) \mod (b*c)) = c*(a\mod b).
intros.
apply (div_mod_spec_to_eq2 (a*c) (b*c) (a/b) ((a*c) \mod (b*c)) (a/b) (c*(a \mod b)))
[ apply div_mod_spec_intro
  [ apply (lt_mod_m_m (a*c) (b*c)).
    rewrite > (S_pred b)
    [ rewrite > (S_pred c)
      [ apply lt_O_times_S_S
      | assumption
      ]
    | assumption
    ]
  | rewrite > (times_numerator_denominator a b c)
    [ apply (div_mod (a*c) (b*c)).
      rewrite > (S_pred b)
      [ rewrite > (S_pred c)
        [ apply (lt_O_times_S_S)
        | assumption
        ]
      | assumption
      ]
    | assumption
    | assumption
    ]
  ]
| constructor 1
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











