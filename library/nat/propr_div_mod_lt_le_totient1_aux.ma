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
(*theorem andb_sym: \forall A,B:bool.
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
*)
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
apply (Sa_le_b_to_O_lt_b (pred (S O)) (pred n) ?).
 apply (lt_pred (S O) n ? ?);
 [ apply (lt_O_S O) 
 | apply (H)
 ]
qed.


theorem NdivM_times_M_to_N: \forall n,m:nat.
O \lt m \to m \divides n \to (n / m) * m = n.
intros.
rewrite > plus_n_O.
apply sym_eq.
cut (n \mod m = O)
[ rewrite < Hcut.
  apply div_mod.
  assumption
| apply divides_to_mod_O;
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
  [ apply (le_times_n c a ?).   
    assumption
  | assumption
  | assumption
  ]
]
qed.


theorem lt_O_a_lt_O_b_a_divides_b_to_lt_O_aDIVb:
\forall a,b:nat.
O \lt a \to O \lt b \to a \divides b \to O \lt (b/a).
intros.
elim H2.
rewrite > H3.
rewrite > (sym_times a n2).
rewrite > (div_times_ltO n2 a)
[ apply (divides_to_lt_O n2 b)
  [ assumption
  | apply (witness n2 b a).
    rewrite > sym_times.
    assumption
  ]  
| assumption  
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


theorem div_mod_minus:
\forall a,b:nat. O \lt b \to
(a /b)*b = a - (a \mod b).
intros.
rewrite > (div_mod a b) in \vdash (? ? ? (? % ?))
[ apply (minus_plus_m_m (times (div a b) b) (mod a b))
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
  rewrite > (div_mod a b) in \vdash (? % ?)
  [ rewrite > (sym_plus b ((a/b)*b)).
    apply lt_plus_r.
    apply lt_mod_m_m.
    assumption
  | assumption
  ]
]
qed.
  

theorem th_div_interi_1: \forall a,c,b:nat.
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











