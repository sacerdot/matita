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

set "baseuri" "cic:/matita/nat/gcd_properties1".

include "nat/propr_div_mod_lt_le_totient1_aux.ma".

(* this file contains some important properites of gcd in N *)

(*it's a generalization of the existing theorem divides_gcd_aux (in which
  c = 1), proved in file gcd.ma
 *)
theorem divides_times_gcd_aux: \forall p,m,n,d,c. 
O \lt c \to O < n \to n \le m \to n \le p \to
d \divides (c*m) \to d \divides (c*n) \to d \divides c*gcd_aux p m n. 
intro.
elim p
[ absurd (O < n)
  [ assumption
  | apply le_to_not_lt.
    assumption
  ]
| simplify.
  cut (n1 \divides m \lor n1 \ndivides m)
  [ elim Hcut
    [ rewrite > divides_to_divides_b_true
      [ simplify.
        assumption
      | assumption
      | assumption
      ]
    | rewrite > not_divides_to_divides_b_false
      [ simplify.
        apply H
        [ assumption
        | cut (O \lt m \mod n1 \lor O = m \mod n1)
          [ elim Hcut1
            [ assumption
            | absurd (n1 \divides m)
              [ apply mod_O_to_divides
                [ assumption
                | apply sym_eq.
                  assumption
                ]
              | assumption
              ]
            ]
          | apply le_to_or_lt_eq.
            apply le_O_n
          ]
        | apply lt_to_le.
          apply lt_mod_m_m.
          assumption
        | apply le_S_S_to_le.
          apply (trans_le ? n1)
          [ change with (m \mod n1 < n1).
            apply lt_mod_m_m.
            assumption
          | assumption
          ]
        | assumption
        | rewrite < times_mod
          [ rewrite < (sym_times c m).
            rewrite < (sym_times c n1).
            apply divides_mod
            [ rewrite > (S_pred c)
              [ rewrite > (S_pred n1)
                [ apply (lt_O_times_S_S)
                | assumption
                ]
              | assumption
              ]
            | assumption
            | assumption
            ]
          | assumption
          | assumption
          ]
        ]
      | assumption
      | assumption
      ]
    ]
  | apply (decidable_divides n1 m).
    assumption
  ]
]
qed.

(*it's a generalization of the existing theorem divides_gcd_d (in which
  c = 1), proved in file gcd.ma
 *)
theorem divides_d_times_gcd: \forall m,n,d,c. 
O \lt c \to d \divides (c*m) \to d \divides (c*n) \to d \divides c*gcd n m. 
intros.
change with
(d \divides c *
match leb n m with
  [ true \Rightarrow 
    match n with 
    [ O \Rightarrow m
    | (S p) \Rightarrow gcd_aux (S p) m (S p) ]
  | false \Rightarrow 
    match m with 
    [ O \Rightarrow n
    | (S p) \Rightarrow gcd_aux (S p) n (S p) ]]).
apply (leb_elim n m)
[ apply (nat_case1 n)
  [ simplify.
    intros.
    assumption
  | intros.
    change with (d \divides c*gcd_aux (S m1) m (S m1)).
    apply divides_times_gcd_aux
    [ assumption
    | unfold lt.
      apply le_S_S.
      apply le_O_n
    | assumption
    | apply (le_n (S m1))
    | assumption
    | rewrite < H3.
      assumption
    ]
  ]
| apply (nat_case1 m)
  [ simplify.
    intros.
    assumption
  | intros.
    change with (d \divides c * gcd_aux (S m1) n (S m1)).
    apply divides_times_gcd_aux
    [ unfold lt.
      change with (O \lt c).
      assumption
    | apply lt_O_S
    | apply lt_to_le.
      apply not_le_to_lt.
      assumption
    | apply (le_n (S m1)).
    | assumption
    | rewrite < H3.
      assumption
    ]
  ]
]
qed.

(* 2 basic properties of divides predicate *)
theorem aDIVb_to_bDIVa_to_aEQb:
\forall a,b:nat.
a \divides b \to b \divides a \to a = b.
intros.
apply antisymmetric_divides;
  assumption.
qed.


theorem O_div_c_to_c_eq_O: \forall c:nat.
O \divides c \to c = O.
intros.
apply aDIVb_to_bDIVa_to_aEQb
[ apply divides_n_O
| assumption
]
qed.

(* an alternative characterization for gcd *)
theorem gcd1: \forall a,b,c:nat.
c \divides a \to c \divides b \to
(\forall d:nat. d \divides a \to d \divides b \to d \divides c) \to (gcd a b) = c.
intros.
elim (H2 ((gcd a b)))
[ apply (aDIVb_to_bDIVa_to_aEQb (gcd a b) c)
  [ apply (witness (gcd a b) c n2).
    assumption
  | apply divides_d_gcd;
      assumption
  ]
| apply divides_gcd_n
| rewrite > sym_gcd.
  apply divides_gcd_n
]
qed.


theorem eq_gcd_times_times_eqv_times_gcd: \forall a,b,c:nat.
(gcd (c*a) (c*b)) = c*(gcd a b).
intros.
apply (nat_case1 c)
[ intros. 
  simplify.
  reflexivity
| intros.
  rewrite < H.
  apply gcd1
  [ apply divides_times
    [ apply divides_n_n
    | apply divides_gcd_n.
    ]
  | apply divides_times
    [ apply divides_n_n
    | rewrite > sym_gcd.  
      apply divides_gcd_n
    ]
  | intros.
    apply (divides_d_times_gcd)
    [ rewrite > H.
      apply lt_O_S  
    | assumption
    | assumption
    ]
  ]
]
qed.
  
  (* 
  apply (nat_case1 a)
  [ intros.
    rewrite > (sym_times c O).
    simplify.
    reflexivity
  | intros.
    rewrite < H1.
    apply (nat_case1 b)
    [ intros.
      rewrite > (sym_times ? O).
      rewrite > (sym_gcd a O).
      rewrite > sym_gcd.
      simplify.
      reflexivity
    | intros.
      rewrite < H2.
      apply gcd1
      [ apply divides_times
        [ apply divides_n_n
        | apply divides_gcd_n.
        ]
      | apply divides_times
        [ apply divides_n_n
        | rewrite > sym_gcd.  
          apply divides_gcd_n
        ]
      | intros.
        apply (divides_d_times_gcd)
        [ rewrite > H.
          apply lt_O_S  
        | assumption
        | assumption
        ]
      ]
    ]
  ]
]
qed.*)


theorem associative_nat_gcd: associative nat gcd.
change with (\forall a,b,c:nat. (gcd (gcd a b) c) = (gcd a (gcd b c))).
intros.
apply gcd1
[ apply divides_d_gcd
  [ apply (trans_divides ? (gcd b c) ?)
    [ apply divides_gcd_m
    | apply divides_gcd_n
    ]
  | apply divides_gcd_n
  ]
| apply (trans_divides ? (gcd b c) ?)
  [ apply divides_gcd_m
  | apply divides_gcd_m
  ]
| intros.
  cut (d \divides a \land d \divides b)
  [ elim Hcut.
    cut (d \divides (gcd b c))
    [ apply (divides_d_gcd (gcd b c) a d Hcut1 H2)
    | apply (divides_d_gcd c b d H1 H3)
    ]
  | split
    [ apply (trans_divides d (gcd a b) a H).
      apply divides_gcd_n
    | apply (trans_divides d (gcd a b) b H).
      apply divides_gcd_m
    ]
  ]
]
qed.

theorem aDIVIDES_b_TIMES_c_to_GCD_a_b_eq_d_to_aDIVd_DIVIDES_c: \forall a,b,c,d:nat.
a \divides (b*c) \to (gcd a b) = d \to (a/d) \divides c.
intros.
apply (nat_case1 a)
[ intros.
  apply (nat_case1 b)
  [ intros.
    cut (d = O)
    [ rewrite > Hcut.
      simplify.
      apply divides_SO_n
    | rewrite > H2 in H1.
      rewrite > H3 in H1.
      apply sym_eq.
      assumption
    ]
  | intros.
    cut (O \lt d)
    [ rewrite > (S_pred d Hcut).
      simplify.
      rewrite > H2 in H.
      cut (c = O)
      [ rewrite > Hcut1.
        apply (divides_n_n O)
      | apply (lt_times_eq_O b c)
        [ rewrite > H3.
          apply lt_O_S
        | apply (O_div_c_to_c_eq_O (b*c) H)
        ]
      ]
    | rewrite < H1.
      apply lt_O_gcd.
      rewrite > H3.
      apply lt_O_S
    ]
  ]
| intros.
  rewrite < H2.
  elim H.
  cut (d \divides a \land d \divides b)
  [ cut (O \lt a)
    [ cut (O \lt d)
      [ elim Hcut.
        rewrite < (NdivM_times_M_to_N a d) in H3
        [ rewrite < (NdivM_times_M_to_N b d) in H3 
          [ cut (b/d*c = a/d*n2)
            [ apply (gcd_SO_to_divides_times_to_divides (b/d) (a/d) c)
              [ apply (O_lt_times_to_O_lt (a/d) d).
                rewrite > (NdivM_times_M_to_N a d);
                  assumption
              | apply (inj_times_r1 d ? ?)
                [ assumption
                | rewrite < (eq_gcd_times_times_eqv_times_gcd (a/d) (b/d) d).
                  rewrite < (times_n_SO d).
                  rewrite < (sym_times (a/d) d).
                  rewrite < (sym_times (b/d) d).
                  rewrite > (NdivM_times_M_to_N a d)
                  [ rewrite > (NdivM_times_M_to_N b d);
                      assumption                    
                  | assumption
                  | assumption              
                  ]
                ]
              | apply (witness (a/d) ((b/d)*c) n2 Hcut3)
              ]
            | apply (inj_times_r1 d ? ?)
              [ assumption
              | rewrite > sym_times.
                rewrite > (sym_times d ((a/d) * n2)).
                rewrite > assoc_times.
                rewrite > (assoc_times (a/d) n2 d).            
                rewrite > (sym_times c d).
                rewrite > (sym_times n2 d).              
                rewrite < assoc_times.
                rewrite < (assoc_times (a/d) d n2).
                assumption
              ]
            ]
          | assumption
          | assumption
          ]
        | assumption
        | assumption    
        ]
      | rewrite < H1.
        rewrite > sym_gcd.
        apply lt_O_gcd.
        assumption
      ]
    | rewrite > H2.
      apply lt_O_S
    ]
  | rewrite < H1.
    split
    [ apply divides_gcd_n
    | apply divides_gcd_m
    ]
  ]
]
qed.

theorem gcd_sum_times_eq_gcd_aux: \forall a,b,d,m:nat. 
(gcd (a+m*b) b) = d \to (gcd a b) = d.
intros.
apply gcd1
[ rewrite > (minus_plus_m_m a (m*b)).
  apply divides_minus
  [ rewrite < H.
    apply divides_gcd_n
  | rewrite > (times_n_SO d).
    rewrite > (sym_times d ?).
    apply divides_times
    [ apply divides_SO_n
    | rewrite < H.
      apply divides_gcd_m
    ]
  ]
| rewrite < H.
  apply divides_gcd_m
| intros.
  rewrite < H.
  apply divides_d_gcd
  [ assumption
  | apply divides_plus
    [ assumption
    | rewrite > (times_n_SO d1).
      rewrite > (sym_times d1 ?).
      apply divides_times
      [ apply divides_SO_n
      | assumption
      ]
    ]
  ]
]
qed.

theorem gcd_sum_times_eq_gcd: \forall a,b,m:nat. 
(gcd (a+m*b) b) = (gcd a b).
intros.
apply sym_eq.
apply (gcd_sum_times_eq_gcd_aux a b (gcd (a+m*b) b) m).
reflexivity.
qed.

theorem gcd_div_div_eq_div_gcd: \forall a,b,m:nat.
O \lt m \to m \divides a \to m \divides b \to 
(gcd (a/m) (b/m)) = (gcd a b) / m.
intros.
apply (inj_times_r1 m H).
rewrite > (sym_times m ((gcd a b)/m)).
rewrite > (NdivM_times_M_to_N (gcd a b) m)
[ rewrite < eq_gcd_times_times_eqv_times_gcd.
  rewrite > (sym_times m (a/m)).
  rewrite > (sym_times m (b/m)).
  rewrite > (NdivM_times_M_to_N a m H H1).
  rewrite > (NdivM_times_M_to_N b m H H2).
  reflexivity
| assumption
| apply divides_d_gcd;
    assumption
]
qed.


theorem gcdSO_divides_divides_times_divides: \forall c,e,f:nat.
(gcd e f) = (S O)  \to e \divides c \to f \divides c \to 
(e*f) \divides c.
intros.
apply (nat_case1 e)
[ intros.
  apply (nat_case1 c)
  [ intros.
    simplify.
    apply (divides_n_n O).
  | intros.
    rewrite > H3 in H1.
    apply False_ind.
    cut (O \lt O)
    [ apply (le_to_not_lt O O)
      [ apply (le_n O)
      | assumption
      ]
    | apply (divides_to_lt_O O c)
      [ rewrite > H4.
        apply lt_O_S
      | assumption
      ]
    ]
  ]
| intros.
  rewrite < H3.
  elim H1.
  elim H2.
  rewrite > H5.
  rewrite > (sym_times e f).
  apply (divides_times)
  [ apply (divides_n_n)
  | rewrite > H5 in H1.
    apply (gcd_SO_to_divides_times_to_divides f e n)
    [ rewrite > H3.
      apply (lt_O_S m)
    | assumption
    | assumption
    ]
  ]
]
qed.


(* the following theorem shows that gcd is a multiplicative function in 
   the following sense: if a1 and a2 are relatively prime, then 
   gcd(a1·a2, b) = gcd(a1, b)·gcd(a2, b). 
 *)
theorem gcd_aTIMESb_c_eq_gcd_a_c_TIMES_gcd_b_c: \forall a,b,c:nat.
(gcd a b) = (S O) \to (gcd (a*b) c) = (gcd a c) * (gcd b c).
intros.
apply gcd1
[ apply divides_times; 
    apply divides_gcd_n
| apply (gcdSO_divides_divides_times_divides c (gcd a c) (gcd b c))
  [ apply gcd1
    [ apply divides_SO_n  
    | apply divides_SO_n
    | intros.
      cut (d \divides a)
      [ cut (d \divides b)
        [ rewrite < H.
          apply (divides_d_gcd b a d Hcut1 Hcut)
        | apply (trans_divides d (gcd b c) b)
          [ assumption
          | apply (divides_gcd_n)
          ]
        ]
      | apply (trans_divides d (gcd a c) a)
        [ assumption
        | apply (divides_gcd_n)
        ]
      ]
    ]
  | apply (divides_gcd_m)
  | apply (divides_gcd_m)      
  ]
| intros.
  rewrite < (eq_gcd_times_times_eqv_times_gcd b c (gcd a c)).
  rewrite > (sym_times (gcd a c) b).
  rewrite > (sym_times (gcd a c) c).
  rewrite < (eq_gcd_times_times_eqv_times_gcd a c b).
  rewrite < (eq_gcd_times_times_eqv_times_gcd a c c).
  apply (divides_d_gcd)
  [ apply (divides_d_gcd)
    [ rewrite > (times_n_SO d).
      apply (divides_times)
      [ assumption
      | apply divides_SO_n
      ]
    | rewrite > (times_n_SO d).
      apply (divides_times)
      [ assumption
      | apply divides_SO_n
      ]
    ]
  | apply (divides_d_gcd)
    [ rewrite > (times_n_SO d).
      rewrite > (sym_times d (S O)).
      apply (divides_times)
      [ apply (divides_SO_n)
      | assumption
      ]
    | rewrite < (sym_times a b).
      assumption
    ]
  ]
]
qed.
  
  
theorem gcd_eq_gcd_minus: \forall a,b:nat.
a \lt b \to (gcd a b) = (gcd (b - a) b).
intros.
apply sym_eq.
apply gcd1
[ apply (divides_minus (gcd a b) b a)
  [ apply divides_gcd_m
  | apply divides_gcd_n
  ]
| apply divides_gcd_m
| intros.
  elim H1.
  elim H2.
  cut(b = (d*n2) + a) 
  [ cut (b - (d*n2) = a)
    [ rewrite > H4 in Hcut1.
      rewrite < (distr_times_minus d n n2) in Hcut1.
      apply divides_d_gcd
      [ assumption
      | apply (witness d a (n - n2)).
        apply sym_eq.
        assumption
      ]
    | apply (plus_to_minus ? ? ? Hcut)      
    ]
  | rewrite > sym_plus.
    apply (minus_to_plus)
    [ apply lt_to_le.
      assumption
    | assumption
    ]
  ]
]
qed.

