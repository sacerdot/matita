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

include "nat/gcd.ma".

(* this file contains some important properites of gcd in N *)

(* an alternative characterization for gcd *)
theorem gcd1: \forall a,b,c:nat.
c \divides a \to c \divides b \to
(\forall d:nat. d \divides a \to d \divides b \to d \divides c) \to (gcd a b) = c.
intros.
elim (H2 ((gcd a b)))
[ apply (antisymmetric_divides (gcd a b) c)
  [ apply (witness (gcd a b) c n1).
    assumption
  | apply divides_d_gcd;
      assumption
  ]
| apply divides_gcd_n
| rewrite > sym_gcd.
  apply divides_gcd_n
]
qed.


theorem eq_gcd_times_times_times_gcd: \forall a,b,c:nat.
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


theorem eq_gcd_div_div_div_gcd: \forall a,b,m:nat.
O \lt m \to m \divides a \to m \divides b \to 
(gcd (a/m) (b/m)) = (gcd a b) / m.
intros.
apply (inj_times_r1 m H).
rewrite > (sym_times m ((gcd a b)/m)).
rewrite > (divides_to_div m (gcd a b))
[ rewrite < eq_gcd_times_times_times_gcd.
  rewrite > (sym_times m (a/m)).
  rewrite > (sym_times m (b/m)).
  rewrite > (divides_to_div m a H1).
  rewrite > (divides_to_div m b H2).
  reflexivity
| apply divides_d_gcd;
    assumption
]
qed.



theorem divides_times_to_divides_div_gcd: \forall a,b,c:nat.
a \divides (b*c) \to (a/(gcd a b)) \divides c.
intros.
apply (nat_case1 a)
[ intros.
  apply (nat_case1 b)
  [ (*It's an impossible situation*)
    intros. 
    simplify.
    apply divides_SO_n
  | intros.    
    cut (c = O)
    [ rewrite > Hcut.
      apply (divides_n_n O)
    | apply (lt_times_eq_O b c)
      [ rewrite > H2.
        apply lt_O_S
      | apply antisymmetric_divides
        [ apply divides_n_O
        | rewrite < H1.
          assumption
        ]
      ]
    ]
  ]
| intros.
  rewrite < H1.
  elim H.
  cut (O \lt a)
  [ cut (O \lt (gcd a b))
    [ apply (gcd_SO_to_divides_times_to_divides (b/(gcd a b)) (a/(gcd a b)) c)
      [ apply (O_lt_times_to_O_lt (a/(gcd a b)) (gcd a b)).
        rewrite > (divides_to_div (gcd a b) a)
        [ assumption      
        | apply divides_gcd_n
        ]
      | rewrite < (div_n_n (gcd a b)) in \vdash (? ? ? %)
        [ apply eq_gcd_div_div_div_gcd
          [ assumption
          | apply divides_gcd_n
          | apply divides_gcd_m
          ]
        | assumption
        ]
      | apply (witness ? ? n1).
        apply (inj_times_r1 (gcd a b) Hcut1).
        rewrite < assoc_times.
        rewrite < sym_times in \vdash (? ? (? % ?) ?).
        rewrite > (divides_to_div (gcd a b) b)
        [ rewrite < assoc_times in \vdash (? ? ? %).
          rewrite < sym_times in \vdash (? ? ? (? % ?)).
          rewrite > (divides_to_div (gcd a b) a)
          [ assumption
          | apply divides_gcd_n
          ]
        | apply divides_gcd_m
        ]
      ]
    | rewrite > sym_gcd.
      apply lt_O_gcd.
      assumption    
    ]
  | rewrite > H1.
    apply lt_O_S
  ]    
]
qed.

theorem gcd_plus_times_gcd: \forall a,b,d,m:nat. 
(gcd (a+m*b) b) = (gcd a b).
intros.
apply gcd1
[ apply divides_plus
  [ apply divides_gcd_n
  | apply (trans_divides ? b ?)
    [ apply divides_gcd_m
    | rewrite > sym_times.
      apply (witness b (b*m) m).
      reflexivity
    ]
  ]
| apply divides_gcd_m
| intros.
  apply divides_d_gcd
  [ assumption
  | rewrite > (minus_plus_m_m a (m*b)). 
    apply divides_minus
    [ assumption
    | apply (trans_divides ? b ?)
      [ assumption
      | rewrite > sym_times.
        apply (witness b (b*m) m).
        reflexivity
      ] 
    ]
  ]
]
qed.



theorem gcd_SO_to_divides_to_divides_to_divides_times: \forall c,e,f:nat.
(gcd e f) = (S O)  \to e \divides c \to f \divides c \to 
(e*f) \divides c.
intros.
apply (nat_case1 c); intros
[ apply divides_n_O 
| rewrite < H3.
  elim H1.
  elim H2.
  rewrite > H5.
  rewrite > (sym_times e f).
  apply (divides_times)
  [ apply (divides_n_n)
  | rewrite > H5 in H1.
    apply (gcd_SO_to_divides_times_to_divides f e n)
    [ rewrite < H5 in H1.
      rewrite > H3 in H1.
      apply (divides_to_lt_O e (S m))
      [ apply lt_O_S
      | assumption
      ]
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
theorem gcd_SO_to_eq_gcd_times_times_gcd_gcd: \forall a,b,c:nat.
(gcd a b) = (S O) \to (gcd (a*b) c) = (gcd a c) * (gcd b c).
intros.
apply gcd1
[ apply divides_times; 
    apply divides_gcd_n
| apply (gcd_SO_to_divides_to_divides_to_divides_times c (gcd a c) (gcd b c))
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
  rewrite < (eq_gcd_times_times_times_gcd b c (gcd a c)).
  rewrite > (sym_times (gcd a c) b).
  rewrite > (sym_times (gcd a c) c).
  rewrite < (eq_gcd_times_times_times_gcd a c b).
  rewrite < (eq_gcd_times_times_times_gcd a c c).
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
  
  
theorem eq_gcd_gcd_minus: \forall a,b:nat.
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
  cut(b = (d*n1) + a) 
  [ cut (b - (d*n1) = a)
    [ rewrite > H4 in Hcut1.
      rewrite < (distr_times_minus d n n1) in Hcut1.
      apply divides_d_gcd
      [ assumption
      | apply (witness d a (n - n1)).
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

