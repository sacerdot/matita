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

set "baseuri" "cic:/matita/Z/moebius".

include "nat/factorization.ma".
include "Z/sigma_p.ma".
  
let rec moebius_aux p n : Z \def
  match p with 
  [ O \Rightarrow pos O
  | (S p1) \Rightarrow 
    match p_ord n (nth_prime p1) with
    [ (pair q r) \Rightarrow
      match q with
      [ O \Rightarrow moebius_aux p1 r
      | (S q1) \Rightarrow
	      match q1 with 
	      [ O \Rightarrow Zopp (moebius_aux p1 r) 
        | (S q2) \Rightarrow OZ
        ]
      ]
    ]
  ]
.

definition moebius : nat \to Z \def
\lambda n.
  let p \def (max n (\lambda p:nat.eqb (n \mod (nth_prime p)) O)) in
  moebius_aux (S p) n.

theorem moebius_O : moebius O = pos O.
simplify. reflexivity.
qed.
      
theorem moebius_SO : moebius (S O) = pos O.
simplify.reflexivity.
qed.  

theorem moebius_SSO : moebius (S (S O)) = neg O.
simplify.reflexivity.
qed.  

theorem moebius_SSSO : moebius (S (S (S O))) = neg O.
simplify.reflexivity.
qed.


theorem not_divides_to_p_ord_O: \forall n,i.
Not (divides (nth_prime i) n) \to p_ord n (nth_prime i) = 
pair nat nat O n.
intros.
apply p_ord_exp1
  [apply lt_O_nth_prime_n
  |assumption
  |autobatch
  ]
qed.

theorem p_ord_O_to_not_divides: \forall n,i,r.
O < n \to
p_ord n (nth_prime i) = pair nat nat O r 
\to Not (divides (nth_prime i) n).
intros.
lapply (p_ord_to_exp1 ? ? ? ? ? ? H1)
  [apply lt_SO_nth_prime_n
  |assumption
  |elim Hletin.
   simplify in H3.
   rewrite > H3.
   rewrite < plus_n_O.
   assumption
  ]
qed.

theorem not_divides_to_eq_moebius_aux: \forall n,p,p1.p \le p1 \to
(\forall i. p \le i \to i \le p1 \to Not (divides (nth_prime i) n))
\to moebius_aux p n = moebius_aux p1 n.
intros 4.
elim H
  [reflexivity
  |simplify.
   rewrite > not_divides_to_p_ord_O
    [simplify.apply H2.intros.
     apply H3[assumption|apply le_S.assumption]
    |apply H3[assumption|apply le_n_Sn]
    ]
  ]
qed.

theorem eq_moebius_moebius_aux: \forall n,p. 
max_prime_factor n < p \to p \le n \to
moebius n = moebius_aux p n.
intros.
unfold moebius.
change with 
(moebius_aux (S (max n (\lambda p:nat.eqb (n\mod nth_prime p) O))) n
= moebius_aux p n).
apply not_divides_to_eq_moebius_aux
  [assumption
  |intros.
   apply divides_b_false_to_not_divides.
   unfold divides_b.
   apply (lt_max_to_false ? n i)
    [assumption
    |apply (trans_le ? p)[assumption|assumption]
    ]
  ]
qed.

theorem moebius_aux_SO: \forall p.moebius_aux p (S O) = pos O.
intros.
elim p
  [simplify.reflexivity
  |rewrite < H.
   apply sym_eq.
   apply not_divides_to_eq_moebius_aux
   [apply le_n_Sn
   |intros.unfold.intro.
    absurd (nth_prime i \le S O)
      [apply divides_to_le
        [apply le_n|assumption]
      |apply lt_to_not_le.
       apply lt_SO_nth_prime_n.
      ]
    ]
  ]
qed.

theorem p_ord_to_not_eq_O : \forall n,p,q,r.
  (S O) < n \to
  p_ord n (nth_prime p) = pair nat nat q r \to
  Not (r=O).
intros.
unfold.intro.
cut (O < n)
  [lapply (p_ord_to_exp1 ? ? ? ? ? ? H1)
    [apply lt_SO_nth_prime_n.
    |assumption
    |elim Hletin.
     apply (lt_to_not_eq ? ? Hcut).
     rewrite > H4.
     rewrite > H2.
     apply times_n_O
    ]
  |apply (trans_lt ? (S O))[apply lt_O_S|assumption]
  ]
qed.

theorem max_prime_factor_to_not_p_ord_O : \forall n,p,r.
  (S O) < n \to
  p = max_prime_factor n \to
  p_ord n (nth_prime p) \neq pair nat nat O r.
intros.unfold Not.intro.
apply (p_ord_O_to_not_divides ? ? ? ? H2)
  [apply (trans_lt ? (S O))[apply lt_O_S|assumption]
  |rewrite > H1.
   apply divides_max_prime_factor_n.
   assumption
  ]
qed.

theorem p_ord_SO_SO_to_moebius : \forall n,p.
  (S O) < n \to
  p = max_prime_factor n \to
  p_ord n (nth_prime p) = pair nat nat (S O) (S O) \to
  moebius n = Zopp (pos O).
intros.
change with 
  (moebius_aux (S (max_prime_factor n)) n = neg O).
rewrite < H1.simplify.
rewrite > H2.simplify.
rewrite > moebius_aux_SO.
reflexivity.
qed.

theorem p_ord_SO_r_to_moebius1 : \forall n,p,r.
  (S O) < n \to 
  p = max_prime_factor n \to
  (S O) < r \to 
  p_ord n (nth_prime p) = pair nat nat (S O) r \to
  moebius n = Zopp (moebius r).
intros.
change with 
  (moebius_aux (S (max_prime_factor n)) n = -(moebius r)).
rewrite < H1.simplify.
rewrite > H3.simplify.
apply eq_f.
apply sym_eq.
change with 
 (moebius_aux (S (max_prime_factor r)) r = moebius_aux p r).
apply not_divides_to_eq_moebius_aux
  [apply (p_ord_to_lt_max_prime_factor n p (S O) ? ? H1)
    [apply (trans_lt ? (S O))[apply lt_O_S|assumption]
    |apply sym_eq. assumption
    |assumption
    ]
  |intros.
   lapply (decidable_le i r).
   elim Hletin
    [apply divides_b_false_to_not_divides.
     apply (lt_max_to_false ? r i)[assumption|assumption]
    |unfold.intro.apply H6.
     apply (trans_le ? (nth_prime i))
      [apply lt_to_le.
       apply lt_n_nth_prime_n
      |apply divides_to_le
        [apply (trans_lt ? (S O))[apply lt_O_S|assumption]
        |assumption
        ]
      ]
    ]
  ]
qed.

theorem p_ord_SO_r_to_moebius : \forall n,p,r.
  (S O) < n \to 
  p = max_prime_factor n \to
  p_ord n (nth_prime p) = pair nat nat (S O) r \to
  moebius n = Zopp (moebius r).
intros 5.
apply (nat_case r);intro
  [apply False_ind.
   apply (p_ord_to_not_eq_O ? ? ? ? H H2).
   reflexivity
  |apply (nat_case m);intros
    [simplify.apply (p_ord_SO_SO_to_moebius ? ? H H1 H2)
    |apply (p_ord_SO_r_to_moebius1 ? ? ? H H1 ? H2).
     apply le_S_S.apply le_S_S.apply le_O_n
    ]
  ]
qed.    

theorem p_ord_SSq_r_to_moebius : \forall n,p,q,r.
  (S O) < n \to
  p = max_prime_factor n \to
  p_ord n (nth_prime p) = pair nat nat (S (S q)) r \to
  moebius n = OZ.
intros.
change with
  (moebius_aux (S (max n (\lambda p:nat.eqb (n\mod nth_prime p) O))) n =OZ).
rewrite < H1.simplify.
rewrite > H2.simplify.
reflexivity.
qed.

lemma eq_p_max: \forall n,p,r:nat. O < n \to
O < r \to
r = (S O) \lor (max r (\lambda p:nat.eqb (r \mod (nth_prime p)) O)) < p \to
p = max_prime_factor (r*(nth_prime p)\sup n).
intros.
apply sym_eq.
unfold max_prime_factor.
apply max_spec_to_max.
split
  [split
    [rewrite > times_n_SO in \vdash (? % ?).
     rewrite > sym_times.
     apply le_times
      [assumption
      |apply lt_to_le.
       apply (lt_to_le_to_lt ? (nth_prime p))
        [apply lt_n_nth_prime_n
        |rewrite > exp_n_SO in \vdash (? % ?).
         apply le_exp
          [apply lt_O_nth_prime_n
          |assumption
          ]
        ]
      ]
    |apply eq_to_eqb_true.
     apply divides_to_mod_O
      [apply lt_O_nth_prime_n
      |apply (lt_O_n_elim ? H).
       intro.
       apply (witness ? ? (r*(nth_prime p \sup m))).
       rewrite < assoc_times.
       rewrite < sym_times in \vdash (? ? ? (? % ?)).
       rewrite > exp_n_SO in \vdash (? ? ? (? (? ? %) ?)).
       rewrite > assoc_times.
       rewrite < exp_plus_times.
       reflexivity
      ]
    ]
  |intros.  
   apply not_eq_to_eqb_false.
   unfold Not.intro.
   lapply (mod_O_to_divides ? ? ? H5)
    [apply lt_O_nth_prime_n
    |cut (Not (divides (nth_prime i) ((nth_prime p)\sup n)))
      [elim H2
        [rewrite > H6 in Hletin.
         simplify in Hletin.
         rewrite < plus_n_O in Hletin.
         apply Hcut.assumption
        |elim (divides_times_to_divides ? ? ? ? Hletin)
          [apply (lt_to_not_le ? ? H3).
           apply lt_to_le. 
           apply (le_to_lt_to_lt ? ? ? ? H6).
           apply f_m_to_le_max
            [apply (trans_le ? (nth_prime i))
              [apply lt_to_le.
               apply lt_n_nth_prime_n
              |apply divides_to_le[assumption|assumption]
              ]
            |apply eq_to_eqb_true.
             apply divides_to_mod_O
              [apply lt_O_nth_prime_n|assumption]
            ]
          |apply prime_nth_prime
          |apply Hcut.assumption
          ]
        ]
      |unfold Not.intro.
       apply (lt_to_not_eq ? ? H3).
       apply sym_eq.
       elim (prime_nth_prime p).
       apply injective_nth_prime.
       apply H8
        [apply (divides_exp_to_divides ? ? ? ? H6).
         apply prime_nth_prime.
        |apply lt_SO_nth_prime_n
        ]
      ]
    ]
  ]
qed.

lemma lt_max_prime_factor_to_not_divides: \forall n,p:nat.
O < n \to n=S O \lor max_prime_factor n < p \to 
(nth_prime p \ndivides n).
intros.unfold Not.intro.
elim H1
  [rewrite > H3 in H2.
   apply (le_to_not_lt (nth_prime p) (S O))
    [apply divides_to_le[apply le_n|assumption]
    |apply lt_SO_nth_prime_n
    ]
  |apply (not_le_Sn_n p).
   change with (p < p).
   apply (le_to_lt_to_lt ? ? ? ? H3).
   unfold max_prime_factor.
   apply  f_m_to_le_max
    [apply (trans_le ? (nth_prime p))
      [apply lt_to_le.
       apply lt_n_nth_prime_n
      |apply divides_to_le;assumption
      ]
    |apply eq_to_eqb_true.
     apply divides_to_mod_O
      [apply lt_O_nth_prime_n|assumption]
    ]
  ]
qed.

theorem moebius_exp: \forall p,q,r:nat. O < r \to
r = (S O) \lor (max_prime_factor r) < p \to
(* r = (S O) \lor (max r (\lambda p:nat.eqb (r \mod (nth_prime p)) O)) < p \to *)
sigma_p (S (S q)) (\lambda y.true) (\lambda y.moebius (r*(exp (nth_prime p) y))) = O.
intros.
elim q
  [rewrite > true_to_sigma_p_Sn
    [rewrite > true_to_sigma_p_Sn
      [rewrite > Zplus_z_OZ.
       rewrite < times_n_SO.
       rewrite > (p_ord_SO_r_to_moebius ? p r)
        [rewrite > sym_Zplus.
         rewrite > Zplus_Zopp.
         reflexivity
        |rewrite < exp_n_SO.
         rewrite > sym_times.
         rewrite > times_n_SO.
         apply lt_to_le_to_lt_times
          [apply lt_SO_nth_prime_n
          |assumption
          |assumption
          ]
        |apply eq_p_max
          [apply le_n|assumption|assumption]
        |apply p_ord_exp1
          [apply lt_O_nth_prime_n
          |apply lt_max_prime_factor_to_not_divides;assumption
          |apply sym_times
          ]
        ]
      |reflexivity
      ]
    |reflexivity
    ]
  |rewrite > true_to_sigma_p_Sn
    [rewrite > H2.
     rewrite > Zplus_z_OZ.
     apply (p_ord_SSq_r_to_moebius ? p n r)
      [rewrite > times_n_SO.
       rewrite > sym_times in \vdash (? ? %).
       apply lt_to_le_to_lt_times
        [apply (trans_lt ? (nth_prime p))
          [apply lt_SO_nth_prime_n
            |rewrite > exp_n_SO in \vdash (? % ?).
             apply lt_exp
              [apply lt_SO_nth_prime_n
              |apply le_S_S.apply le_S_S.apply le_O_n
              ]
            ]
          |assumption
          |assumption
          ]
        |apply eq_p_max
          [apply le_S_S.apply le_O_n|assumption|assumption]  
        |apply p_ord_exp1
          [apply lt_O_nth_prime_n
          |apply lt_max_prime_factor_to_not_divides;assumption        
          |apply sym_times
          ]
        ]
      |reflexivity
      ]
    ]   
qed.
  
theorem sigma_p_moebius1: \forall n,m,p:nat.O < n \to O < m \to 
n = (S O) \lor max_prime_factor n < p \to
sigma_p (S (n*(exp (nth_prime p) m))) (\lambda y.divides_b y (n*(exp (nth_prime p) m))) moebius = O.
intros.
rewrite > sigma_p_divides_b
  [apply (trans_eq ? ? (sigma_p (S n) (\lambda x:nat.divides_b x n) (\lambda x:nat.OZ)))
    [apply eq_sigma_p1
      [intros.reflexivity
      |apply (lt_O_n_elim m H1).
       intros.apply moebius_exp
        [apply (divides_b_true_to_lt_O ? ? ? H4).
         assumption
        |elim H2
          [left.rewrite > H5 in H3.
           elim (le_to_or_lt_eq ? ? (le_S_S_to_le ? ? H3))
            [apply False_ind.
             apply (lt_to_not_le O x)
              [apply (divides_b_true_to_lt_O n x H H4)
              |apply le_S_S_to_le.assumption
              ]
            |assumption
            ]
          |right.
           apply (le_to_lt_to_lt ? ? ? ? H5).
           apply (divides_to_max_prime_factor1 x n)
            [apply (divides_b_true_to_lt_O ? ? H H4)
            |assumption
            |apply divides_b_true_to_divides.
             assumption
            ]
          ]
        ]
      ]
    |generalize in match (\lambda x:nat.divides_b x n).
     intro.
     elim n
      [simplify.elim (f O);reflexivity
      |apply (bool_elim ? (f (S n1)))
        [intro.
         rewrite > true_to_sigma_p_Sn
          [rewrite > H3.reflexivity|assumption]
        |intro.
         rewrite > false_to_sigma_p_Sn
          [apply H3|assumption]
        ]
      ]
    ]
  |assumption
  |apply prime_nth_prime
  |apply lt_max_prime_factor_to_not_divides;assumption
  ]
qed.

theorem sigma_p_moebius: \forall n. (S O) < n \to
sigma_p (S n) (\lambda y.divides_b y n) moebius = O.
intros.
lapply (exp_ord (nth_prime (max_prime_factor n)) n)
  [rewrite > sym_times in Hletin.
   rewrite > Hletin.
   apply sigma_p_moebius1
    [apply lt_O_ord_rem
      [apply lt_SO_nth_prime_n
      |apply lt_to_le.assumption
      ]
    |unfold lt.
     change with
      (fst ? ? (pair ? ? (S O) (S O)) \leq ord n (nth_prime (max_prime_factor n))).
     rewrite < (p_ord_p (nth_prime (max_prime_factor n)))
      [apply (divides_to_le_ord ? (nth_prime (max_prime_factor n)) n)
        [apply lt_O_nth_prime_n
        |apply lt_to_le.assumption
        |apply prime_nth_prime
        |apply divides_max_prime_factor_n.
         assumption
        ]
      |apply lt_SO_nth_prime_n
      ]
    |lapply (lt_O_ord_rem (nth_prime (max_prime_factor n)) n)
      [elim (le_to_or_lt_eq ? ? Hletin1)
        [right.
         apply (p_ord_to_lt_max_prime_factor1 n (max_prime_factor n) 
          (ord n (nth_prime (max_prime_factor n)))
          (ord_rem n (nth_prime (max_prime_factor n))))
          [apply lt_to_le.assumption
          |apply le_n
          |autobatch
          |assumption
          ]
        |left.apply sym_eq.assumption
        ]
      |apply lt_SO_nth_prime_n
      |apply lt_to_le.assumption
      ]
    ]
  |apply lt_SO_nth_prime_n
  |apply lt_to_le.assumption
  ]
qed.



