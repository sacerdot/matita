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

include "nat/exp.ma".
include "nat/gcd.ma".
include "nat/permutation.ma".
include "nat/congruence.ma".

theorem permut_S_mod: \forall n:nat. permut (S_mod (S n)) n.
intro.unfold permut.split.intros.
unfold S_mod.
apply le_S_S_to_le.
change with ((S i) \mod (S n) < S n).
apply lt_mod_m_m.
unfold lt.apply le_S_S.apply le_O_n.
unfold injn.intros.
apply inj_S.
rewrite < (lt_to_eq_mod i (S n)).
rewrite < (lt_to_eq_mod j (S n)).
cut (i < n \lor i = n).
cut (j < n \lor j = n).
elim Hcut.
elim Hcut1.
(* i < n, j< n *)
rewrite < mod_S.
rewrite < mod_S.
apply H2.unfold lt.apply le_S_S.apply le_O_n.
rewrite > lt_to_eq_mod.
unfold lt.apply le_S_S.assumption.
unfold lt.apply le_S_S.assumption.
unfold lt.apply le_S_S.apply le_O_n.
rewrite > lt_to_eq_mod.
unfold lt.apply le_S_S.assumption.
unfold lt.apply le_S_S.assumption.
(* i < n, j=n *)
unfold S_mod in H2.
simplify.
apply False_ind.
apply (not_eq_O_S (i \mod (S n))).
apply sym_eq.
rewrite < (mod_n_n (S n)).
rewrite < H4 in \vdash (? ? ? (? %?)).
rewrite < mod_S.assumption.
unfold lt.apply le_S_S.apply le_O_n.
rewrite > lt_to_eq_mod.
unfold lt.apply le_S_S.assumption.
unfold lt.apply le_S_S.assumption.
unfold lt.apply le_S_S.apply le_O_n.
(* i = n, j < n *)
elim Hcut1.
apply False_ind.
apply (not_eq_O_S (j \mod (S n))).
rewrite < (mod_n_n (S n)).
rewrite < H3 in \vdash (? ? (? %?) ?).
rewrite < mod_S.assumption.
unfold lt.apply le_S_S.apply le_O_n.
rewrite > lt_to_eq_mod.
unfold lt.apply le_S_S.assumption.
unfold lt.apply le_S_S.assumption.
unfold lt.apply le_S_S.apply le_O_n.
(* i = n, j= n*)
rewrite > H3.
rewrite > H4.
reflexivity.
apply le_to_or_lt_eq.assumption.
apply le_to_or_lt_eq.assumption.
unfold lt.apply le_S_S.assumption.
unfold lt.apply le_S_S.assumption.
qed.

(*
theorem eq_fact_pi: \forall n,m:nat. n < m \to n! = pi n (S_mod m).
intro.elim n.
simplify.reflexivity.
change with (S n1)*n1!=(S_mod m n1)*(pi n1 (S_mod m)).
unfold S_mod in \vdash (? ? ? (? % ?)). 
rewrite > lt_to_eq_mod.
apply eq_f.apply H.apply (trans_lt ? (S n1)).
simplify. apply le_n.assumption.assumption.
qed.
*)

theorem prime_to_not_divides_fact: \forall p:nat. prime p \to \forall n:nat.
n \lt p \to \not divides p n!.
intros 3.elim n.unfold Not.intros.
apply (lt_to_not_le (S O) p).
unfold prime in H.elim H.
assumption.apply divides_to_le.unfold lt.apply le_n.
assumption.
change with (divides p ((S n1)*n1!) \to False).
intro.
cut (divides p (S n1) \lor divides p n1!).
elim Hcut.apply (lt_to_not_le (S n1) p).
assumption.
apply divides_to_le.unfold lt.apply le_S_S.apply le_O_n.
assumption.apply H1.
apply (trans_lt ? (S n1)).unfold lt. apply le_n.
assumption.assumption.
apply divides_times_to_divides.
assumption.assumption.
qed.

theorem permut_mod: \forall p,a:nat. prime p \to
\lnot divides p a\to permut (\lambda n.(mod (a*n) p)) (pred p).
unfold permut.intros.
split.intros.apply le_S_S_to_le.
apply (trans_le ? p).
change with (mod (a*i) p < p).
apply lt_mod_m_m.
unfold prime in H.elim H.
unfold lt.apply (trans_le ? (S (S O))).
apply le_n_Sn.assumption.
rewrite < S_pred.apply le_n.
unfold prime in H.
elim H.
apply (trans_lt ? (S O)).unfold lt.apply le_n.assumption.
unfold injn.intros.
apply (nat_compare_elim i j).
(* i < j *)
intro.
absurd (j-i \lt p).
unfold lt.
rewrite > (S_pred p).
apply le_S_S.
apply le_plus_to_minus.
apply (trans_le ? (pred p)).assumption.
rewrite > sym_plus.
apply le_plus_n.
unfold prime in H.
elim H.
apply (trans_lt ? (S O)).unfold lt.apply le_n.assumption.
apply (le_to_not_lt p (j-i)).
apply divides_to_le.unfold lt.
apply le_SO_minus.assumption.
cut (divides p a \lor divides p (j-i)).
elim Hcut.apply False_ind.apply H1.assumption.assumption.
apply divides_times_to_divides.assumption.
rewrite > distr_times_minus.
apply eq_mod_to_divides.
unfold prime in H.
elim H.
apply (trans_lt ? (S O)).unfold lt.apply le_n.assumption.
apply sym_eq.
apply H4.
(* i = j *)
intro. assumption.
(* j < i *)
intro.
absurd (i-j \lt p).
unfold lt.
rewrite > (S_pred p).
apply le_S_S.
apply le_plus_to_minus.
apply (trans_le ? (pred p)).assumption.
rewrite > sym_plus.
apply le_plus_n.
unfold prime in H.
elim H.
apply (trans_lt ? (S O)).unfold lt.apply le_n.assumption.
apply (le_to_not_lt p (i-j)).
apply divides_to_le.unfold lt.
apply le_SO_minus.assumption.
cut (divides p a \lor divides p (i-j)).
elim Hcut.apply False_ind.apply H1.assumption.assumption.
apply divides_times_to_divides.assumption.
rewrite > distr_times_minus.
apply eq_mod_to_divides.
unfold prime in H.
elim H.
apply (trans_lt ? (S O)).unfold lt.apply le_n.assumption.
apply H4.
qed.

theorem congruent_exp_pred_SO: \forall p,a:nat. prime p \to \lnot divides p a \to
congruent (exp a (pred p)) (S O) p. 
intros.
cut (O < a)
  [cut (O < p)
    [cut (O < pred p)
      [apply divides_to_congruent
        [assumption
        |change with (O < exp a (pred p)).apply lt_O_exp.assumption
        |cut (divides p (exp a (pred p)-(S O)) \lor divides p (pred p)!)
          [elim Hcut3
            [assumption
            |apply False_ind.
             apply (prime_to_not_divides_fact p H (pred p))
              [unfold lt.rewrite < (S_pred ? Hcut1).apply le_n.
              |assumption
              ]
            ]
          |apply divides_times_to_divides
           [assumption
           |rewrite > times_minus_l.
            rewrite > (sym_times (S O)).
            rewrite < times_n_SO.
            rewrite > (S_pred (pred p) Hcut2).
            rewrite > eq_fact_pi.
            rewrite > exp_pi_l.
            apply congruent_to_divides
              [assumption
              | apply (transitive_congruent p ? 
                        (pi (pred (pred p)) (\lambda m. a*m \mod p) (S O)))
                [ apply (congruent_pi (\lambda m. a*m)).assumption
                |cut (pi (pred(pred p)) (\lambda m.m) (S O)
                       = pi (pred(pred p)) (\lambda m.a*m \mod p) (S O))
                  [rewrite > Hcut3.apply congruent_n_n
                  |rewrite < eq_map_iter_i_pi.
                   rewrite < eq_map_iter_i_pi.
                   apply (permut_to_eq_map_iter_i ? ? ? ? ? (λm.m))
                   [apply assoc_times
                   |apply sym_times
                   |rewrite < plus_n_Sm.
                    rewrite < plus_n_O.
                    rewrite < (S_pred ? Hcut2).
                    apply permut_mod[assumption|assumption]
                   |intros.
                    cut (m=O)
                     [rewrite > Hcut3.
                      rewrite < times_n_O.
                      apply mod_O_n.
                     |apply sym_eq.apply le_n_O_to_eq.apply le_S_S_to_le.assumption
                     ]
                   ]
                 ]
               ]
             ]
           ]
         ]
       ]
     |unfold lt.apply le_S_S_to_le.rewrite < (S_pred ? Hcut1).
      unfold prime in H.elim H.assumption
     ]
   |unfold prime in H.elim H.
    apply (trans_lt ? (S O))[unfold lt.apply le_n|assumption]
   ]
 |cut (O < a \lor O = a)
   [elim Hcut
     [assumption
     |apply False_ind.apply H1.rewrite < H2.apply (witness ? ? O).apply times_n_O
     ]
   |apply le_to_or_lt_eq.apply le_O_n
   ]
 ]
qed.

