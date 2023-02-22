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

include "Q/q/q.ma".
include "R/r.ma". 

let rec Rexp_nat x n on n ≝
 match n with
 [ O ⇒ R1
 | S p ⇒ x * (Rexp_nat x p) ].
 
axiom daemon : False.

lemma Rexp_nat_tech : ∀a,b,n.O < n → R0 < b → b < a →
  Rexp_nat a n - Rexp_nat b n ≤ n*(a - b)*Rexp_nat a (n-1).
intros;elim H
[simplify;right;autobatch paramodulation
|simplify in ⊢ (? ? (? ? %));rewrite < minus_n_O;
 rewrite > distr_Rtimes_Rplus_l;
 rewrite > sym_Rtimes;
 rewrite > distr_Rtimes_Rplus_l;
 rewrite > sym_Rtimes in ⊢ (? ? (? (? ? %) ?));rewrite < assoc_Rtimes;
 rewrite > R_OF_nat_S;rewrite > sym_Rtimes in ⊢ (? ? (? ? (? ? %)));
 rewrite > distr_Rtimes_Rplus_l;rewrite > Rtimes_x_R1;
 rewrite > sym_Rplus in ⊢ (? ? (? % ?));
 rewrite > assoc_Rplus;simplify;rewrite > sym_Rtimes;
 apply Rle_plus_l;
 do 2 rewrite > distr_Rtimes_Rplus_l;rewrite > Rtimes_x_R1;
 rewrite < Rplus_x_R0;rewrite > sym_Rplus;
 apply Rle_plus_r_to_l;rewrite < assoc_Rplus;
 apply Rle_minus_l_to_r;rewrite > sym_Rplus;rewrite > Rplus_x_R0;
 apply Rle_minus_l_to_r;rewrite < Ropp_Rtimes_r;
 rewrite < Ropp_inv;rewrite < sym_Rplus;rewrite < sym_Rtimes;
 rewrite > Ropp_Rtimes_r;rewrite < distr_Rtimes_Rplus_l;
 apply (trans_Rle ? (b*n1*(a-b)*Rexp_nat a (n1-1)))
 [do 2 rewrite > assoc_Rtimes;apply Rle_times_l
  [rewrite < assoc_Rtimes;assumption|autobatch]
 |rewrite > assoc_Rtimes in ⊢ (??%);rewrite < distr_Rtimes_Rplus_l;
  rewrite < distr_Rtimes_Rplus_r;
  rewrite > sym_Rtimes in ⊢ (? ? (? ? %));rewrite < assoc_Rtimes;
  rewrite > sym_Rtimes;do 2 rewrite < assoc_Rtimes;
  rewrite > (?:(Rexp_nat a n1 = Rexp_nat a (n1-1)*a))
  [do 2 rewrite > assoc_Rtimes;do 2 rewrite > assoc_Rtimes in ⊢ (??%);
   apply Rle_times_l
   [apply Rle_times_r
    [left;assumption
    |elim daemon] (* trivial *)
   |elim daemon] (* trivial: auxiliary lemma *)
  |rewrite > sym_Rtimes;elim H3;simplify
   [reflexivity
   |rewrite < minus_n_O;reflexivity]]]]
qed.

(* FIXME: se uso la notazione, la disambiguazione fa un casino... *) 
(*lemma roots_lemma : ∀x:R.∀n:nat.R0 ≤ x → 1 ≤ n → ∃y.R0 ≤ y ∧ x = Rexp_nat y n.*)

lemma roots_lemma : ∀x:R.∀n:nat.R0 ≤ x → 1 ≤ n → ex ? (λy.R0 ≤ y ∧ x = Rexp_nat y n).
intros;cases H
[alias symbol "lt" = "real numbers less than".
letin bound ≝ (λy:R.R0 < y ∧ Rexp_nat y n < x); 
 elim (R_dedekind bound)
 [cut (R0 < a)
  [|
   (* Hp: ∀y.0<y → y^n<x → y≤a 
      case 0 < x ≤ 1 : take y = x/2
      0 < (x/2)^n < x ⇒ 0 < x/2 ≤ a
      case 1 < x : take y = 1 
      0 < 1^n = 1 < x ⇒ 0 < 1 ≤ a
   unfold in H1;elim H1;unfold in H2;lapply (H1 R1)
   [elim Hletin
    [autobatch
    |rewrite < H3;autobatch]
   |unfold;split
    [autobatch
    |rewrite > Rtimes_x_R1;rewrite < Rplus_x_R0 in ⊢ (? % ?);
     autobatch]] *)
   elim daemon]
 apply ex_intro[apply a]
 split [left;assumption]
 elim H3;unfold in H4;unfold bound in H4;
 cases (trichotomy_Rlt x (Rexp_nat a n)) [|assumption]
 cases H6
 [letin k ≝ ((Rexp_nat a n - x)*Rinv (n*Rexp_nat a (n-1)));
  cut (R0 < k) [|elim daemon]
  cut (k < a) [|elim daemon]
  cut (ub bound (a-k))
  [lapply (H5 ? Hcut3);rewrite < Rplus_x_R0 in Hletin:(?%?);
   rewrite > sym_Rplus in Hletin:(? % ?);lapply (Rle_plus_l_to_r ? ? ? Hletin);
   rewrite > assoc_Rplus in Hletin1;
   rewrite > sym_Rplus in Hletin1:(? ? (? ? %));
   rewrite < assoc_Rplus in Hletin1;
   lapply (Rle_minus_r_to_l ??? Hletin1);
   rewrite > sym_Rplus in Hletin2;rewrite > Rplus_x_R0 in Hletin2;
   rewrite > Rplus_Ropp in Hletin2;cases Hletin2
   [elim (asym_Rlt ?? Hcut1 H8)
   |rewrite > H8 in Hcut1;elim (irrefl_Rlt ? Hcut1)]
  |unfold;intros;elim H8;unfold k;rewrite < Rplus_x_R0;
   rewrite < sym_Rplus;apply Rle_minus_r_to_l;
   apply (pos_z_to_le_Rtimes_Rtimes_to_lt ? ? (n*Rexp_nat a (n-1)))
   [apply pos_times_pos_pos
    [apply (nat_lt_to_R_lt ?? H1);
    |elim daemon]
   |rewrite > Rtimes_x_R0;do 2 rewrite > distr_Rtimes_Rplus_l;
    rewrite > sym_Rtimes in ⊢ (? ? (? (? ? (? ? (? %))) ?));
    rewrite > Ropp_Rtimes_r;
    rewrite < assoc_Rtimes in ⊢ (? ? (? (? ? %) ?));
    rewrite > Rinv_Rtimes_l
    [rewrite > sym_Rtimes in ⊢ (? ? (? (? ? %) ?));
     rewrite > Rtimes_x_R1;rewrite > distr_Ropp_Rplus;
     rewrite < Ropp_inv;rewrite < assoc_Rplus;
     rewrite > assoc_Rplus in ⊢ (? ? (? % ?));
     rewrite > sym_Rplus in ⊢ (? ? (? % ?));
     rewrite > assoc_Rplus;rewrite > sym_Rplus;
     apply Rle_minus_l_to_r;rewrite > distr_Ropp_Rplus;
     rewrite < Ropp_inv;rewrite < sym_Rplus;rewrite > Rplus_x_R0;
     rewrite < distr_Rtimes_Rplus_l;
     apply (trans_Rle ? (Rexp_nat a n - Rexp_nat y n)) 
     [apply Rle_plus_l;left;autobatch
     | cut (∀x,y.(S x ≤ y) = (x < y));[2: intros; reflexivity]
       (* applyS Rexp_nat_tech by sym_Rtimes, assoc_Rtimes;*)
      rewrite > assoc_Rtimes;rewrite > sym_Rtimes in ⊢ (??(??%));
      rewrite < assoc_Rtimes;apply Rexp_nat_tech
      [autobatch
      |assumption
      |(* by transitivity y^n < x < a^n and injectivity *) elim daemon]]
    |intro;apply (irrefl_Rlt (n*Rexp_nat a (n-1)));
     rewrite > H11 in ⊢ (?%?);apply pos_times_pos_pos
     [apply (nat_lt_to_R_lt ?? H1);
     |elim daemon]]]]
|elim (R_archimedean R1 ((x-Rexp_nat a n)/(n*Rexp_nat (a+1) (n-1)))) 
 [|autobatch]
 rewrite > Rtimes_x_R1 in H8;
 letin h ≝ ((x-Rexp_nat a n)/(n*Rexp_nat (a+1) (n-1)*a1));
 lapply (H4 (a+h))
  [rewrite < Rplus_x_R0 in Hletin:(??%);rewrite < sym_Rplus in Hletin:(??%);
   lapply (Rle_plus_r_to_l ? ? ? Hletin);
   rewrite > sym_Rplus in Hletin1:(?(?%?)?);rewrite > assoc_Rplus in Hletin1;
   rewrite > Rplus_Ropp in Hletin1;rewrite > Rplus_x_R0 in Hletin1;
   unfold h in Hletin1;
   cut (R0 < (x-Rexp_nat a n)/(n*Rexp_nat (a+1) (n-1)*a1))
   [cases Hletin1
    [elim (asym_Rlt ? ? Hcut1 H9)
    |rewrite > H9 in Hcut1;elim (irrefl_Rlt ? Hcut1)]
   |apply pos_times_pos_pos
    [apply Rlt_plus_l_to_r;rewrite > sym_Rplus;rewrite > Rplus_x_R0;
     assumption
    |apply lt_R0_Rinv;apply pos_times_pos_pos
     [apply pos_times_pos_pos
      [apply (nat_lt_to_R_lt ?? H1);
      |elim daemon]
     |apply (trans_Rlt ???? H8);apply pos_times_pos_pos
      [apply Rlt_plus_l_to_r;rewrite > sym_Rplus;rewrite > Rplus_x_R0;
       assumption
      |apply lt_R0_Rinv;apply pos_times_pos_pos
       [apply (nat_lt_to_R_lt ?? H1);
       |elim daemon]]]]]
  |split
   [(* show that h > R0, also useful in previous parts of the proof *)
    elim daemon
   |(* by monotonicity ov Rexp_nat *) elim daemon]]]
|apply ex_intro[apply (x/(x+R1))]
 unfold bound;simplify;split
 [apply pos_times_pos_pos
  [assumption
  |apply lt_R0_Rinv;apply pos_plus_pos_pos
   [assumption
   |autobatch]]
 |apply (trans_Rlt ? (x/(x+R1)))
  [(* antimonotone exponential with base in [0,1] *) elim daemon
  |rewrite < Rtimes_x_R1 in ⊢ (??%);
   apply Rlt_times_l
   [rewrite < (Rinv_Rtimes_l R1)
    [rewrite > sym_Rtimes in ⊢ (??%);rewrite > Rtimes_x_R1;
     apply lt_Rinv
     [autobatch
     |rewrite > Rinv_Rtimes_l
      [apply Rlt_minus_l_to_r;rewrite > Rplus_Ropp;assumption
      |intro;elim not_eq_R0_R1;symmetry;assumption]]
    |intro;elim not_eq_R0_R1;symmetry;assumption]
   |assumption]]]
|apply ex_intro[apply (x+R1)]
 unfold ub;intros;unfold in H3;elim H3;cases (trichotomy_Rlt y (x+R1))
 [cases H6
  [left;assumption
  |elim (asym_Rlt (Rexp_nat y n) x)
   [assumption
   |apply (trans_Rlt ? y)
     [apply (trans_Rlt ???? H7);rewrite > sym_Rplus;
      apply Rlt_minus_l_to_r;rewrite > Rplus_Ropp;autobatch
    |(* monotonia; il caso n=1 andra` facilmente gestito a parte *)
     elim daemon]]]
 |right;assumption]]
|apply ex_intro[apply R0]
 split
 [right;reflexivity
 |rewrite < H2;elim H1;
  simplify;rewrite > sym_Rtimes;rewrite > Rtimes_x_R0;reflexivity]]
qed.

definition root : ∀n:nat.∀x:R.O < n → R0 ≤ x → R.
intros;apply (\fst (choose ?? (roots_lemma x n ??)));assumption;
qed.

notation < "hvbox(maction (\root mstyle scriptlevel 1(term 19 n)
         \of (term 19 x)) ((\root n \of x)\sub(h,k)))" 
 with precedence 90 for @{ 'aroot $n $x $h $k}.
 
interpretation "real numbers root" 'aroot n x h k = (root n x h k).

(* FIXME: qui non c'e` modo di far andare la notazione...*)
(*lemma root_sound : ∀n:nat.∀x:R.1 ≤ n → R0 ≤ x → 
                     R0 ≤ (root n x ??) ∧ x = Rexp_nat (root n x ??) n.*)
alias id "PAnd" = "cic:/matita/logic/connectives/And.ind#xpointer(1/1)".

lemma root_sound : ∀n:nat.∀x:R.1 ≤ n → R0 ≤ x → 
                     PAnd (R0 ≤ (root n x ??)) (x = Rexp_nat (root n x ??) n).
try assumption;
intros;unfold root;apply (\snd (choose ?? (roots_lemma x n ??)));
qed.

lemma defactorize_O_nfa_zero : ∀x.defactorize x = 0 → x = nfa_zero.
intro;elim x
[reflexivity
|simplify in H;destruct H
|simplify in H;cut (∀m.defactorize_aux n m ≠ O)
 [elim (Hcut ? H)
 |intro;intro;autobatch]]
qed.   

lemma lt_O_defactorize_numerator : ∀f.0 < defactorize (numerator f).
intro;elim f;simplify
[rewrite < plus_n_O;rewrite > plus_n_O in ⊢ (?%?);apply lt_plus;
 apply lt_O_exp;autobatch
|autobatch
|generalize in match H;generalize in match (not_eq_numerator_nfa_zero f1);
 cases (numerator f1);intros
 [elim H1;reflexivity
 |simplify;cases z;simplify
  [1,3:autobatch
  |rewrite < plus_n_O;rewrite > plus_n_O in ⊢ (?%?);
   apply lt_plus;autobatch depth=2]
 |simplify;cases z;simplify;
  [1,3:autobatch
  |rewrite < plus_n_O;rewrite > (times_n_O O) in ⊢ (?%?);
   apply lt_times
   [rewrite > plus_n_O in ⊢ (?%?); apply lt_plus;autobatch
   |autobatch]]]]
qed.

lemma lt_O_defactorize_denominator : ∀f.O < defactorize (denominator f).
intros;unfold denominator;apply lt_O_defactorize_numerator;
qed.

lemma Rexp_nat_pos : ∀x,n.R0 ≤ x → R0 ≤ Rexp_nat x n.
intros;elim n;simplify
[left;autobatch
|cases H
 [cases H1
  [left;autobatch
  |right;rewrite < H3;rewrite > Rtimes_x_R0;reflexivity]
 |right;rewrite < H2;rewrite > sym_Rtimes;rewrite > Rtimes_x_R0;reflexivity]]
qed.

definition Rexp_Q : ∀x:R.Q → R0 ≤ x → R.
apply (λx,q,p.match q with
 [ OQ ⇒ R1
 | Qpos r ⇒ match r with
  [ one ⇒ x
  | frac f ⇒ root (defactorize (denominator f)) 
                    (Rexp_nat x (defactorize (numerator f))) 
                    (lt_O_defactorize_denominator ?) ? ]
 | Qneg r ⇒ match r with
  [ one ⇒ Rinv x
  | frac f ⇒ Rinv (root (defactorize (denominator f)) 
                    (Rexp_nat x (defactorize (numerator f)))
                    (lt_O_defactorize_denominator ?) ?) ]]);
autobatch;
qed.

lemma Rexp_nat_plus_Rtimes : 
  ∀x,p,q.Rexp_nat x (p+q) = Rexp_nat x p * Rexp_nat x q.
intros;elim q
[simplify;autobatch paramodulation
|rewrite < sym_plus;simplify;autobatch paramodulation]
qed.

lemma monotonic_Rexp_nat : ∀x,y,n.O < n → R0 ≤ x → x < y → 
                                  Rexp_nat x n < Rexp_nat y n.
intros;elim H;simplify
[do 2 rewrite > Rtimes_x_R1;assumption 
|apply (trans_Rlt ? (y*Rexp_nat x n1))
 [rewrite > sym_Rtimes;rewrite > sym_Rtimes in ⊢ (??%);
  apply Rlt_times_l
  [assumption
  |(* already proved, but for ≤: shit! *)elim daemon]
 |apply Rlt_times_l
  [assumption
  |cases H1
   [autobatch
   |rewrite > H5;assumption]]]]
qed.

lemma inj_Rexp_nat_l : ∀x,y,n.O < n → R0 ≤ x → R0 ≤ y →
                         Rexp_nat x n = Rexp_nat y n → x = y.
intros;cases (trichotomy_Rlt x y)
[cases H4
 [lapply (monotonic_Rexp_nat ?? n H H1 H5);
  elim (Rlt_to_neq ?? Hletin H3)
 |lapply (monotonic_Rexp_nat ?? n H H2 H5);
  elim (Rlt_to_neq ?? Hletin);symmetry;assumption]
|assumption]
qed.

lemma root_unique : ∀x,y,n.R0 ≤ x → R0 ≤ y → O < n → 
                      Rexp_nat y n = x → y = root n x ? ?.
[1,2:assumption
|intros;cases (root_sound n x)
 [2,3:assumption
 |rewrite > H5 in H3;lapply (inj_Rexp_nat_l ?????? H3);assumption]]
qed.

lemma Rtimes_Rexp_nat : ∀x,y:R.∀p.Rexp_nat x p*Rexp_nat y p = Rexp_nat (x*y) p.
intros;elim p;simplify
[autobatch paramodulation
|rewrite > assoc_Rtimes;rewrite < assoc_Rtimes in ⊢ (? ? (? ? %) ?);
 rewrite < sym_Rtimes in ⊢ (? ? (? ? (? % ?)) ?);
 rewrite < H;do 3 rewrite < assoc_Rtimes;reflexivity]
qed.

lemma times_root : ∀x,y,n,H,H1,H2,H3.
  root n x H H2 * root n y H H3 = root n (x*y) H H1.
intros;lapply (Rtimes_Rexp_nat (root n x H H2) (root n y H H3) n);
lapply (sym_eq ??? Hletin);
cases (root_sound n x)
[2,3:assumption
|cases (root_sound n y)
 [2,3:assumption
 |rewrite < H5 in Hletin1;rewrite < H7 in Hletin1;
  lapply (root_unique ?????? Hletin1)
  [assumption
  |cases H4
   [cases H6
    [left;autobatch
    |right;autobatch paramodulation]
   |right;autobatch paramodulation]
  |*:assumption]]]
qed.

lemma Rexp_nat_Rexp_nat_Rtimes : 
  ∀x,p,q.Rexp_nat (Rexp_nat x p) q = Rexp_nat x (p*q).
intros;elim q
[rewrite < times_n_O;simplify;reflexivity
|rewrite < times_n_Sm;rewrite > Rexp_nat_plus_Rtimes;simplify;
 rewrite < H;reflexivity]
qed. 

lemma root_root_times : ∀x,n,m,H,H1,H2.root m (root n x H H1) H2 ? =
                          root (m*n) x ? H1.
[cases (root_sound n x H H1);assumption
| change in match O with (O*O); apply lt_times; assumption; 
  (* autobatch paramodulation; non fa narrowing, non fa deep subsumption... *) 
|intros;lapply (Rexp_nat_Rexp_nat_Rtimes (root m (root n x H H1) H2 ?) m n)
 [cases (root_sound n x H H1);assumption
 |cases (root_sound m (root n x H H1))
  [2:assumption
  |3:cases (root_sound n x H H1);assumption
  |rewrite < H4 in Hletin:(??%?);lapply (root_sound n x H H1);
   cases Hletin1;rewrite < H6 in Hletin:(??%?);
   apply root_unique
   [apply H3
   |symmetry;apply Hletin]]]]
qed.