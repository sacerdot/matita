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

include "R/root.ma".
include "nat/orders.ma".
include "Z/times.ma".

definition Rexp_Z ≝
λx:R.λy:Z.match y with
[ pos z ⇒ Rexp_nat x (S z)
| neg z ⇒ Rinv (Rexp_nat x (S z))
| OZ ⇒ R1 ].

lemma eq_Rexp_nat_Rexp_Z : ∀x.∀n:nat.Rexp_nat x n = Rexp_Z x n.
intros;cases n;simplify;reflexivity;
qed.

definition expcut : ∀x,y,z:R.Prop ≝ 
  λx,y,z:R.∃p:Z.∃q:nat.∃H1,H2.
    z = root q (Rexp_Z x p) H1 H2 ∧ p ≤ (y*q).
    
axiom Zopp_to_Ropp : ∀z. R_of_Z (Zopp z) = Ropp (R_of_Z z).
axiom distr_Rinv_Rtimes : ∀x,y.x ≠ R0 → y ≠ R0 → Rinv (x*y) = Rinv x * Rinv y.
axiom Rinv_Rexp_nat : ∀n,z. z ≠ R0 → Rinv (Rexp_nat z n) = Rexp_nat (Rinv z) n.

lemma Rexp_nat_R0 : ∀x,n.Rexp_nat x n = R0 → x = R0.
intros 2;elim n
[simplify in H;elim not_eq_R0_R1;symmetry;assumption
|simplify in H1;
 cases (trichotomy_Rlt x R0)
 [apply H;simplify in H1;cases H2;lapply (Rlt_to_neq ? ? H3);
  rewrite < (Rtimes_x_R0 (Rinv x));
  rewrite > sym_Rtimes in ⊢ (???%);apply eq_Rtimes_l_to_r
  [assumption
  |2,4:rewrite > sym_Rtimes;assumption
  |intro;apply Hletin;symmetry;assumption]
 |assumption]]
qed.

lemma Rexp_Z_Rexp_Z_Rtimes :
 ∀x,y,z.x ≠ R0 → Rexp_Z (Rexp_Z x y) z = Rexp_Z x (y*z).
intros;cases y
[simplify;cases z
 [reflexivity
 |simplify;rewrite > sym_Rtimes;rewrite > Rtimes_x_R1;
  elim n
  [reflexivity
  |simplify;rewrite > sym_Rtimes;rewrite > Rtimes_x_R1;assumption]
 |simplify;rewrite > sym_Rtimes;rewrite > Rtimes_x_R1;
  elim n;simplify
  [rewrite < Rtimes_x_R1;rewrite < sym_Rtimes;
   apply Rinv_Rtimes_l;intro;autobatch
  |rewrite > sym_Rtimes;rewrite > Rtimes_x_R1;assumption]]
|cases z
 [reflexivity
 |simplify;change in ⊢ (? ? (? ? (? % ?)) ?) with (Rexp_nat x (S n));
  rewrite > Rexp_nat_Rexp_nat_Rtimes;
  rewrite > assoc_Rtimes;rewrite < Rexp_nat_plus_Rtimes;do 2 apply eq_f;
  rewrite > sym_times in ⊢ (???%); simplify;
  do 2 rewrite < assoc_plus;rewrite < sym_plus in ⊢ (? ? (? % ?) ?);
  rewrite < sym_times;reflexivity
 |simplify;apply eq_f;change in ⊢ (? ? (? ? (? % ?)) ?) with (Rexp_nat x (S n));
  rewrite > Rexp_nat_Rexp_nat_Rtimes;
  rewrite > assoc_Rtimes;rewrite < Rexp_nat_plus_Rtimes;
  do 2 apply eq_f;rewrite > sym_times in ⊢ (???%); simplify;
  do 2 rewrite < assoc_plus;rewrite < sym_plus in ⊢ (? ? (? % ?) ?);
  rewrite < sym_times;reflexivity]
|cases z
 [reflexivity
 |simplify;change in ⊢ (? ? (? (? %) (? (? %) ?)) ?) with (Rexp_nat x (S n));
  rewrite < Rinv_Rexp_nat
  [rewrite < distr_Rinv_Rtimes
   [apply eq_f;rewrite > Rexp_nat_Rexp_nat_Rtimes;
    rewrite < Rexp_nat_plus_Rtimes;
    change in ⊢ (? ? ? %) with (Rexp_nat x (S (n1+n*S n1)));
    apply eq_f;autobatch paramodulation
   |intro;apply H;apply (Rexp_nat_R0 ?? H1)
   |intro;apply H;lapply (Rexp_nat_R0 ?? H1);apply (Rexp_nat_R0 ?? Hletin)]
  |intro;apply H;apply (Rexp_nat_R0 ?? H1)]
 |simplify;rewrite < Rinv_Rexp_nat
  [rewrite < distr_Rinv_Rtimes
   [rewrite < Rinv_inv
    [change in ⊢ (? ? (? ? (? % ?)) ?) with (Rexp_nat x (S n));
     rewrite > Rexp_nat_Rexp_nat_Rtimes;
     rewrite > assoc_Rtimes;rewrite < Rexp_nat_plus_Rtimes;
     apply eq_f;apply eq_f;rewrite > sym_times in ⊢ (???%); simplify;
     do 2 rewrite < assoc_plus;rewrite < sym_plus in ⊢ (? ? (? % ?) ?);
     rewrite < sym_times;reflexivity
    |intro;apply H;
     change in H1:(??%?) with (Rexp_nat (x*Rexp_nat x n) (S n1));
     lapply (Rexp_nat_R0 ?? H1);
     change in Hletin:(??%?) with (Rexp_nat x (S n));
     apply (Rexp_nat_R0 ?? Hletin)]
   |intro;apply H;change in H1:(??%?) with (Rexp_nat x (S n));
    apply (Rexp_nat_R0 ?? H1)
   |intro;apply H;
    lapply (Rexp_nat_R0 ?? H1);
    change in Hletin:(??%?) with (Rexp_nat x (S n));
    apply (Rexp_nat_R0 ?? Hletin)]
  |intro;apply H;change in H1:(??%?) with (Rexp_nat x (S n));
   apply (Rexp_nat_R0 ?? H1)]]]
qed.

lemma pos_Rexp_nat : ∀x,n.R0 < x → R0 < Rexp_nat x n.
intros;elim n;simplify
[autobatch
|rewrite < (Rtimes_x_R0 x);apply Rlt_times_l;assumption]
qed.

lemma Rexp_nat_R0_Sn : ∀n.Rexp_nat R0 (S n) = R0.
intro;simplify;rewrite > sym_Rtimes;rewrite > Rtimes_x_R0;reflexivity;
qed.

lemma lt_to_lt_Rexp_nat : ∀x,y,n.R0 ≤ x → R0 ≤ y → O < n → x < y →
  Rexp_nat x n < Rexp_nat y n.
intros;cases H
[cases H1
 [elim H2;simplify
  [do 2 rewrite > Rtimes_x_R1;assumption
  |apply (trans_Rlt ? (y*Rexp_nat x n1))
   [rewrite > sym_Rtimes;rewrite > sym_Rtimes in ⊢ (??%);
    apply Rlt_times_l
    [assumption
    |apply pos_Rexp_nat;assumption]
   |apply Rlt_times_l;autobatch]]
 |rewrite < H5 in H3;elim (irrefl_Rlt R0);apply (trans_Rlt ? x);assumption]
|cases H1
 [rewrite < H4;cases H2;rewrite > Rexp_nat_R0_Sn
  [simplify;rewrite > Rtimes_x_R1;assumption
  |apply pos_Rexp_nat;assumption]
 |elim (irrefl_Rlt x);rewrite < H4 in ⊢ (??%);rewrite > H5;assumption]]
qed. 

lemma le_to_le_Rexp_nat : ∀x,y,n.R0 ≤ x → R0 ≤ y → x ≤ y →
  Rexp_nat x n ≤ Rexp_nat y n.
intros;elim n
[right;reflexivity
|cases H
 [cases H1
  [cases H2
   [left;apply lt_to_lt_Rexp_nat;autobatch
   |rewrite > H6;right;reflexivity]
  |rewrite < H5 in H2;elim (irrefl_Rlt R0);cases H2
   [apply (trans_Rlt ? x);assumption
   |rewrite < H6 in ⊢ (??%);assumption]]
 |rewrite < H4;rewrite > Rexp_nat_R0_Sn;cases H1
  [left;apply pos_Rexp_nat;assumption
  |rewrite < H5;rewrite > Rexp_nat_R0_Sn;right;reflexivity]]]
qed.

lemma inj_Rexp_nat : ∀x,y,n.R0 ≤ x → R0 ≤ y → O < n → 
  Rexp_nat x n = Rexp_nat y n → x = y.
intros;cases (trichotomy_Rlt x y)
[cases H4
 [lapply (lt_to_lt_Rexp_nat ??? H H1 H2 H5);rewrite > H3 in Hletin;
  elim (irrefl_Rlt ? Hletin)
 |lapply (lt_to_lt_Rexp_nat ??? H1 H H2 H5);rewrite > H3 in Hletin;
  elim (irrefl_Rlt ? Hletin)]
|assumption]
qed.

axiom eq_Rinv_Ropp_Ropp_Rinv : ∀x. x ≠ R0 → Rinv (Ropp x) = Ropp (Rinv x).
lemma Rlt_times_r : ∀x,y,z:R.x < y → R0 < z → x*z < y*z.
intros;rewrite < sym_Rtimes;rewrite < sym_Rtimes in ⊢ (??%);
autobatch;
qed.

lemma Rexp_nat_R1 : ∀x.Rexp_nat x 1 = x.
intros;simplify;rewrite > Rtimes_x_R1;reflexivity;
qed. 

alias symbol "lt" = "real numbers less than".
lemma Rexp_lemma : ∀x,y:R. R1 < x → ∃z.lub (expcut x y) z.
intros;apply R_dedekind
[unfold expcut;cases (trichotomy_Rlt y R0)
 [cases H1
  [cases (R_archimedean R1 (Ropp y))
   [apply ex_intro[apply (Rexp_Z x (Zopp x1))]
    apply ex_intro[apply (Zopp x1)]
    apply ex_intro[apply 1]
    apply ex_intro[apply le_n]
    apply ex_intro
    [left;cases x1;simplify
     [autobatch
     |apply lt_R0_Rinv;change in ⊢(??%) with (Rexp_nat x (S n));
      apply pos_Rexp_nat;autobatch]
    |split
     [cases (root_sound 1 (Rexp_Z x (-x1)))
      [rewrite > Rexp_nat_R1 in H5;apply H5
      |*:skip]
     |simplify;left;rewrite > Rtimes_x_R1;rewrite > Ropp_inv in ⊢ (??%);
      lapply (Rlt_to_Rlt_Ropp_Ropp ?? H3);rewrite > Rtimes_x_R1 in Hletin;
      rewrite > Zopp_to_Ropp;apply Hletin]]
   |autobatch]
  |cases (R_archimedean y R1)
   [cut (O < x1) [|elim daemon]
    cut (R0 ≤ x) [|left;apply (trans_Rlt ???? H);autobatch] 
    apply ex_intro[apply (root x1 x Hcut Hcut1);assumption]
    apply ex_intro[apply (Z_of_nat 1)]
    apply ex_intro[apply x1]
    apply ex_intro[assumption]
    apply ex_intro
    [simplify;rewrite > Rtimes_x_R1;assumption
    |simplify in ⊢ (? (? ? ? (? ? % ? ?)) ?);
     split
     [symmetry;cases (root_sound x1 (x*R1) Hcut)
      [apply root_unique
       [apply H4
       |rewrite > Rtimes_x_R1 in H5:(??%?);
        symmetry;assumption]
      |skip]
     |simplify;rewrite > sym_Rtimes;left;assumption]]
   |assumption]]
 |rewrite > H1;
  apply ex_intro
  [apply (root 1 (Rexp_Z x OZ))
   [autobatch
   |simplify;left;autobatch]
  |apply ex_intro[apply OZ]
   apply ex_intro[apply 1]
   apply ex_intro[autobatch]
   apply ex_intro[simplify;left;autobatch]
   split
   [reflexivity
   |simplify;rewrite > Rtimes_x_R1;right;reflexivity]]]
|cases (R_archimedean R1 y)
 [apply ex_intro[apply (Rexp_Z x x1)]
  unfold;intros;unfold in H2;
  cases H2;cases H3;cases H4;cases H5;cases H6;
  clear H2 H3 H4 H5 H6;
  rewrite > Rtimes_x_R1 in H1;
  cut (x2 < x1*x3)
  [apply (trans_Rle ? (root x3 (Rexp_Z x (x1*x3)) ??))
   [assumption
   |apply (trans_Rle ??? x5);(*monotonia potenza*)elim daemon
   |rewrite > H7;left;
    (* monotonia della root *)
    elim daemon
   |right;elim (root_sound x3 (Rexp_Z (Rexp_Z x x1) x3))
    [rewrite < Rexp_Z_Rexp_Z_Rtimes
     [apply (inj_Rexp_nat ?? x3)
      [apply H2
      |left;rewrite < eq_Rexp_nat_Rexp_Z;apply pos_Rexp_nat;
       autobatch
      |assumption
      |symmetry;rewrite > eq_Rexp_nat_Rexp_Z;apply H3]
     |intro;rewrite > H4 in H;apply (asym_Rlt ?? H);apply lt_R0_R1]
    |*:skip]]
  |(*apply Rlt_div_l_to_r manca *) elim daemon]
 |autobatch]]
qed.

definition Rexp : ∀x,y:R.R0 < x → R.
intros;cases (decide ? ? (trichotomy_Rlt x R1))
[cases (decide ? ? H1)
 [apply (\fst (choose ?? (Rexp_lemma (Rinv x) r ?)));
  rewrite < Rtimes_x_R1 in ⊢(??%);rewrite < sym_Rtimes;
  apply Rlt_times_l_to_r
  [assumption
  |rewrite < sym_Rtimes;rewrite > Rtimes_x_R1;assumption]
 |apply (\fst (choose ?? (Rexp_lemma x r H2)))]
|apply R1]
qed.

(* testing "decide" axiom 
lemma aaa : ∀x,y:R.R1 < x → lub (expcut x y) (Rexp x y ?). 
[autobatch
|intros;unfold Rexp;
 cases (decide (x<R1∨R1<x) (x=R1) (trichotomy_Rlt x R1))
 [simplify;cases (decide (x<R1) (R1<x) H1)
  [elim (asym_Rlt ?? H H2)
  |simplify;
   apply (\snd (choose ℝ (lub (expcut x y)) (Rexp_lemma x y H2)))]
  |simplify;rewrite > H1 in H;elim (irrefl_Rlt ? H)]]
qed.*)

interpretation "real numbers exponent" 'exp a b = (Rexp a b ?).
