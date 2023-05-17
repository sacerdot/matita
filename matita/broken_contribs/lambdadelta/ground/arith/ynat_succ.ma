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

include "ground/notation/functions/upspoon_1.ma".
include "ground/arith/nat_succ.ma".
include "ground/arith/ynat_nat.ma".

(* SUCCESSOR FOR NON-NEGATIVE INTEGERS WITH INFINITY ************************)

definition ysucc_aux (n): ynat ≝
           yinj_nat (↑n).

(*** ysucc *)
definition ysucc: ynat → ynat ≝
           ynat_bind_nat ysucc_aux (∞).

interpretation
  "successor (non-negative integers with infinity)"
  'UpSpoon x = (ysucc x).

(* Constructions ************************************************************)

(*** ysucc_inj *)
lemma ysucc_inj (n): yinj_nat (↑n) = ⫯(yinj_nat n).
@(ynat_bind_nat_inj ysucc_aux)
qed.

(*** ysucc_Y *)
lemma ysucc_inf: ∞ = ⫯∞.
// qed.

(* Inversions ***************************************************************)

(*** ysucc_inv_inj_sn *)
lemma eq_inv_inj_ysucc (n1) (x2:ynat):
      yinj_nat n1 = ⫯x2 →
      ∃∃n2. yinj_nat n2 = x2 & ↑n2 ={ℕ} n1.
#n1 #x2 @(ynat_split_nat_inf … x2) -x2
[ /3 width=3 by eq_inv_yinj_nat_bi, ex2_intro/
| #H elim (eq_inv_yinj_nat_inf … H)
]
qed-.

(*** ysucc_inv_inj_dx *)
lemma eq_inv_ysucc_inj (x1) (n2):
      (⫯x1) = yinj_nat n2  →
      ∃∃n1. yinj_nat n1 = x1 & ↑n1 ={ℕ} n2.
/2 width=1 by eq_inv_inj_ysucc/ qed-.

(*** ysucc_inv_Y_sn *)
lemma eq_inv_inf_ysucc (x2): ∞ = ⫯x2 → ∞ = x2.
#x2 @(ynat_split_nat_inf … x2) -x2 //
#n1 <ysucc_inj #H elim (eq_inv_inf_yinj_nat … H)
qed-.

(*** ysucc_inv_Y_dx *)
lemma eq_inv_ysucc_inf (x1): ⫯x1 = ∞ → ∞ = x1.
/2 width=1 by eq_inv_inf_ysucc/ qed-.

(*** ysucc_inv_inj *)
lemma eq_inv_ysucc_bi: injective … ysucc.
#x1 @(ynat_split_nat_inf … x1) -x1
[ #n1 #x2 <ysucc_inj #H
  elim (eq_inv_inj_ysucc … H) -H #n2 #H1 #H2 destruct
  <(eq_inv_nsucc_bi … H2) -H2 //
| #x2 #H <(eq_inv_inf_ysucc … H) -H //
]
qed-.

(*** ysucc_inv_refl *)
lemma eq_inv_fix_ysucc (x): x = ⫯x → ∞ = x.
#x @(ynat_split_nat_inf … x) -x //
#n <ysucc_inj #H
lapply (eq_inv_yinj_nat_bi … H) -H #H
elim (eq_inv_fix_nsucc … H)
qed-.

(*** ysucc_inv_O_sn *)
lemma eq_inv_zero_ysucc (x): 𝟎 = ⫯x → ⊥.
#x #H
elim (eq_inv_inj_ysucc (𝟎) ? H) -H #n #_ #H
/2 width=2 by eq_inv_zero_npos/
qed-.

(*** ysucc_inv_O_dx *)
lemma eq_inv_ysucc_zero (x): ⫯x = 𝟎 → ⊥.
/2 width=2 by eq_inv_zero_ysucc/ qed-.

(* Eliminations *************************************************************)

(*** ynat_ind *)
lemma ynat_ind_succ (Q:predicate …):
      Q (𝟎) → (∀n:ℕ. Q (yinj_nat n) → Q (⫯(yinj_nat n))) → Q (∞) → ∀x. Q x.
#Q #IH1 #IH2 #IH3 #x @(ynat_split_nat_inf … x) -x //
#n @(nat_ind_succ … n) -n /2 width=1 by/
qed-.
