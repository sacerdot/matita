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

include "Q/q/qtimes.ma".
include "Q/q/qplus.ma".
include "logic/cprop_connectives.ma".

interpretation "Q" 'Q = Q. 

(* group over Q *)
axiom qp : ℚ → ℚ → ℚ.

interpretation "Q plus" 'plus x y = (qp x y).
interpretation "Q minus" 'minus x y = (qp x (Qopp y)).

axiom q_plus_OQ: ∀x:ℚ.x + OQ = x.
axiom q_plus_sym: ∀x,y:ℚ.x + y = y + x.
axiom q_plus_minus: ∀x.x - x = OQ.
axiom q_plus_assoc: ∀x,y,z.x + (y + z) = x + y + z. 
axiom q_opp_plus: ∀x,y,z:Q. Qopp (y + z) = Qopp y + Qopp z.

(* order over Q *)
axiom qlt : ℚ → ℚ → Prop.
axiom qle : ℚ → ℚ → Prop.
interpretation "Q less than" 'lt x y = (qlt x y).
interpretation "Q less or equal than" 'leq x y = (qle x y).

inductive q_comparison (a,b:ℚ) : CProp ≝
 | q_leq : a ≤ b → q_comparison a b 
 | q_gt : b < a → q_comparison a b.

axiom q_cmp:∀a,b:ℚ.q_comparison a b.

inductive q_le_elimination (a,b:ℚ) : CProp ≝
| q_le_from_eq : a = b → q_le_elimination a b
| q_le_from_lt : a < b → q_le_elimination a b.

axiom q_le_cases : ∀x,y:ℚ.x ≤ y → q_le_elimination x y.

axiom q_le_to_le_to_eq : ∀x,y. x ≤ y → y ≤ x → x = y.

axiom q_le_plus_l: ∀a,b,c:ℚ. a ≤ c - b → a + b ≤ c.
axiom q_le_plus_r: ∀a,b,c:ℚ. a - b ≤ c → a ≤ c + b.
axiom q_lt_plus_l: ∀a,b,c:ℚ. a < c - b → a + b < c.
axiom q_lt_plus_r: ∀a,b,c:ℚ. a - b < c → a < c + b.

axiom q_lt_opp_opp: ∀a,b.b < a → Qopp a < Qopp b.

axiom q_le_n: ∀x. x ≤ x.
axiom q_lt_to_le: ∀a,b:ℚ.a < b → a ≤ b.

axiom q_lt_corefl: ∀x:Q.x < x → False.
axiom q_lt_le_incompat: ∀x,y:Q.x < y → y ≤ x → False.

axiom q_neg_gt: ∀r:ratio.Qneg r < OQ.
axiom q_pos_OQ: ∀x.OQ < Qpos x.

axiom q_lt_trans: ∀x,y,z:Q. x < y → y < z → x < z.
axiom q_lt_le_trans: ∀x,y,z:Q. x < y → y ≤ z → x < z.
axiom q_le_lt_trans: ∀x,y,z:Q. x ≤ y → y < z → x < z.
axiom q_le_trans: ∀x,y,z:Q. x ≤ y → y ≤ z → x ≤ z.

axiom q_le_lt_OQ_plus_trans: ∀x,y:Q.OQ ≤ x → OQ < y → OQ < x + y.
axiom q_lt_le_OQ_plus_trans: ∀x,y:Q.OQ < x → OQ ≤ y → OQ < x + y.
axiom q_le_OQ_plus_trans: ∀x,y:Q.OQ ≤ x → OQ ≤ y → OQ ≤ x + y.

axiom q_leWl: ∀x,y,z.OQ ≤ x → x + y ≤ z → y ≤ z.
axiom q_ltWl: ∀x,y,z.OQ ≤ x → x + y < z → y < z.

(* distance *)
axiom q_dist : ℚ → ℚ → ℚ.

notation "hbox(\dd [term 19 x, break term 19 y])" with precedence 90
for @{'distance $x $y}.
interpretation "ℚ distance" 'distance x y = (q_dist x y).

axiom q_d_ge_OQ : ∀x,y:ℚ. OQ ≤ ⅆ[x,y].
axiom q_d_OQ: ∀x:Q.ⅆ[x,x] = OQ.
axiom q_d_noabs: ∀x,y. x ≤ y → ⅆ[y,x] = y - x.
axiom q_d_sym: ∀x,y. ⅆ[x,y] = ⅆ[y,x].

lemma q_2opp: ∀x:ℚ.Qopp (Qopp x) = x.
intros; cases x; reflexivity; qed.

(* derived *)
lemma q_lt_canc_plus_r:
  ∀x,y,z:Q.x + z < y + z → x < y.
intros; rewrite < (q_plus_OQ y); rewrite < (q_plus_minus z);
rewrite > q_plus_assoc; apply q_lt_plus_r; rewrite > q_2opp; assumption;
qed.

lemma q_lt_inj_plus_r:
  ∀x,y,z:Q.x < y → x + z < y + z.
intros; apply (q_lt_canc_plus_r ?? (Qopp z));
do 2 rewrite < q_plus_assoc; rewrite > q_plus_minus; 
do 2 rewrite > q_plus_OQ; assumption;
qed.

lemma q_le_inj_plus_r:
  ∀x,y,z:Q.x ≤ y → x + z ≤ y + z.
intros;cases (q_le_cases ?? H);
[1: rewrite > H1; apply q_le_n;
|2: apply q_lt_to_le; apply q_lt_inj_plus_r; assumption;]
qed.

lemma q_le_canc_plus_r:
  ∀x,y,z:Q.x + z ≤ y + z → x ≤ y.
intros; lapply (q_le_inj_plus_r ?? (Qopp z) H) as H1;
do 2 rewrite < q_plus_assoc in H1;
rewrite > q_plus_minus in H1; do 2 rewrite > q_plus_OQ in H1; assumption;
qed. 
