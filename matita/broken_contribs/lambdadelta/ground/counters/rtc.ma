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

include "ground/notation/functions/zerozero_0.ma".
include "ground/notation/functions/zeroone_0.ma".
include "ground/notation/functions/onezero_0.ma".
include "ground/xoa/ex_1_2.ma".
include "ground/generated/prod_4.ma".
include "ground/generated/insert_eq_1.ma".
include "ground/arith/nat.ma".

(* RT-TRANSITION COUNTERS ***************************************************)

definition rtc: Type[0] ≝
           (⨉ ℕ & ℕ & ℕ & ℕ).

(* Note: inner r-steps *)
definition ri: rtc → ℕ ≝
           proj_4_1 ????.

(* Note: spine r-steps *)
definition rs: rtc → ℕ ≝
           proj_4_2 ????.

(* Note: inner t-steps *)
definition ti: rtc → ℕ ≝
           proj_4_3 ????.

(* Note: spine t-steps *)
definition ts: rtc → ℕ ≝
           proj_4_4 ????.

interpretation
  "one structural step (rt-transition counters)"
  'ZeroZero = (mk_prod_4 ???? nzero nzero nzero nzero).

interpretation
  "one r-step (rt-transition counters)"
  'OneZero = (mk_prod_4 ???? nzero (npos punit) nzero nzero).

interpretation
  "one t-step (rt-transition counters)"
  'ZeroOne = (mk_prod_4 ???? nzero nzero nzero (npos punit)).

definition rtc_eq_f: relation rtc ≝ λc1,c2. ⊤.

inductive rtc_eq_t: relation rtc ≝
| eq_t_intro: ∀ri1,ri2,rs1,rs2,ti,ts.
              rtc_eq_t (〈ri1,rs1,ti,ts〉) (〈ri2,rs2,ti,ts〉)
.

(* Basic constructions ******************************************************)

lemma rtc_eq_t_refl:
      reflexive …  rtc_eq_t.
* // qed.

(* Basic inversions *********************************************************)

lemma rtc_eq_t_inv_dx:
      ∀ri1,rs1,ti,ts,y. rtc_eq_t (〈ri1,rs1,ti,ts〉) y →
      ∃∃ri2,rs2. y = 〈ri2,rs2,ti,ts〉.
#ri0 #rs0 #ti0 #ts0 #y @(insert_eq_1 … (〈ri0,rs0,ti0,ts0〉))
#x * -x -y
#ri1 #ri2 #rs1 #rs2 #ti1 #ts1 #H destruct -ri1 -rs1
/2 width=3 by ex1_2_intro/
qed-.
