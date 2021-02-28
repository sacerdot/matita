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

include "ground/xoa/ex_1_2.ma".
include "ground/notation/functions/tuple_4.ma".
include "ground/notation/functions/zerozero_0.ma".
include "ground/notation/functions/zeroone_0.ma".
include "ground/notation/functions/onezero_0.ma".
include "ground/generated/insert_eq_1.ma".
include "ground/arith/nat.ma".

(* RT-TRANSITION COUNTERS ***************************************************)

record rtc: Type[0] ≝ {
(* Note: inner r-steps *)
   ri: nat;
(* Note: spine r-steps *)
   rs: nat;
(* Note: inner t-steps *)
   ti: nat;
(* Note: spine t-steps *)
   ts: nat
}.

interpretation
  "constructor (rtc)"
  'Tuple ri rs ti ts = (mk_rtc ri rs ti ts).

interpretation
  "one structural step (rtc)"
  'ZeroZero = (mk_rtc nzero nzero nzero nzero).

interpretation
  "one r-step (rtc)"
  'OneZero = (mk_rtc nzero (ninj punit) nzero nzero).

interpretation
  "one t-step (rtc)"
  'ZeroOne = (mk_rtc nzero nzero nzero (ninj punit)).

definition rtc_eq_f: relation rtc ≝ λc1,c2. ⊤.

inductive rtc_eq_t: relation rtc ≝
| eq_t_intro: ∀ri1,ri2,rs1,rs2,ti,ts.
              rtc_eq_t (〈ri1,rs1,ti,ts〉) (〈ri2,rs2,ti,ts〉)
.

(* Basic constructions ******************************************************)

lemma rtc_eq_t_refl: reflexive …  rtc_eq_t.
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
