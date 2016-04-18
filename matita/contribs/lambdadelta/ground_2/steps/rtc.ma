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

include "ground_2/notation/constructors/tuple_4.ma".
include "ground_2/notation/constructors/zerozero_0.ma".
include "ground_2/notation/constructors/zeroone_0.ma".
include "ground_2/notation/constructors/onezero_0.ma".
include "ground_2/lib/arith.ma".

(* RT-TRANSITION COUNTER ****************************************************)

record rtc: Type[0] ≝ {
   ri: nat; (* Note: inner r-steps *)
   rh: nat; (* Note: head  r-steps *)
   ti: nat; (* Note: inner t-steps *)
   th: nat  (* Note: head  t-steps *)
}.

interpretation "constructor (rtc)"
   'Tuple ri rh ti th = (mk_rtc ri rh ti th).

(* Note: for one structural step *)
definition OO: rtc ≝ 〈0, 0, 0, 0〉.

interpretation "one structural step (rtc)"
   'ZeroZero = (OO).

(* Note: for one r-step *)
definition UO: rtc ≝ 〈0, 1, 0, 0〉.

interpretation "one r-step (rtc)"
   'OneZero = (UO).

(* Note: for one t-step *)
definition OU: rtc ≝ 〈0, 0, 0, 1〉.

interpretation "one t-step (rtc)"
   'ZeroOne = (OU).
