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

include "Basic-2/reduction/tpr_lift.ma".
include "Basic-2/reduction/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS ****************************)

(* Relocation properties ****************************************************)

(* Basic-1: was: pr2_lift *)

(* Basic-1: was: pr2_gen_lift *)

(* Advanced inversion lemmas ************************************************)

(* Basic-1: was: pr2_gen_abst *)
lemma cpr_inv_abst1: ∀V1,T1,U2. 𝕔{Abst} V1. T1 ⇒ U2 →
                     ∃∃V2,T2. V1 ⇒ V2 & T1 ⇒ T2 & U2 = 𝕔{Abst} V2. T2.
/2/ qed.
