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

include "basic_2/unfold/ltpss_ltpss.ma".
include "basic_2/reducibility/cpr.ma".
include "basic_2/reducibility/lcpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON LOCAL ENVIRONMENTS *************)

(* Advanced properties ****************************************************)

lemma lcpr_pair: ∀L1,L2. L1 ⊢ ➡ L2 → ∀V1,V2. L2 ⊢ V1 ➡ V2 →
                 ∀I. L1. ⓑ{I} V1 ⊢ ➡ L2. ⓑ{I} V2.
#L1 #L2 * #L #HL1 #HL2 #V1 #V2 *
<(ltpss_fwd_length … HL2) /4 width=5/
qed.

lemma ltpss_lcpr: ∀L1,L2,d,e. L1 ▶* [d, e] L2 → L1 ⊢ ➡ L2.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e // /3 width=3/
qed. 
