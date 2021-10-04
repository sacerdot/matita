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

include "ground/notation/functions/element_u_1.ma".
include "ground/relocation/pr_nexts.ma".
include "ground/relocation/pr_id.ma".

(* UNIFORM ELEMENTS FOR PARTIAL RELOCATION MAPS *****************************)

(*** uni *)
definition pr_uni (n) ≝ ↑*[n] 𝐢.

interpretation
  "uniform elements (partial relocation maps)"
  'ElementU n = (pr_uni n).

(* Basic constructions ******************************************************)

(*** uni_zero *)
lemma pr_uni_zero: 𝐢 = 𝐮❨𝟎❩.
// qed.

(*** uni_succ *)
lemma pr_uni_succ (n): ↑𝐮❨n❩ = 𝐮❨↑n❩.
/2 width=1 by pr_nexts_succ/ qed.
