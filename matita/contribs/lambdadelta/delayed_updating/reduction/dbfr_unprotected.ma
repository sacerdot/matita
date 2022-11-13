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

include "delayed_updating/reduction/ibfr_constructors.ma".
include "delayed_updating/substitution/lift_prototerm_constructors.ma".
include "ground/arith/pnat_two.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Example of unprotected balanced β-reduction ******************************)

definition l3_t0: prototerm ≝
           (𝛌.＠(⧣𝟏).＠(𝛌.＠(⧣𝟐).⧣𝟏).𝛌.⧣𝟏).

definition l3_t1: prototerm ≝
           (𝛌.＠(⧣𝟏).＠(𝛌.＠(⧣𝟐).⧣𝟏).𝛌.(𝛌.＠(⧣↑𝟐).⧣𝟏)).

lemma l3_t01:
      l3_t0 ➡𝐢𝐛𝐟[𝗟◗𝗔◗𝗔◗𝗟◗𝐞] l3_t1.
@ibfr_abst_hd
@ibfr_appl_hd
@ibfr_eq_trans [| @ibfr_beta_0 // ]
@appl_eq_repl [ // ]
@abst_eq_repl
@(subset_eq_canc_sn … (fsubst_empty_rc …))
@(subset_eq_canc_sn … (lift_term_abst …))
@abst_eq_repl
@(subset_eq_canc_sn … (lift_term_appl … ))
@appl_eq_repl
@(subset_eq_canc_sn … (lift_term_oref_pap … )) //
qed.
