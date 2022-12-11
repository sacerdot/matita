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

include "delayed_updating/reduction/dbfr_constructors.ma".
include "delayed_updating/reduction/ibfr_constructors.ma".
include "delayed_updating/unwind/unwind2_prototerm_constructors.ma".
include "delayed_updating/substitution/lift_prototerm_constructors.ma".
include "ground/arith/pnat_two.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Example of unprotected balanced β-reduction ******************************)

definition l3_t: prototerm ≝
           (＠(⧣𝟏).＠(𝛌.⧣𝟏).𝛌.⧣𝟏).

definition l3_i1: prototerm ≝
           (＠(⧣𝟏).＠(𝛌.⧣𝟏).𝛌.𝛌.⧣𝟏).

definition l3_i2: prototerm ≝
           (＠(⧣𝟏).＠(𝛌.⧣𝟏).𝛌.𝛌.⧣↑𝟐).

definition l3_d1: prototerm ≝
           (＠(⧣𝟏).＠(𝛌.⧣𝟏).𝛌.𝛕𝟏.𝛌.⧣𝟏).

definition l3_d2: prototerm ≝
           (＠(⧣𝟏).＠(𝛌.⧣𝟏).𝛌.𝛕𝟏.𝛌.𝛕𝟏.⧣𝟏).

lemma l3_ti1:
      l3_t ➡𝐢𝐛𝐟[𝗔◗𝗔◗𝗟◗𝐞] l3_i1.
@ibfr_appl_hd
@ibfr_eq_trans [| @ibfr_beta_0 // ]
@appl_eq_repl [ // ]
@abst_eq_repl
@(subset_eq_canc_sn … (fsubst_empty_rc …))
@(subset_eq_canc_sn … (lift_term_abst …))
@abst_eq_repl
@(subset_eq_canc_sn … (lift_term_oref_pap … )) //
qed.

lemma l3_i12:
      l3_i1 ➡𝐢𝐛𝐟[𝗔◗𝗔◗𝗟◗𝗟◗𝐞] l3_i2.
@ibfr_eq_trans [| @ibfr_beta_1 // ]
@appl_eq_repl [ // ]
@appl_eq_repl [ // ]
@abst_eq_repl
@abst_eq_repl
@(subset_eq_canc_sn … (fsubst_empty_rc …))
@(subset_eq_canc_sn … (lift_term_oref_pap … )) //
qed.

lemma l3_td1:
      l3_t ➡𝐝𝐛𝐟[𝗔◗𝗔◗𝗟◗𝐞] l3_d1.
@dbfr_appl_hd
@dbfr_eq_trans [| @dbfr_beta_0 // ]
@appl_eq_repl [ // ]
@abst_eq_repl
@(subset_eq_canc_sn … (fsubst_empty_rc …)) //
qed.

lemma ld_di2:
      l3_i2 ⇔ ▼[𝐢]l3_d2.
@(subset_eq_canc_sn … (unwind2_term_appl …)) @appl_eq_repl
[ @(subset_eq_canc_sn … (unwind2_term_oref_pap …)) // ]
@(subset_eq_canc_sn … (unwind2_term_appl …)) @appl_eq_repl
[ @(subset_eq_canc_sn … (unwind2_term_abst …)) @abst_eq_repl
  @(subset_eq_canc_sn … (unwind2_term_oref_pap …)) //
]
@(subset_eq_canc_sn … (unwind2_term_abst …)) @abst_eq_repl
@(subset_eq_canc_sn … (unwind2_term_iref …))
@(subset_eq_canc_sn … (unwind2_term_abst …)) @abst_eq_repl
@(subset_eq_canc_sn … (unwind2_term_iref …))
@(subset_eq_canc_sn … (unwind2_term_oref_pap …)) //
qed.
