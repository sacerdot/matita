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

definition un_t: prototerm ≝
           ＠(𝛌.⧣𝟏).𝛌.𝛌.＠(⧣𝟐).𝛌.＠(⧣𝟐).⧣𝟏.

definition un_i1: prototerm ≝
           ＠(𝛌.⧣𝟏).𝛌.𝛌.＠(𝛌.⧣𝟏).𝛌.＠(⧣𝟐).⧣𝟏.

lemma un_ti1:
      un_t ➡𝐢𝐛𝐟[𝗔◗𝗟◗𝗟◗𝗦◗𝐞] un_i1.
@(ibfr_eq_trans … (ibfr_beta_0 …))
[ >list_append_lcons_sn
  /3 width=1 by in_comp_appl_sd, in_comp_abst_hd/
| /3 width=3 by pcc_S_sn, pcc_L_sn/
| skip
]
@appl_eq_repl [ // ] @abst_eq_repl
@(subset_eq_canc_sn … (fsubst_abst_hd …)) @abst_eq_repl
@(subset_eq_canc_sn … (fsubst_appl_sd …)) @appl_eq_repl [| // ]
@(subset_eq_canc_sn … (fsubst_empty_rc …))
@(subset_eq_canc_sn … (lift_term_abst …)) @abst_eq_repl
@(subset_eq_canc_sn … (lift_term_oref_pap … )) //
qed.

definition un_i2: prototerm ≝
           ＠(𝛌.⧣𝟏).𝛌.𝛌.＠(𝛌.⧣𝟏).𝛌.＠(⧣𝟐).𝛌.⧣𝟏.

lemma un_i12:
      un_i1 ➡𝐢𝐛𝐟[𝗔◗𝗟◗𝗟◗𝗔◗𝗟◗𝗔◗𝐞] un_i2.
@ibfr_appl_hd
@ibfr_abst_hd
@ibfr_abst_hd
@(ibfr_eq_trans … (ibfr_beta_0 …))
[ >list_append_lcons_sn
  /2 width=1 by in_comp_appl_hd/
| /2 width=1 by pcc_A_sn, pcc_empty/
| skip
]
@appl_eq_repl [ // ] @abst_eq_repl
@(subset_eq_canc_sn … (fsubst_appl_hd …)) @appl_eq_repl [ // ]
@(subset_eq_canc_sn … (fsubst_empty_rc …))
@(subset_eq_canc_sn … (lift_term_abst …)) @abst_eq_repl
@(subset_eq_canc_sn … (lift_term_oref_pap … )) //
qed.

definition un_i3: prototerm ≝
           ＠(𝛌.⧣𝟏).𝛌.𝛌.＠(𝛌.⧣𝟏).𝛌.＠(⧣𝟐).𝛌.⧣↑𝟐.

lemma un_i23:
      un_i2 ➡𝐢𝐛𝐟[𝗔◗𝗟◗𝗟◗𝗔◗𝗟◗𝗔◗𝗟◗𝐞] un_i3.
@ibfr_appl_hd
@ibfr_abst_hd
@ibfr_abst_hd
@ibfr_appl_hd
@ibfr_abst_hd
@(ibfr_eq_trans … (ibfr_beta_0 …))
[ // | // | skip ]
@appl_eq_repl [ // ] @abst_eq_repl
@(subset_eq_canc_sn … (fsubst_empty_rc …))
@(subset_eq_canc_sn … (lift_term_oref_pap … )) //
qed.

definition un_d1: prototerm ≝
           ＠(𝛌.⧣𝟏).𝛌.𝛌.＠(𝛕𝟐.𝛌.⧣𝟏).𝛌.＠(⧣𝟐).⧣𝟏.

lemma un_td1:
      un_t ➡𝐝𝐛𝐟[𝗔◗𝗟◗𝗟◗𝗦◗𝐞] un_d1.
@(dbfr_eq_trans … (dbfr_beta_0 …))
[ >list_append_lcons_sn
  /3 width=1 by in_comp_appl_sd, in_comp_abst_hd/
| /3 width=3 by pcc_S_sn, pcc_L_sn/
| skip
]
@appl_eq_repl [ // ] @abst_eq_repl
@(subset_eq_canc_sn … (fsubst_abst_hd …)) @abst_eq_repl
@(subset_eq_canc_sn … (fsubst_appl_sd …)) @appl_eq_repl [| // ]
@(subset_eq_canc_sn … (fsubst_empty_rc …))
@iref_eq_repl //
qed.

definition un_d2: prototerm ≝
           ＠(𝛌.⧣𝟏).𝛌.𝛌.＠(𝛕𝟐.𝛌.⧣𝟏).𝛌.＠(⧣𝟐).𝛕𝟏.𝛕𝟐.𝛌.⧣𝟏.

lemma un_d12:
      un_d1 ➡𝐝𝐛𝐟[𝗔◗𝗟◗𝗟◗𝗔◗𝗟◗𝗔◗𝐞] un_d2.
@dbfr_appl_hd
@dbfr_abst_hd
@dbfr_abst_hd
@(dbfr_eq_trans … (dbfr_beta_0 …))
[ >list_append_lcons_sn /2 width=1 by in_comp_appl_hd/
| /2 width=1 by pcc_A_sn/
| skip
]
@appl_eq_repl [ // ] @abst_eq_repl
@(subset_eq_canc_sn … (fsubst_appl_hd …)) @appl_eq_repl [ // ]
@(subset_eq_canc_sn … (fsubst_empty_rc …))
@iref_eq_repl @iref_eq_repl //
qed.

definition un_d3: prototerm ≝
           ＠(𝛌.⧣𝟏).𝛌.𝛌.＠(𝛕𝟐.𝛌.⧣𝟏).𝛌.＠(⧣𝟐).𝛌.𝛕𝟏.⧣𝟐.

lemma un_di3:
      un_i3 ⇔ ▼[𝐢] un_d3.
@(subset_eq_canc_sn … (unwind2_term_appl …)) @appl_eq_repl
[ @(subset_eq_canc_sn … (unwind2_term_abst …)) @abst_eq_repl
  @(subset_eq_canc_sn … (unwind2_term_oref_pap …)) //
]
@(subset_eq_canc_sn … (unwind2_term_abst …)) @abst_eq_repl
@(subset_eq_canc_sn … (unwind2_term_abst …)) @abst_eq_repl
@(subset_eq_canc_sn … (unwind2_term_appl …)) @appl_eq_repl
[ @(subset_eq_canc_sn … (unwind2_term_iref …))
  @(subset_eq_canc_sn … (unwind2_term_abst …)) @abst_eq_repl
  @(subset_eq_canc_sn … (unwind2_term_oref_pap …)) //
]
@(subset_eq_canc_sn … (unwind2_term_abst …)) @abst_eq_repl
@(subset_eq_canc_sn … (unwind2_term_appl …)) @appl_eq_repl
[ @(subset_eq_canc_sn … (unwind2_term_oref_pap …)) //
]
@(subset_eq_canc_sn … (unwind2_term_abst …)) @abst_eq_repl
@(subset_eq_canc_sn … (unwind2_term_iref …))
@(subset_eq_canc_sn … (unwind2_term_oref_pap …)) //
qed.
