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

include "static_2/syntax/term_simple.ma".
include "static_2/syntax/teqw.ma".

(* SORT-IRRELEVANT WHD EQUIVALENCE ON TERMS *********************************)

(* Properties with simple terms *********************************************)

lemma teqw_simple_trans:
      âT1,T2. T1 â T2 â đâšT1â© â đâšT2â©.
#T1 #T2 * -T1 -T2
[4,5: #p #V1 #V2 #T1 #T2 [ #_ ] #H
      elim (simple_inv_bind âŠ H)
|*  : /1 width=1 by simple_atom, simple_flat/
]
qed-.
