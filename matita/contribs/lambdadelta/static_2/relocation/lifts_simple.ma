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
include "static_2/relocation/lifts.ma".

(* GENERIC RELOCATION FOR TERMS *********************************************)

(* Forward lemmas with simple terms *****************************************)

(* Basic_2A1: includes: lift_simple_dx *)
lemma lifts_simple_dx: âf,T1,T2. â§*[f] T1 â T2 â đâšT1â© â đâšT2â©.
#f #T1 #T2 #H elim H -f -T1 -T2 //
#f #p #I #V1 #V2 #T1 #T2 #_ #_ #_ #_ #H elim (simple_inv_bind âŠ H)
qed-.

(* Basic_2A1: includes: lift_simple_sn *)
lemma lifts_simple_sn: âf,T1,T2. â§*[f] T1 â T2 â đâšT2â© â đâšT1â©.
#f #T1 #T2 #H elim H -f -T1 -T2 //
#f #p #I #V1 #V2 #T1 #T2 #_ #_ #_ #_ #H elim (simple_inv_bind âŠ H)
qed-.
