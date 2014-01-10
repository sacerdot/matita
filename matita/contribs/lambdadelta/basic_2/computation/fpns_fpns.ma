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

include "basic_2/substitution/lleq_lleq.ma".
include "basic_2/computation/lpxs_lpxs.ma".
include "basic_2/computation/fpns.ma".

(* PARALLEL COMPUTATION FOR "BIG TREE" NORMAL FORMS *************************)

(* Main properties **********************************************************)

theorem fpns_trans: ∀h,g. tri_transitive … (fpns h g).
#h #g #G1 #G #L1 #L #T1 #T * -G -L -T
#L #HL1 #HT1 #G2 #L2 #T2 * -G2 -L2 -T2
/3 width=3 by lpxs_trans, lleq_trans, fpns_intro/
qed-.
