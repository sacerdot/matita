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

include "basic_2/reducibility/tpr_tpr.ma".
include "basic_2/reducibility/fpr.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON CLOSURES ******************************)

(* Main properties **********************************************************)

theorem fpr_conf: bi_confluent … fpr.
#L0 #L1 #T0 #T1 * #HL01 #HT01 #L2 #T2 * >HL01 #HL12 #HT02
elim (tpr_conf … HT01 HT02) -L0 -T0 #X #H1 #H2
elim (tpr_fwd_shift1 … H1) #L #T #HL1 #H destruct /3 width=5/
qed.
