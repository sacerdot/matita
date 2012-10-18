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

include "basic_2/reducibility/cpr_cpr.ma".
include "basic_2/reducibility/cfpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON CLOSURES *************************)

(* Main properties **********************************************************)

theorem cfpr_conf: ∀L. bi_confluent … (cfpr L).
#L #L0 #L1 #T0 #T1 * #HL01 #HT01 #L2 #T2 * >HL01 #HL12 #HT02
elim (cpr_conf … HT01 HT02) -L0 -T0 #X #H1 #H2
elim (cpr_fwd_shift1 … H1) #L0 #T0 #HL10 #H destruct /3 width=5/
qed.
