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

include "basic_2/unfold/sstas_lift.ma".
include "basic_2/computation/cprs_lift.ma".
include "basic_2/computation/cpds.ma".

(* DECOMPOSED EXTENDED PARALLEL COMPUTATION ON TERMS ************************)

(* Relocation properties ****************************************************)

lemma cpds_lift: ∀h,g,G. l_liftable (cpds h g G).
#h #g #G #K #T1 #T2 * #T #HT1 #HT2 #L #d #e
elim (lift_total T d e)
/3 width=11 by cprs_lift, sstas_lift, ex2_intro/
qed.

lemma cpds_inv_lift1: ∀h,g,G. l_deliftable_sn (cpds h g G).
#h #g #G #L #U1 #U2 * #U #HU1 #HU2 #K #d #e #HLK #T1 #HTU1
elim (sstas_inv_lift1 … HU1 … HLK … HTU1) -U1 #T #HT1 #HTU
elim (cprs_inv_lift1 … HU2 … HLK … HTU) -U -L /3 width=5/
qed-.
