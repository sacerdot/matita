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

include "basic_2/static/lsubr.ma".
include "basic_2/rt_transition/cpg.ma".

(* COUNTED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Properties with restricted refinement for local environments *************)

lemma lsubr_cpg_trans: ∀Rt,c,h,G. lsub_trans … (cpg Rt h c G) lsubr.
#Rt #c #h #G #L1 #T1 #T2 #H elim H -c -G -L1 -T1 -T2
[ //
| /2 width=2 by cpg_ess/
| #c #G #L1 #V1 #V2 #W2 #_ #HVW2 #IH #X #H
  elim (lsubr_inv_abbr2 … H) -H #L2 #HL21 #H destruct
  /3 width=3 by cpg_delta/
| #c #G #L1 #V1 #V2 #W2 #_ #HVW2 #IH #X #H
  elim (lsubr_inv_abst2 … H) -H * #L2 [2: #V ] #HL21 #H destruct
  /4 width=3 by cpg_delta, cpg_ell, cpg_ee/
| #c #I1 #G #L1 #V1 #T1 #U1 #i #_ #HTU1 #IH #X #H
  elim (lsubr_fwd_pair2 … H) -H #I2 #L2 #V2 #HL21 #H destruct
  /3 width=3 by cpg_lref/
|6,12: /4 width=1 by cpg_bind, cpg_beta, lsubr_pair/
|7,8,10,11: /3 width=1 by cpg_appl, cpg_cast, cpg_eps, cpg_ee/
|9,13: /4 width=3 by cpg_zeta, cpg_theta, lsubr_pair/
]
qed-.
