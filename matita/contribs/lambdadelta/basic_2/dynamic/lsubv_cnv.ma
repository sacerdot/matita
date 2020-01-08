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

include "basic_2/dynamic/lsubv_cpms.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR NATIVE VALIDITY *************************)

(* Forward lemmas with native validity **************************************)

(* Basic_2A1: uses: lsubsv_snv_trans *)
lemma lsubv_cnv_trans (h) (a) (G):
      ∀L2,T. ❪G,L2❫ ⊢ T ![h,a] →
      ∀L1. G ⊢ L1 ⫃![h,a] L2 → ❪G,L1❫ ⊢ T ![h,a].
#h #a #G #L2 #T #H elim H -G -L2 -T //
[ #I #G #K2 #V #HV #IH #L1 #H
  elim (lsubv_inv_bind_dx … H) -H * /3 width=1 by cnv_zero/
| #I #G #K2 #i #_ #IH #L1 #H
  elim (lsubv_inv_bind_dx … H) -H * /3 width=1 by cnv_lref/
| #p #I #G #L2 #V #T #_ #_ #IHV #IHT #L1 #HL12
  /4 width=1 by cnv_bind, lsubv_bind/
| #n #p #G #L2 #V #W #T #U #Ha #_ #_ #HVW #HTU #IHV #IHT #L1 #HL
  /4 width=10 by lsubv_cpms_trans, cnv_appl/
| #G #L2 #U #T #U0 #_ #_ #HU0 #HTU0 #IHU #IHT #L1 #HL12
  /4 width=6 by lsubv_cpms_trans, cnv_cast/
]
qed-.
