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

include "basic_2/rt_conversion/lpce.ma".
include "basic_2/dynamic/cnv.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

theorem cnv_cpce_trans_lpce (h) (G):
        ∀L1,T1,T2. ⦃G,L1⦄ ⊢ T1 ⬌η[h] T2 → ⦃G,L1⦄ ⊢ T1 !*[h] →
        ∀L2. ⦃G,L1⦄ ⊢ ⬌η[h] L2 → ⦃G,L2⦄ ⊢ T2 !*[h].
#h #G #L1 #T1 #T2 #H elim H -G -L1 -T1 -T2
[ #G #L1 #s #_ #L2 #_ //
| #G #K1 #V1 #_ #Y2 #HY
  elim (lpce_inv_pair_sn … HY) -HY #K2 #V2 #HK #HV #H destruct               