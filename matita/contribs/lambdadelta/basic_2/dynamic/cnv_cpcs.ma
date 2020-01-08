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

include "basic_2/rt_computation/csx_aaa.ma".
include "basic_2/rt_equivalence/cpcs_csx.ma".
include "basic_2/dynamic/cnv_aaa.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Properties with r-equivalence ********************************************)

lemma cnv_cpcs_dec (h) (a) (G) (L):
      ∀T1. ❪G,L❫ ⊢ T1 ![h,a] → ∀T2. ❪G,L❫ ⊢ T2 ![h,a] →
      Decidable … (❪G,L❫ ⊢ T1 ⬌*[h] T2).
#h #a #G #L #T1 #HT1 #T2 #HT2
elim (cnv_fwd_aaa … HT1) -HT1 #A1 #HA1
elim (cnv_fwd_aaa … HT2) -HT2 #A2 #HA2
/3 width=2 by csx_cpcs_dec, aaa_csx/
qed-.
