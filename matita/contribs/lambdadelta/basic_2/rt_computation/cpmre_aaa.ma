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
include "basic_2/rt_computation/cpms_aaa.ma".
include "basic_2/rt_computation/cprre_csx.ma".
include "basic_2/rt_computation/cprre_cpms.ma".

(* EVALUATION FOR T-BOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION ON TERMS *)

(* Properties with atomic atomic arity assignment on terms ******************)

lemma cpmre_total_aaa (h) (n) (A) (G) (L):
      ∀T1. ⦃G,L⦄ ⊢ T1 ⁝ A → ∃T2. ⦃G,L⦄ ⊢ T1 ➡*[h,n] 𝐍⦃T2⦄.
#h #n #A #G #L #T1 #HT1
elim (cpms_total_aaa h … n … HT1) #T0 #HT10
elim (cprre_total_csx h G L T0)
[ #T2 /3 width=4 by cpms_cprre_trans, ex_intro/
| /4 width=4 by cpms_fwd_cpxs, aaa_csx, csx_cpxs_trans/
]
qed-.
