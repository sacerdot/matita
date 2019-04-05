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

include "basic_2/rt_computation/cpms_aaa.ma".
include "basic_2/rt_equivalence/cpes.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-EQUIVALENCE FOR TERMS **************)

(* Properties with atomic arity assignment on terms *************************)

(* Basic_2A1: uses: scpes_refl *)
lemma cpes_refl_aaa (h) (n):
      ∀G,L,T,A.  ⦃G, L⦄ ⊢ T ⁝ A → ⦃G, L⦄ ⊢ T ⬌*[h,n,n] T.
#h #n #G #L #T #A #HA
elim (aaa_cpms_total h … n … HA) #U #HTU
/2 width=3 by cpms_div/
qed.

(* Main inversion lemmas with atomic arity assignment on terms **************)

(* Basic_2A1: uses: scpes_aaa_mono *)
theorem cpes_aaa_mono (h) (n1) (n2):
        ∀G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ⬌*[h,n1,n2] T2 →
        ∀A1. ⦃G, L⦄ ⊢ T1 ⁝ A1 → ∀A2. ⦃G, L⦄ ⊢ T2 ⁝ A2 → A1 = A2.
#h #n1 #n2 #G #L #T1 #T2 * #T #HT1 #HT2 #A1 #HA1 #A2 #HA2
lapply (cpms_aaa_conf … HA1 … HT1) -T1 #HA1
lapply (cpms_aaa_conf … HA2 … HT2) -T2 #HA2
lapply (aaa_mono … HA1 … HA2) -L -T //
qed-.
