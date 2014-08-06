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

include "basic_2/computation/scpds_aaa.ma".
include "basic_2/equivalence/scpes.ma".

(* DECOMPOSED EXTENDED PARALLEL EQUIVALENCE FOR TERMS ***********************)

(* Main inversion lemmas about atomic arity assignment on terms *************)

theorem scpes_aaa_mono: ∀h,g,G,L,T1,T2,l1,l2. ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l1, l2] T2 →
                        ∀A1. ⦃G, L⦄ ⊢ T1 ⁝ A1 → ∀A2. ⦃G, L⦄ ⊢ T2 ⁝ A2 →
                        A1 = A2.
#h #g #G #L #T1 #T2 #l1 #l2 * #T #HT1 #HT2 #A1 #HA1 #A2 #HA2
lapply (scpds_aaa_conf … HA1 … HT1) -T1 #HA1
lapply (scpds_aaa_conf … HA2 … HT2) -T2 #HA2
lapply (aaa_mono … HA1 … HA2) -L -T //
qed-.
