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

include "basic_2/equivalence/cpcs_ltpss_dx.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON TERMS **************************)

(* Properties concerning sn partial unfold on local environments ************)

lemma cpcs_ltpss_sn_conf: ∀L1,L2,d,e. L1 ⊢ ▶* [d, e] L2 →
                          ∀T1,T2. L1 ⊢ T1 ⬌* T2 → L2 ⊢ T1 ⬌* T2.
#L1 #L2 #d #e #H
lapply (ltpss_sn_ltpssa … H) -H #H @(ltpssa_ind … H) -L2 //
#L #L2 #_ #HL2 #IHL1 #T1 #U1 #HTU1
lapply (IHL1 … HTU1) -IHL1 -HTU1 #HTU1
lapply (cpcs_ltpss_dx_conf … HL2 … HTU1) -HTU1 -HL2 //
qed-.
