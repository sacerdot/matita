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

include "basic_2/reducibility/cpr_tpss.ma".
include "basic_2/computation/cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Properties on partial unfold for terms ***********************************)

lemma cprs_tpss_trans: ∀L,T1,T. L ⊢ T1 ➡* T →
                       ∀T2,d,e. L ⊢ T ▶* [d, e] T2 → L ⊢ T1 ➡* T2.
#L #T1 #T #H @(cprs_ind … H) -T /2 width=3/ /3 width=5/
qed.

lemma cprs_tps_trans: ∀L,T1,T. L ⊢ T1 ➡* T →
                      ∀T2,d,e. L ⊢ T ▶ [d, e] T2 → L ⊢ T1 ➡* T2.
/3 width=5 by inj, cprs_tpss_trans/ qed. (**) (* auto too slow without trace *)

lemma cprs_tpss_conf: ∀L,T0,T1. L ⊢ T0 ➡* T1 →
                      ∀T2,d,e. L ⊢ T0 ▶* [d, e] T2 →
                      ∃∃T. L ⊢ T1 ▶* [d, e] T & L ⊢ T2 ➡* T.
#L #T0 #T1 #H @(cprs_ind … H) -T1 /2 width=3/
#T #T1 #_ #HT1 #IHT0 #T2 #d #e #HT02
elim (IHT0 … HT02) -T0 #T0 #HT0 #HT20
elim (cpr_tpss_conf … HT1 … HT0) -T /3 width=5/
qed-.
