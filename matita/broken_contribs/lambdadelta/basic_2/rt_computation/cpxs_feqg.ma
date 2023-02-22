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

include "static_2/static/feqg.ma".
include "basic_2/rt_computation/cpxs_reqg.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS *************)

(* Properties with generic equivalence for closures *************************)

(* to update *)
lemma feqg_cpxs_trans (S):
      reflexive … S → symmetric … S →
      ∀G1,G2,L1,L2,T1,T. ❨G1,L1,T1❩ ≛[S] ❨G2,L2,T❩ →
      ∀T2. ❨G2,L2❩ ⊢ T ⬈* T2 →
      ∃∃T0. ❨G1,L1❩ ⊢ T1 ⬈* T0 & ❨G1,L1,T0❩ ≛[S] ❨G2,L2,T2❩.
#S #H1S #H2S #G1 #G2 #L1 #L2 #T1 #T #H #T2 #H2T2
elim (feqg_inv_gen_dx … H) -H // #H #HL12 #HT1 destruct
lapply (reqg_cpxs_trans … H2T2 … HL12) // #H1T2
lapply (cpxs_reqg_conf_dx … H2T2 … HL12) -HL12 // #HL12
lapply (teqg_cpxs_trans … HT1 … H1T2) -T // #HT12
/4 width=3 by feqg_intro_dx, teqg_refl, ex2_intro/
qed-.
