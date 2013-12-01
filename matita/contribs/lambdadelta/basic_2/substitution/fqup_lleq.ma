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

include "basic_2/relocation/fqu_lleq.ma".
include "basic_2/substitution/fqup.ma".

(* PLUS-ITERATED SUPCLOSURE *************************************************)

(* Properties on lazy equivalence for local environments ********************)

lemma lleq_fqup_trans: ∀G1,G2,L2,K2,T,U. ⦃G1, L2, T⦄ ⊃+ ⦃G2, K2, U⦄ →
                       ∀L1. L1 ⋕[0, T] L2 →
                       ∃∃K1. ⦃G1, L1, T⦄ ⊃+ ⦃G2, K1, U⦄ & K1 ⋕[0, U] K2.
#G1 #G2 #L2 #K2 #T #U #H @(fqup_ind … H) -G2 -K2 -U
[ #G2 #K2 #U #HTU #L1 #HL12 elim (lleq_fqu_trans … HTU … HL12) -L2
  /3 width=3 by fqu_fqup, ex2_intro/
| #G #G2 #K #K2 #U #U2 #_ #HU2 #IHTU #L1 #HL12 elim (IHTU … HL12) -L2
  #K1 #HTU #HK1 elim (lleq_fqu_trans … HU2 … HK1) -K
  /3 width=5 by fqup_strap1, ex2_intro/
]
qed-.
