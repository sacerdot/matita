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

include "basic_2/substitution/fqup_lleq.ma".
include "basic_2/substitution/fqus_alt.ma".

(* STAR-ITERATED SUPCLOSURE *************************************************)

(* Properties on lazy equivalence for local environments ********************)

lemma lleq_fqus_trans: ∀G1,G2,L2,K2,T,U. ⦃G1, L2, T⦄ ⊃* ⦃G2, K2, U⦄ →
                       ∀L1. L1 ⋕[0, T] L2 →
                       ∃∃K1. ⦃G1, L1, T⦄ ⊃* ⦃G2, K1, U⦄ & K1 ⋕[0, U] K2.
#G1 #G2 #L2 #K2 #T #U #H #L1 #HL12 elim(fqus_inv_gen … H) -H
[ #H elim (lleq_fqup_trans … H … HL12) -L2 /3 width=3 by fqup_fqus, ex2_intro/
| * #HG #HL #HT destruct /2 width=3 by ex2_intro/
]
qed-.