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

include "basic_2/substitution/fqus_alt.ma".
include "basic_2/substitution/lleq_ext.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

(* Properties on supclosure and derivatives *********************************)

lemma lleq_fqu_trans: ∀G1,G2,L2,K2,T,U. ⦃G1, L2, T⦄ ⊃ ⦃G2, K2, U⦄ →
                      ∀L1. L1 ⋕[T, 0] L2 →
                      ∃∃K1. ⦃G1, L1, T⦄ ⊃ ⦃G2, K1, U⦄ & K1 ⋕[U, 0] K2.
#G1 #G2 #L2 #K2 #T #U #H elim H -G1 -G2 -L2 -K2 -T -U
[ #I #G #L2 #V #L1 #H elim (lleq_inv_lref_ge_dx … H … I L2 V) -H //
  #I1 #K1 #H1 #H2 lapply (ldrop_inv_O2 … H1) -H1
  #H destruct /2 width=3 by fqu_lref_O, ex2_intro/
| * [ #a ] #I #G #L2 #V #T #L1 #H
  [ elim (lleq_inv_bind … H)
  | elim (lleq_inv_flat … H)
  ] -H
  /2 width=3 by fqu_pair_sn, ex2_intro/
| #a #I #G #L2 #V #T #L1 #H elim (lleq_inv_bind_O … H) -H
  #H3 #H4 /2 width=3 by fqu_bind_dx, ex2_intro/
| #I #G #L2 #V #T #L1 #H elim (lleq_inv_flat … H) -H
  /2 width=3 by fqu_flat_dx, ex2_intro/
| #G #L2 #K2 #T #U #e #HLK2 #HTU #L1 #HL12
  elim (ldrop_O1_le (e+1) L1)
  [ /3 width=12 by fqu_drop, lleq_inv_lift_le, ex2_intro/
  | lapply (ldrop_fwd_length_le2 … HLK2) -K2
    lapply (lleq_fwd_length … HL12) -T -U //
  ]
]
qed-.

lemma lleq_fquq_trans: ∀G1,G2,L2,K2,T,U. ⦃G1, L2, T⦄ ⊃⸮ ⦃G2, K2, U⦄ →
                       ∀L1. L1 ⋕[T, 0] L2 →
                       ∃∃K1. ⦃G1, L1, T⦄ ⊃⸮ ⦃G2, K1, U⦄ & K1 ⋕[U, 0] K2.
#G1 #G2 #L2 #K2 #T #U #H #L1 #HL12 elim(fquq_inv_gen … H) -H
[ #H elim (lleq_fqu_trans … H … HL12) -L2 /3 width=3 by fqu_fquq, ex2_intro/
| * #HG #HL #HT destruct /2 width=3 by ex2_intro/
]
qed-.

lemma lleq_fqup_trans: ∀G1,G2,L2,K2,T,U. ⦃G1, L2, T⦄ ⊃+ ⦃G2, K2, U⦄ →
                       ∀L1. L1 ⋕[T, 0] L2 →
                       ∃∃K1. ⦃G1, L1, T⦄ ⊃+ ⦃G2, K1, U⦄ & K1 ⋕[U, 0] K2.
#G1 #G2 #L2 #K2 #T #U #H @(fqup_ind … H) -G2 -K2 -U
[ #G2 #K2 #U #HTU #L1 #HL12 elim (lleq_fqu_trans … HTU … HL12) -L2
  /3 width=3 by fqu_fqup, ex2_intro/
| #G #G2 #K #K2 #U #U2 #_ #HU2 #IHTU #L1 #HL12 elim (IHTU … HL12) -L2
  #K1 #HTU #HK1 elim (lleq_fqu_trans … HU2 … HK1) -K
  /3 width=5 by fqup_strap1, ex2_intro/
]
qed-.

lemma lleq_fqus_trans: ∀G1,G2,L2,K2,T,U. ⦃G1, L2, T⦄ ⊃* ⦃G2, K2, U⦄ →
                       ∀L1. L1 ⋕[T, 0] L2 →
                       ∃∃K1. ⦃G1, L1, T⦄ ⊃* ⦃G2, K1, U⦄ & K1 ⋕[U, 0] K2.
#G1 #G2 #L2 #K2 #T #U #H #L1 #HL12 elim(fqus_inv_gen … H) -H
[ #H elim (lleq_fqup_trans … H … HL12) -L2 /3 width=3 by fqup_fqus, ex2_intro/
| * #HG #HL #HT destruct /2 width=3 by ex2_intro/
]
qed-.
