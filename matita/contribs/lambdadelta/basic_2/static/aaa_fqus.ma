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

include "basic_2/multiple/fqus_alt.ma".
include "basic_2/static/aaa_lift.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Properties on supclosure *************************************************)

lemma aaa_fqu_conf: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                    ∀A1. ⦃G1, L1⦄ ⊢ T1 ⁝ A1 → ∃A2. ⦃G2, L2⦄ ⊢ T2 ⁝ A2.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I #G #L #T #A #H elim (aaa_inv_lref … H) -H
  #J #K #V #H #HA lapply (drop_inv_O2 … H) -H
  #H destruct /2 width=2 by ex_intro/
| * [ #a ] * #G #L #V #T #X #H
  [ elim (aaa_inv_abbr … H)
  | elim (aaa_inv_abst … H)
  | elim (aaa_inv_appl … H)
  | elim (aaa_inv_cast … H)
  ] -H /2 width=2 by ex_intro/
| #a * #G #L #V #T #X #H
  [ elim (aaa_inv_abbr … H)
  | elim (aaa_inv_abst … H)
  ] -H /2 width=2 by ex_intro/
| * #G #L #V #T #X #H
  [ elim (aaa_inv_appl … H)
  | elim (aaa_inv_cast … H)
  ] -H /2 width=2 by ex_intro/
| /3 width=9 by aaa_inv_lift, ex_intro/
]
qed-.

lemma aaa_fquq_conf: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                     ∀A1. ⦃G1, L1⦄ ⊢ T1 ⁝ A1 → ∃A2. ⦃G2, L2⦄ ⊢ T2 ⁝ A2.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim(fquq_inv_gen … H) -H /2 width=6 by aaa_fqu_conf/
* #H1 #H2 #H3 destruct /2 width=2 by ex_intro/
qed-.

lemma aaa_fqup_conf: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                     ∀A1. ⦃G1, L1⦄ ⊢ T1 ⁝ A1 → ∃A2. ⦃G2, L2⦄ ⊢ T2 ⁝ A2.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
[2: #G #G2 #L #L2 #T #T2 #_ #H2 #IH1 #A #HA elim (IH1 … HA) -IH1 -A ]
/2 width=6 by aaa_fqu_conf/
qed-.

lemma aaa_fqus_conf: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                     ∀A1. ⦃G1, L1⦄ ⊢ T1 ⁝ A1 → ∃A2. ⦃G2, L2⦄ ⊢ T2 ⁝ A2.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim(fqus_inv_gen … H) -H /2 width=6 by aaa_fqup_conf/
* #H1 #H2 #H3 destruct /2 width=2 by ex_intro/
qed-.
