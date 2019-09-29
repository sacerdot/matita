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

include "static_2/relocation/drops_sex.ma".

(* GENERIC SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Properties with syntactic equivalence for selected local environments ****)

lemma seq_co_dedropable_sn: co_dedropable_sn seq.
@sex_liftable_co_dedropable_sn
/2 width=6 by cfull_lift_sn, ceq_lift_sn/ qed-.

lemma seq_co_dropable_sn: co_dropable_sn seq.
@sex_co_dropable_sn qed-.

lemma seq_co_dropable_dx: co_dropable_dx seq.
@sex_co_dropable_dx qed-.

(* Basic_2A1: includes: lreq_drop_trans_be *)
lemma seq_drops_trans_next: ∀f2,L1,L2. L1 ≡[f2] L2 →
                            ∀b,f,I,K2. ⇩*[b,f] L2 ≘ K2.ⓘ{I} → 𝐔⦃f⦄ →
                            ∀f1. f ~⊚ ↑f1 ≘ f2 →
                            ∃∃K1. ⇩*[b,f] L1 ≘ K1.ⓘ{I} & K1 ≡[f1] K2.
#f2 #L1 #L2 #HL12 #b #f #I2 #K2 #HLK2 #Hf #f1 #Hf2
elim (sex_drops_trans_next … HL12 … HLK2 Hf … Hf2) -f2 -L2 -Hf
#I1 #K1 #HLK1 #HK12 #H <(ceq_ext_inv_eq … H) -I2
/2 width=3 by ex2_intro/
qed-.

(* Basic_2A1: includes: lreq_drop_conf_be *)
lemma seq_drops_conf_next: ∀f2,L1,L2. L1 ≡[f2] L2 →
                           ∀b,f,I,K1. ⇩*[b,f] L1 ≘ K1.ⓘ{I} → 𝐔⦃f⦄ →
                           ∀f1. f ~⊚ ↑f1 ≘ f2 →
                           ∃∃K2. ⇩*[b,f] L2 ≘ K2.ⓘ{I} & K1 ≡[f1] K2.
#f2 #L1 #L2 #HL12 #b #f #I1 #K1 #HLK1 #Hf #f1 #Hf2
elim (seq_drops_trans_next … (seq_sym … HL12) … HLK1 … Hf2) // -f2 -L1 -Hf
/3 width=3 by seq_sym, ex2_intro/
qed-.

lemma drops_seq_trans_next: ∀f1,K1,K2. K1 ≡[f1] K2 →
                            ∀b,f,I,L1. ⇩*[b,f] L1.ⓘ{I} ≘ K1 →
                            ∀f2. f ~⊚ f1 ≘ ↑f2 →
                            ∃∃L2. ⇩*[b,f] L2.ⓘ{I} ≘ K2 & L1 ≡[f2] L2 & L1.ⓘ{I} ≡[f] L2.ⓘ{I}.
#f1 #K1 #K2 #HK12 #b #f #I1 #L1 #HLK1 #f2 #Hf2
elim (drops_sex_trans_next … HK12 … HLK1 … Hf2) -f1 -K1
/2 width=6 by cfull_lift_sn, ceq_lift_sn/
#I2 #L2 #HLK2 #HL12 #H >(ceq_ext_inv_eq … H) -I1
/2 width=4 by ex3_intro/
qed-.
