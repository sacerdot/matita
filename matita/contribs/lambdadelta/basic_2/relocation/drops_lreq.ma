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

include "basic_2/relocation/drops_ceq.ma".
include "basic_2/relocation/drops_lexs.ma".

(* GENERIC SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Properties with ranged equivalence for local environments ****************)

lemma lreq_dedropable: dedropable_sn lreq.
@lexs_liftable_dedropable
/2 width=6 by cfull_lift, ceq_lift, cfull_refl, ceq_refl/
qed-.

lemma lreq_dropable: ∀RN,RP. dropable_dx (lexs RN RP).
@lexs_dropable qed-.

(* Basic_2A1: includes: lreq_drop_trans_be *)
lemma lreq_drops_trans_next: ∀f2,L1,L2. L1 ≡[f2] L2 →
                             ∀b,f,I,K2,V. ⬇*[b,f] L2 ≡ K2.ⓑ{I}V → 𝐔⦃f⦄ →
                             ∀f1. f ⊚ ⫯f1 ≡ f2 →
                             ∃∃K1. ⬇*[b,f] L1 ≡ K1.ⓑ{I}V & K1 ≡[f1] K2.
#f2 #L1 #L2 #HL12 #b #f #I #K1 #V #HLK1 #Hf #f1 #Hf2
elim (lexs_drops_trans_next … HL12 … HLK1 Hf … Hf2) -f2 -L2 -Hf
/2 width=3 by ex2_intro/
qed-.

(* Basic_2A1: includes: lreq_drop_conf_be *)
lemma lreq_drops_conf_next: ∀f2,L1,L2. L1 ≡[f2] L2 →
                            ∀b,f,I,K1,V. ⬇*[b,f] L1 ≡ K1.ⓑ{I}V → 𝐔⦃f⦄ →
                            ∀f1. f ⊚ ⫯f1 ≡ f2 →
                            ∃∃K2. ⬇*[b,f] L2 ≡ K2.ⓑ{I}V & K1 ≡[f1] K2.
#f2 #L1 #L2 #HL12 #b #f #I #K1 #V #HLK1 #Hf #f1 #Hf2
elim (lreq_drops_trans_next … (lreq_sym … HL12) … HLK1 … Hf2) // -f2 -L1 -Hf
/3 width=3 by lreq_sym, ex2_intro/
qed-.

lemma drops_lreq_trans_next: ∀f1,K1,K2. K1 ≡[f1] K2 →
                             ∀b,f,I,L1,V. ⬇*[b,f] L1.ⓑ{I}V ≡ K1 →
                             ∀f2. f ⊚ f1 ≡ ⫯f2 →
                             ∃∃L2. ⬇*[b,f] L2.ⓑ{I}V ≡ K2 & L1 ≡[f2] L2 & L1.ⓑ{I}V≡[f]L2.ⓑ{I}V.
#f1 #K1 #K2 #HK12 #b #f #I #L1 #V #HLK1 #f2 #Hf2
elim (drops_lexs_trans_next … HK12 … HLK1 … Hf2) -f1 -K1
/2 width=6 by cfull_lift, ceq_lift, cfull_refl, ceq_refl, ex3_intro/
qed-.
