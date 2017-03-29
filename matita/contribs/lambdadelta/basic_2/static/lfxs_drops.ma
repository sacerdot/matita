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
include "basic_2/static/frees_drops.ma".
include "basic_2/static/lfxs.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)

definition dedropable_sn: predicate (relation3 lenv term term) ≝
                          λR. ∀b,f,L1,K1. ⬇*[b, f] L1 ≡ K1 →
                          ∀K2,T. K1 ⦻*[R, T] K2 → ∀U. ⬆*[f] T ≡ U →
                          ∃∃L2. L1 ⦻*[R, U] L2 & ⬇*[b, f] L2 ≡ K2 & L1 ≡[f] L2.

definition dropable_sn: predicate (relation3 lenv term term) ≝
                        λR. ∀b,f,L1,K1. ⬇*[b, f] L1 ≡ K1 → 𝐔⦃f⦄ →
                        ∀L2,U. L1 ⦻*[R, U] L2 → ∀T. ⬆*[f] T ≡ U →
                        ∃∃K2. K1 ⦻*[R, T] K2 & ⬇*[b, f] L2 ≡ K2.

definition dropable_dx: predicate (relation3 lenv term term) ≝
                        λR. ∀L1,L2,U. L1 ⦻*[R, U] L2 →
                        ∀b,f,K2. ⬇*[b, f] L2 ≡ K2 → 𝐔⦃f⦄ → ∀T. ⬆*[f] T ≡ U →
                        ∃∃K1. ⬇*[b, f] L1 ≡ K1 & K1 ⦻*[R, T] K2.

(* Properties with generic slicing for local environments *******************)

(* Basic_2A1: includes: llpx_sn_lift_le llpx_sn_lift_ge *)
lemma lfxs_liftable_dedropable_sn: ∀R. (∀L. reflexive ? (R L)) →
                                   d_liftable2_sn R → dedropable_sn R.
#R #H1R #H2R #b #f #L1 #K1 #HLK1 #K2 #T * #f1 #Hf1 #HK12 #U #HTU
elim (frees_total L1 U) #f2 #Hf2
lapply (frees_fwd_coafter … Hf2 … HLK1 … HTU … Hf1) -HTU #Hf
elim (lexs_liftable_co_dedropable_sn … H1R … H2R … HLK1 … HK12 … Hf) -f1 -K1
/3 width=6 by cfull_lift_sn, ex3_intro, ex2_intro/
qed-.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_2A1: restricts: llpx_sn_inv_lift_le llpx_sn_inv_lift_be llpx_sn_inv_lift_ge *)
(* Basic_2A1: was: llpx_sn_drop_conf_O *)
lemma lfxs_dropable_sn: ∀R. dropable_sn R.
#R #b #f #L1 #K1 #HLK1 #H1f #L2 #U * #f2 #Hf2 #HL12 #T #HTU
elim (frees_total K1 T) #f1 #Hf1
lapply (frees_fwd_coafter … Hf2 … HLK1 … HTU … Hf1) -HTU #H2f
elim (lexs_co_dropable_sn … HLK1 … HL12 … H2f) -f2 -L1
/3 width=3 by ex2_intro/
qed-.

(* Basic_2A1: was: llpx_sn_drop_trans_O *)
(* Note: the proof might be simplified *)
lemma lfxs_dropable_dx: ∀R. dropable_dx R.
#R #L1 #L2 #U * #f2 #Hf2 #HL12 #b #f #K2 #HLK2 #H1f #T #HTU
elim (drops_isuni_ex … H1f L1) #K1 #HLK1
elim (frees_total K1 T) #f1 #Hf1
lapply (frees_fwd_coafter … Hf2 … HLK1 … HTU … Hf1) -K1 #H2f
elim (lexs_co_dropable_dx … HL12 … HLK2 … H2f) -L2
/4 width=9 by frees_inv_lifts, ex2_intro/
qed-.

(* Basic_2A1: was: llpx_sn_inv_lift_O *)
lemma lfxs_inv_lifts_bi: ∀R,L1,L2,U. L1 ⦻*[R, U] L2 →
                         ∀K1,K2,i. ⬇*[i] L1 ≡ K1 → ⬇*[i] L2 ≡ K2 →
                         ∀T. ⬆*[i] T ≡ U → K1 ⦻*[R, T] K2.
#R #L1 #L2 #U #HL12 #K1 #K2 #i #HLK1 #HLK2 #T #HTU
elim (lfxs_dropable_sn … HLK1 … HL12 … HTU) -L1 -U // #Y #HK12 #HY
lapply (drops_mono … HY … HLK2) -L2 -i #H destruct //
qed-.

lemma lfxs_inv_lref_sn: ∀R,L1,L2,i. L1 ⦻*[R, #i] L2 → ∀I,K1,V1. ⬇*[i] L1 ≡ K1.ⓑ{I}V1 →
                        ∃∃K2,V2. ⬇*[i] L2 ≡ K2.ⓑ{I}V2 & K1 ⦻*[R, V1] K2 & R K1 V1 V2.
#R #L1 #L2 #i #HL12 #I #K1 #V1 #HLK1 elim (lfxs_dropable_sn … HLK1 … HL12 (#0)) -HLK1 -HL12 //
#Y #HY #HLK2 elim (lfxs_inv_zero_pair_sn … HY) -HY
#K2 #V2 #HK12 #HV12 #H destruct /2 width=5 by ex3_2_intro/
qed-.

lemma lfxs_inv_lref_dx: ∀R,L1,L2,i. L1 ⦻*[R, #i] L2 → ∀I,K2,V2. ⬇*[i] L2 ≡ K2.ⓑ{I}V2 →
                        ∃∃K1,V1. ⬇*[i] L1 ≡ K1.ⓑ{I}V1 & K1 ⦻*[R, V1] K2 & R K1 V1 V2.
#R #L1 #L2 #i #HL12 #I #K2 #V2 #HLK2 elim (lfxs_dropable_dx … HL12 … HLK2 … (#0)) -HLK2 -HL12 //
#Y #HLK1 #HY elim (lfxs_inv_zero_pair_dx … HY) -HY
#K1 #V1 #HK12 #HV12 #H destruct /2 width=5 by ex3_2_intro/
qed-.
