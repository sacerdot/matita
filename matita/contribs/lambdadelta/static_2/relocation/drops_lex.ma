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

include "static_2/relocation/lex.ma".
include "static_2/relocation/drops_cext2.ma".
include "static_2/relocation/drops_sex.ma".

(* GENERIC SLICING FOR LOCAL ENVIRONMENTS ***********************************)

definition dedropable_sn: predicate … ≝
                          λR. ∀b,f,L1,K1. ⇩*[b,f] L1 ≘ K1 → ∀K2. K1 ⪤[R] K2 →
                          ∃∃L2. L1 ⪤[R] L2 & ⇩*[b,f] L2 ≘ K2 & L1 ≡[f] L2.

definition dropable_sn: predicate … ≝
                        λR. ∀b,f,L1,K1. ⇩*[b,f] L1 ≘ K1 → 𝐔⦃f⦄ → ∀L2. L1 ⪤[R] L2 →
                        ∃∃K2. K1 ⪤[R] K2 & ⇩*[b,f] L2 ≘ K2.

definition dropable_dx: predicate … ≝
                        λR. ∀L1,L2. L1 ⪤[R] L2 → ∀b,f,K2. ⇩*[b,f] L2 ≘ K2 → 𝐔⦃f⦄ →
                        ∃∃K1. ⇩*[b,f] L1 ≘ K1 & K1 ⪤[R] K2.

(* Properties with generic extension ****************************************)

(* Basic_2A1: was: lpx_sn_liftable_dedropable *)
lemma lex_liftable_dedropable_sn (R): c_reflexive … R →
                                      d_liftable2_sn … lifts R → dedropable_sn R.
#R #H1R #H2R #b #f #L1 #K1 #HLK1 #K2 * #f1 #Hf1 #HK12
elim (sex_liftable_co_dedropable_sn … HLK1 … HK12) -K1
/3 width=6 by cext2_d_liftable2_sn, cfull_lift_sn, ext2_refl, coafter_isid_dx, ex3_intro, ex2_intro/
qed-.

(* Inversion lemmas with generic extension **********************************)

(* Basic_2A1: was: lpx_sn_deliftable_dropable *)
lemma lex_dropable_sn (R): dropable_sn R.
#R #b #f #L1 #K1 #HLK1 #H1f #L2 * #f2 #Hf2 #HL12
elim (sex_co_dropable_sn … HLK1 … HL12) -L1
/3 width=3 by coafter_isid_dx, ex2_intro/
qed-.

(* Basic_2A1: was: lpx_sn_dropable *)
lemma lex_dropable_dx (R): dropable_dx R.
#R #L1 #L2 * #f2 #Hf2 #HL12 #b #f #K2 #HLK2 #Hf
elim (sex_co_dropable_dx … HL12 … HLK2) -L2
/3 width=5 by coafter_isid_dx, ex2_intro/
qed-.

(* Basic_2A1: includes: lpx_sn_drop_conf *)
lemma lex_drops_conf_pair (R): ∀L1,L2. L1 ⪤[R] L2 →
                               ∀b,f,I,K1,V1. ⇩*[b,f] L1 ≘ K1.ⓑ{I}V1 → 𝐔⦃f⦄ →
                               ∃∃K2,V2. ⇩*[b,f] L2 ≘ K2.ⓑ{I}V2 & K1 ⪤[R] K2 & R K1 V1 V2.
#R #L1 #L2 * #f2 #Hf2 #HL12 #b #f #I #K1 #V1 #HLK1 #Hf
elim (sex_drops_conf_push … HL12 … HLK1 Hf f2) -L1 -Hf
[ #Z2 #K2 #HLK2 #HK12 #H
  elim (ext2_inv_pair_sn … H) -H #V2 #HV12 #H destruct
  /3 width=5 by ex3_2_intro, ex2_intro/
| /3 width=3 by coafter_isid_dx, isid_push/
]
qed-.

(* Basic_2A1: includes: lpx_sn_drop_trans *)
lemma lex_drops_trans_pair (R): ∀L1,L2. L1 ⪤[R] L2 →
                                ∀b,f,I,K2,V2. ⇩*[b,f] L2 ≘ K2.ⓑ{I}V2 → 𝐔⦃f⦄ →
                                ∃∃K1,V1. ⇩*[b,f] L1 ≘ K1.ⓑ{I}V1 & K1 ⪤[R] K2 & R K1 V1 V2.
#R #L1 #L2 * #f2 #Hf2 #HL12 #b #f #I #K2 #V2 #HLK2 #Hf
elim (sex_drops_trans_push … HL12 … HLK2 Hf f2) -L2 -Hf
[ #Z1 #K1 #HLK1 #HK12 #H
  elim (ext2_inv_pair_dx … H) -H #V1 #HV12 #H destruct
  /3 width=5 by ex3_2_intro, ex2_intro/
| /3 width=3 by coafter_isid_dx, isid_push/
]
qed-.
