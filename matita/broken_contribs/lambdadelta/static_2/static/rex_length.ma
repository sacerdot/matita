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

include "static_2/relocation/sex_length.ma".
include "static_2/static/rex_drops.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)

(* Forward lemmas with length for local environments ************************)

(* Basic_2A1: uses: llpx_sn_fwd_length *)
lemma rex_fwd_length (R): ∀L1,L2,T. L1 ⪤[R,T] L2 → |L1| = |L2|.
#R #L1 #L2 #T * /2 width=4 by sex_fwd_length/
qed-.

(* Properties with length for local environments ****************************)

(* Basic_2A1: uses: llpx_sn_sort *)
lemma rex_sort_length (R): ∀L1,L2. |L1| = |L2| → ∀s. L1 ⪤[R,⋆s] L2.
#R #L1 elim L1 -L1
[ #Y #H #s >(length_inv_zero_sn … H) -H //
| #K1 #I1 #IH #Y #H #s
  elim (length_inv_succ_sn … H) -H #I2 #K2 #HK12 #H destruct
  /3 width=1 by rex_sort/
]
qed.

(* Basic_2A1: uses: llpx_sn_gref *)
lemma rex_gref_length (R): ∀L1,L2. |L1| = |L2| → ∀l. L1 ⪤[R,§l] L2.
#R #L1 elim L1 -L1
[ #Y #H #s >(length_inv_zero_sn … H) -H //
| #K1 #I1 #IH #Y #H #s
  elim (length_inv_succ_sn … H) -H #I2 #K2 #HK12 #H destruct
  /3 width=1 by rex_gref/
]
qed.

lemma rex_unit_length (R): ∀L1,L2. |L1| = |L2| → ∀I. L1.ⓤ[I] ⪤[R,#0] L2.ⓤ[I].
/3 width=3 by rex_unit, sex_length_isid/ qed.

(* Basic_2A1: uses: llpx_sn_lift_le llpx_sn_lift_ge *)
lemma rex_lifts_bi (R):
      d_liftable2_sn … lifts R →
      ∀L1,L2. |L1| = |L2| → ∀K1,K2,T. K1 ⪤[R,T] K2 →
      ∀b,f. ⇩*[b,f] L1 ≘ K1 → ⇩*[b,f] L2 ≘ K2 →
      ∀U. ⇧*[f] T ≘ U → L1 ⪤[R,U] L2.
#R #HR #L1 #L2 #HL12 #K1 #K2 #T * #f1 #Hf1 #HK12 #b #f #HLK1 #HLK2 #U #HTU
elim (frees_total L1 U) #f2 #Hf2
lapply (frees_fwd_coafter … Hf2 … HLK1 … HTU … Hf1) -HTU #Hf
/4 width=12 by sex_length_cfull, sex_liftable_co_dedropable_bi, cext2_d_liftable2_sn, cfull_lift_sn, ex2_intro/
qed-.

(* Inversion lemmas with length for local environment ***********************)

lemma rex_inv_zero_length (R):
      ∀Y1,Y2. Y1 ⪤[R,#0] Y2 →
      ∨∨ ∧∧ Y1 = ⋆ & Y2 = ⋆
       | ∃∃I,L1,L2,V1,V2. L1 ⪤[R,V1] L2 & R L1 V1 V2 &
           Y1 = L1.ⓑ[I]V1 & Y2 = L2.ⓑ[I]V2
       | ∃∃I,L1,L2. |L1| = |L2| & Y1 = L1.ⓤ[I] & Y2 = L2.ⓤ[I].
#R #Y1 #Y2 #H elim (rex_inv_zero … H) -H *
/4 width=9 by sex_fwd_length, ex4_5_intro, ex3_3_intro, or3_intro2, or3_intro1, or3_intro0, conj/
qed-.
