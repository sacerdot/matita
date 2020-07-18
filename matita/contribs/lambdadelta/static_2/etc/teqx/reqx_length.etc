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

include "static_2/relocation/lifts_teqx.ma".
include "static_2/static/rex_length.ma".
include "static_2/static/rex_fsle.ma".
include "static_2/static/reqx.ma".

(* SORT-IRRELEVANT EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ***)

(* Advanved properties with free variables inclusion ************************)

lemma reqx_fsge_comp: rex_fsge_compatible cdeq.
#L1 #L2 #T * #f1 #Hf1 #HL12
lapply (frees_reqx_conf … Hf1 … HL12)
lapply (sex_fwd_length … HL12)
/3 width=8 by lveq_length_eq, ex4_4_intro/ (**) (* full auto fails *)
qed-.

(* Properties with length for local environments ****************************)

(* Basic_2A1: uses: lleq_sort *)
lemma reqx_sort_length: ∀L1,L2. |L1| = |L2| → ∀s. L1 ≛[⋆s] L2.
/2 width=1 by rex_sort_length/ qed.

(* Basic_2A1: uses: lleq_gref *)
lemma reqx_gref_length: ∀L1,L2. |L1| = |L2| → ∀l. L1 ≛[§l] L2.
/2 width=1 by rex_gref_length/ qed.

lemma reqx_unit_length: ∀L1,L2. |L1| = |L2| →
                        ∀I. L1.ⓤ[I] ≛[#0] L2.ⓤ[I].
/2 width=1 by rex_unit_length/ qed.

(* Basic_2A1: uses: lleq_lift_le lleq_lift_ge *)
lemma reqx_lifts_bi: ∀L1,L2. |L1| = |L2| → ∀K1,K2,T. K1 ≛[T] K2 →
                     ∀b,f. ⇩*[b,f] L1 ≘ K1 → ⇩*[b,f] L2 ≘ K2 →
                     ∀U. ⇧*[f] T ≘ U → L1 ≛[U] L2.
/3 width=9 by rex_lifts_bi, teqx_lifts_sn/ qed-.

(* Forward lemmas with length for local environments ************************)

(* Basic_2A1: lleq_fwd_length *)
lemma reqx_fwd_length: ∀L1,L2. ∀T:term. L1 ≛[T] L2 → |L1| = |L2|.
/2 width=3 by rex_fwd_length/ qed-.
