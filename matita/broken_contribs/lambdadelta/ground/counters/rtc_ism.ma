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

include "ground/notation/relations/predicate_m_2.ma".
include "ground/counters/rtc.ma".

(* T-BOUND RT-TRANSITION COUNTERS *******************************************)

definition rtc_ism: relation2 (ℕ) rtc ≝ λts,c.
           ∃∃ri,rs. 〈ri,rs,𝟎,ts〉 = c.

interpretation
  "construction (t-bound rt-transition counters)"
  'PredicateM ts c = (rtc_ism ts c).

(* Basic constructions ******************************************************)

lemma rtc_ism_zz: 𝐌❨𝟎,𝟘𝟘❩.
/2 width=3 by ex1_2_intro/ qed.

lemma rtc_ism_zu: 𝐌❨𝟎,𝟙𝟘❩.
/2 width=3 by ex1_2_intro/ qed.

lemma rtc_ism_uz: 𝐌❨𝟏,𝟘𝟙❩.
/2 width=3 by ex1_2_intro/ qed.

lemma rtc_ism_eq_t_trans (n) (c1) (c2): 𝐌❨n,c1❩ → rtc_eq_t c1 c2 → 𝐌❨n,c2❩.
#n #c1 #c2 * #ri1 #rs1 #H destruct
#H elim (rtc_eq_t_inv_dx … H) -H /2 width=3 by ex1_2_intro/
qed-.

(* Basic destructions *******************************************************)

lemma rtc_ism_des_zz (n): 𝐌❨n,𝟘𝟘❩ → 𝟎 = n.
#n * #ri #rs #H destruct //
qed-.

lemma rtc_ism_des_uz (n): 𝐌❨n,𝟙𝟘❩ → 𝟎 = n.
#n * #ri #rs #H destruct //
qed-.

lemma rtc_ism_des_01 (n): 𝐌❨n,𝟘𝟙❩ → ninj (𝟏) = n.
#n * #ri #rs #H destruct //
qed-.

(* Main inversions **********************************************************)

theorem rtc_ism_inj (n1) (n2) (c): 𝐌❨n1,c❩ → 𝐌❨n2,c❩ → n1 = n2.
#n1 #n2 #c * #ri1 #rs1 #H1 * #ri2 #rs2 #H2 destruct //
qed-.

theorem rtc_ism_mono (n) (c1) (c2): 𝐌❨n,c1❩ → 𝐌❨n,c2❩ → rtc_eq_t c1 c2.
#n #c1 #c2 * #ri1 #rs1 #H1 * #ri2 #rs2 #H2 destruct //
qed-.
