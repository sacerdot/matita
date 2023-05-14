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

include "ground/notation/relations/predicate_t_2.ma".
include "ground/counters/rtc.ma".

(* T-TRANSITION COUNTERS ****************************************************)

definition rtc_ist: relation2 (ℕ) rtc ≝
           λts,c. 〈𝟎,𝟎,𝟎,ts〉 = c.

interpretation
  "construction (t-transition counters)"
  'PredicateT ts c = (rtc_ist ts c).

(* Basic constructions ******************************************************)

lemma rtc_ist_zz: 𝐓❨𝟎,𝟘𝟘❩.
// qed.

lemma rtc_ist_zu: 𝐓❨𝟏,𝟘𝟙❩.
// qed.

(* Basic inversions *********************************************************)

lemma rtc_ist_inv_zz (n): 𝐓❨n,𝟘𝟘❩ → 𝟎 = n.
#n #H destruct //
qed-.

lemma rtc_ist_inv_zu (n): 𝐓❨n,𝟘𝟙❩ → ninj (𝟏) = n.
#n #H destruct //
qed-.

lemma rtc_ist_inv_uz (n): 𝐓❨n,𝟙𝟘❩ → ⊥.
#h #H destruct
qed-.

(* Main inversions **********************************************************)

theorem rtc_ist_inj (n1) (n2) (c): 𝐓❨n1,c❩ → 𝐓❨n2,c❩ → n1 = n2.
#n1 #n2 #c #H1 #H2 destruct //
qed-.

theorem rtc_ist_mono (n) (c1) (c2): 𝐓❨n,c1❩ → 𝐓❨n,c2❩ → c1 = c2.
#n #c1 #c2 #H1 #H2 destruct //
qed-.
