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

include "ground_2/notation/relations/istype_2.ma".
include "ground_2/steps/rtc.ma".

(* T-TRANSITION COUNTER *****************************************************)

definition ist: relation2 nat rtc ≝
           λts,c. 〈0,0,0,ts〉 = c.

interpretation "test for t-transition counter (rtc)"
   'IsType ts c = (ist ts c).

(* Basic properties *********************************************************)

lemma isr_00: 𝐓❪0,𝟘𝟘❫.
// qed.

lemma ist_01: 𝐓❪1,𝟘𝟙❫.
// qed.

(* Basic inversion properties ***********************************************)

lemma ist_inv_00: ∀n. 𝐓❪n,𝟘𝟘❫ → 0 = n.
#n #H destruct //
qed-.

lemma ist_inv_01: ∀n. 𝐓❪n,𝟘𝟙❫ → 1 = n.
#n #H destruct //
qed-.

lemma ist_inv_10: ∀n. 𝐓❪n,𝟙𝟘❫ → ⊥.
#h #H destruct
qed-.

(* Main inversion properties ************************************************)

theorem ist_inj: ∀n1,n2,c. 𝐓❪n1,c❫ → 𝐓❪n2,c❫ → n1 = n2.
#n1 #n2 #c #H1 #H2 destruct //
qed-.

theorem ist_mono: ∀n,c1,c2. 𝐓❪n,c1❫ → 𝐓❪n,c2❫ → c1 = c2.
#n #c1 #c2 #H1 #H2 destruct //
qed-.
