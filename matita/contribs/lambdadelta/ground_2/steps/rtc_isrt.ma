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

include "ground_2/notation/relations/isredtype_2.ma".
include "ground_2/steps/rtc.ma".

(* RT-TRANSITION COUNTER ****************************************************)

definition isrt: relation2 nat rtc ≝ λts,c.
                 ∃∃ri,rs. 〈ri, rs, 0, ts〉 = c.

interpretation "test for costrained rt-transition counter (rtc)"
   'IsRedType ts c = (isrt ts c).

(* Basic properties *********************************************************)

lemma isr_00: 𝐑𝐓⦃0, 𝟘𝟘⦄.
/2 width=3 by ex1_2_intro/ qed.

lemma isr_10: 𝐑𝐓⦃0, 𝟙𝟘⦄.
/2 width=3 by ex1_2_intro/ qed.

lemma isrt_01: 𝐑𝐓⦃1, 𝟘𝟙⦄.
/2 width=3 by ex1_2_intro/ qed.

(* Basic inversion properties ***********************************************)

lemma isrt_inv_00: ∀n. 𝐑𝐓⦃n, 𝟘𝟘⦄ → 0 = n.
#n * #ri #rs #H destruct //
qed-.

lemma isrt_inv_10: ∀n. 𝐑𝐓⦃n, 𝟙𝟘⦄ → 0 = n.
#n * #ri #rs #H destruct //
qed-.

lemma isrt_inv_01: ∀n. 𝐑𝐓⦃n, 𝟘𝟙⦄ → 1 = n.
#n * #ri #rs #H destruct //
qed-.

(* Main inversion properties ************************************************)

theorem isrt_mono: ∀n1,n2,c. 𝐑𝐓⦃n1, c⦄ → 𝐑𝐓⦃n2, c⦄ → n1 = n2.
#n1 #n2 #c * #ri1 #rs1 #H1 * #ri2 #rs2 #H2 destruct //
qed-.
