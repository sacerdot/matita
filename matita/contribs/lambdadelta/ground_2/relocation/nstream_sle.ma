(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.tcs.unibo.it                            *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "ground_2/relocation/nstream_lift.ma".

(* RELOCATION N-STREAM ******************************************************)

coinductive sle: relation rtmap ≝
| sle_next: ∀f1,f2,g1,g2. sle f1 f2 → g1 = ↑f1 → g2 = ↑f2 → sle g1 g2
| sle_push: ∀f1,f2,g1,g2. sle f1 f2 → g1 = ⫯f1 → g2 = ⫯f2 → sle g1 g2
| sle_weak: ∀f1,f2,g1,g2. sle f1 f2 → g1 = ↑f1 → g2 = ⫯f2 → sle g1 g2
.

interpretation "inclusion (nstream)"
   'subseteq t1 t2 = (sle t1 t2).

(* Basic inversion lemmas ***************************************************)

fact sle_inv_xO_aux: ∀g1,g2. g1 ⊆ g2 → ∀f2. g2 = ↑f2 →
                     ∃∃f1. f1 ⊆ f2 & g1 = ↑f1.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x2 #Hx2 destruct
[ lapply (injective_push … Hx2) -Hx2 /2 width=3 by ex2_intro/ ]
elim (discr_next_push … Hx2)
qed-.

lemma sle_inv_xO: ∀g1,f2. g1 ⊆ ↑f2 → ∃∃f1. f1 ⊆ f2 & g1 = ↑f1.
/2 width=3 by sle_inv_xO_aux/ qed-.

fact sle_inv_Sx_aux: ∀g1,g2. g1 ⊆ g2 → ∀f1. g1 = ⫯f1 →
                     ∃∃f2. f1 ⊆ f2 & g2 = ⫯f2.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x1 #Hx1 destruct
[2: lapply (injective_next … Hx1) -Hx1 /2 width=3 by ex2_intro/ ]
elim (discr_push_next … Hx1)
qed-.

lemma sle_inv_Sx: ∀f1,g2. ⫯f1 ⊆ g2 → ∃∃f2. f1 ⊆ f2 & g2 = ⫯f2.
/2 width=3 by sle_inv_Sx_aux/ qed-.

fact sle_inv_OS_aux: ∀g1,g2. g1 ⊆ g2 → ∀f1,f2. g1 = ↑f1 → g2 = ⫯f2 → f1 ⊆ f2.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x1 #x2 #Hx1 #Hx2 destruct
[ elim (discr_push_next … Hx2)
| elim (discr_next_push … Hx1)
| lapply (injective_push … Hx1) -Hx1
  lapply (injective_next … Hx2) -Hx2 //
]
qed-.

lemma sle_inv_OS: ∀f1,f2. ↑f1 ⊆ ⫯f2 → f1 ⊆ f2.
/2 width=5 by sle_inv_OS_aux/ qed-.

(* Advanced inversion lemmas ************************************************)

fact sle_inv_OO_aux: ∀g1,g2. g1 ⊆ g2 → ∀f1,f2. g1 = ↑f1 → g2 = ↑f2 → f1 ⊆ f2.
#g1 #g2 #H #f1 #f2 #H1 #H2 elim (sle_inv_xO_aux … H … H2) -g2
#x1 #H #Hx1 destruct lapply (injective_push … Hx1) -Hx1 //
qed-.

fact sle_inv_SS_aux: ∀g1,g2. g1 ⊆ g2 → ∀f1,f2. g1 = ⫯f1 → g2 = ⫯f2 → f1 ⊆ f2.
#g1 #g2 #H #f1 #f2 #H1 #H2 elim (sle_inv_Sx_aux … H … H1) -g1
#x2 #H #Hx2 destruct lapply (injective_next … Hx2) -Hx2 //
qed-.
