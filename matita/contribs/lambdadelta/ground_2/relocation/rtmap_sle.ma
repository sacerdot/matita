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

include "ground_2/relocation/rtmap_isid.ma".

(* RELOCATION MAP ***********************************************************)

coinductive sle: relation rtmap ≝
| sle_push: ∀f1,f2,g1,g2. sle f1 f2 → ↑f1 = g1 → ↑f2 = g2 → sle g1 g2
| sle_next: ∀f1,f2,g1,g2. sle f1 f2 → ⫯f1 = g1 → ⫯f2 = g2 → sle g1 g2
| sle_weak: ∀f1,f2,g1,g2. sle f1 f2 → ↑f1 = g1 → ⫯f2 = g2 → sle g1 g2
.

interpretation "inclusion (rtmap)"
   'subseteq t1 t2 = (sle t1 t2).

(* Basic inversion lemmas ***************************************************)

lemma sle_inv_xp: ∀g1,g2. g1 ⊆ g2 → ∀f2. ↑f2 = g2 →
                  ∃∃f1. f1 ⊆ f2 & ↑f1 = g1.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x2 #Hx2 destruct
[ lapply (injective_push … Hx2) -Hx2 /2 width=3 by ex2_intro/ ]
elim (discr_push_next … Hx2)
qed-.

lemma sle_inv_nx: ∀g1,g2. g1 ⊆ g2 → ∀f1. ⫯f1 = g1 →
                  ∃∃f2. f1 ⊆ f2 & ⫯f2 = g2.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x1 #Hx1 destruct
[2: lapply (injective_next … Hx1) -Hx1 /2 width=3 by ex2_intro/ ]
elim (discr_next_push … Hx1)
qed-.

lemma sle_inv_pn: ∀g1,g2. g1 ⊆ g2 → ∀f1,f2. ↑f1 = g1 → ⫯f2 = g2 → f1 ⊆ f2.
#g1 #g2 * -g1 -g2
#f1 #f2 #g1 #g2 #H #H1 #H2 #x1 #x2 #Hx1 #Hx2 destruct
[ elim (discr_next_push … Hx2)
| elim (discr_push_next … Hx1)
| lapply (injective_push … Hx1) -Hx1
  lapply (injective_next … Hx2) -Hx2 //
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma sle_inv_pp: ∀g1,g2. g1 ⊆ g2 → ∀f1,f2. ↑f1 = g1 → ↑f2 = g2 → f1 ⊆ f2.
#g1 #g2 #H #f1 #f2 #H1 #H2 elim (sle_inv_xp … H … H2) -g2
#x1 #H #Hx1 destruct lapply (injective_push … Hx1) -Hx1 //
qed-.

lemma sle_inv_nn: ∀g1,g2. g1 ⊆ g2 → ∀f1,f2.  ⫯f1 = g1 → ⫯f2 = g2 → f1 ⊆ f2.
#g1 #g2 #H #f1 #f2 #H1 #H2 elim (sle_inv_nx … H … H1) -g1
#x2 #H #Hx2 destruct lapply (injective_next … Hx2) -Hx2 //
qed-.

(* properties on isid *******************************************************)

let corec sle_isid_sn: ∀f1. 𝐈⦃f1⦄ → ∀f2. f1 ⊆ f2 ≝ ?.
#f1 * -f1
#f1 #g1 #Hf1 #H1 #f2 cases (pn_split f2) *
/3 width=5 by sle_weak, sle_push/
qed.

(* inversion lemmas on isid *************************************************)

let corec sle_inv_isid_dx: ∀f1,f2. f1 ⊆ f2 → 𝐈⦃f2⦄ → 𝐈⦃f1⦄ ≝ ?.
#f1 #f2 * -f1 -f2
#f1 #f2 #g1 #g2 #Hf * * #H
[2,3: elim (isid_inv_next … H) // ]
lapply (isid_inv_push … H ??) -H
/3 width=3 by isid_push/
qed-.
