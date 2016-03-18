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

include "ground_2/notation/relations/isuniform_1.ma".
include "ground_2/relocation/rtmap_isid.ma".

(* RELOCATION MAP ***********************************************************)

inductive isuni: predicate rtmap ≝
| isuni_isid: ∀f. 𝐈⦃f⦄ → isuni f
| isuni_next: ∀f. isuni f → ∀g. ⫯f = g → isuni g
.

interpretation "test for uniformity (rtmap)"
   'IsUniform f = (isuni f).

(* Basic inversion lemmas ***************************************************)

lemma isuni_inv_push: ∀g. 𝐔⦃g⦄ → ∀f. ↑f = g → 𝐈⦃f⦄.
#g * -g /2 width=3 by isid_inv_push/
#f #_ #g #H #x #Hx destruct elim (discr_push_next … Hx)
qed-.

lemma isuni_inv_next: ∀g. 𝐔⦃g⦄ → ∀f. ⫯f = g → 𝐔⦃f⦄.
#g * -g #f #Hf
[ #x #Hx elim (isid_inv_next … Hf … Hx)
| #g #H #x #Hx destruct /2 width=1 by injective_push/
]
qed-.

(* basic forward lemmas *****************************************************)

lemma isuni_fwd_push: ∀g. 𝐔⦃g⦄ → ∀f. ↑f = g → 𝐔⦃f⦄.
/3 width=3 by isuni_inv_push, isuni_isid/ qed-.
