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

include "ground_2/notation/relations/runion_3.ma".
include "ground_2/relocation/trace_isid.ma".

(* RELOCATION TRACE *********************************************************)

inductive sor: relation3 trace trace trace ≝
   | sor_empty: sor (◊) (◊) (◊)
   | sor_inh  : ∀cs1,cs2,cs. sor cs1 cs2 cs →
                ∀b1,b2. sor (b1 @ cs1) (b2 @ cs2) ((b1 ∨ b2) @ cs).

interpretation
   "union (trace)"
   'RUnion L1 L2 L = (sor L2 L1 L).

(* Basic properties *********************************************************)

lemma sor_length: ∀cs1,cs2. |cs1| = |cs2| →
                  ∃∃cs. cs2 ⋓ cs1 ≡ cs & |cs| = |cs1| & |cs| = |cs2|.
#cs1 elim cs1 -cs1
[ #cs2 #H >(length_inv_zero_sn … H) -H /2 width=4 by sor_empty, ex3_intro/
| #b1 #cs1 #IH #x #H elim (length_inv_succ_sn … H) -H
  #cs2 #b2 #H12 #H destruct elim (IH … H12) -IH -H12
  #cs #H12 #H1 #H2 @(ex3_intro … ((b1 ∨ b2) @ cs)) /2 width=1 by sor_inh/ (**) (* explicit constructor *)
]
qed-.

lemma sor_sym: ∀cs1,cs2,cs. cs1 ⋓ cs2 ≡ cs → cs2 ⋓ cs1 ≡ cs.
#cs1 #cs2 #cs #H elim H -cs1 -cs2 -cs /2 width=1 by sor_inh/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma sor_inv_length: ∀cs1,cs2,cs. cs2 ⋓ cs1 ≡ cs →
                      ∧∧ |cs1| = |cs2| & |cs| = |cs1| & |cs| = |cs2|.
#cs1 #cs2 #cs #H elim H -cs1 -cs2 -cs /2 width=1 by and3_intro/
#cs1 #cs2 #cs #_ #b1 #b2 * /2 width=1 by and3_intro/
qed-.

(* Basic forward lemmas *****************************************************)

lemma sor_fwd_isid_sn: ∀cs1,cs2,cs. cs1 ⋓ cs2 ≡ cs → 𝐈⦃cs1⦄ → 𝐈⦃cs⦄.
#cs1 #cs2 #cs #H elim H -cs1 -cs2 -cs //
#cs1 #cs2 #cs #_ #b1 #b2 #IH #H elim (isid_inv_cons … H) -H
/3 width=1 by isid_true/
qed-.

lemma sor_fwd_isid_dx: ∀cs1,cs2,cs. cs1 ⋓ cs2 ≡ cs → 𝐈⦃cs2⦄ → 𝐈⦃cs⦄.
/3 width=4 by sor_fwd_isid_sn, sor_sym/ qed-.
