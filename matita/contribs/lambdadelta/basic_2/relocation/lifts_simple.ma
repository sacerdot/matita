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

include "basic_2/grammar/term_simple.ma".
include "basic_2/relocation/lifts.ma".

(* GENERIC RELOCATION FOR TERMS *********************************************)

(* Forward lemmas on simple terms *******************************************)

(* Basic_2A1: includes: lift_simple_dx *)
lemma lifts_simple_dx: ∀T1,T2,f. ⬆*[f] T1 ≡ T2 → 𝐒⦃T1⦄ → 𝐒⦃T2⦄.
#T1 #T2 #f #H elim H -T1 -T2 -f //
#p #I #V1 #V2 #T1 #T2 #f #_ #_ #_ #_ #H elim (simple_inv_bind … H)
qed-.

(* Basic_2A1: includes: lift_simple_sn *)
lemma lifts_simple_sn: ∀T1,T2,f. ⬆*[f] T1 ≡ T2 → 𝐒⦃T2⦄ → 𝐒⦃T1⦄.
#T1 #T2 #f #H elim H -T1 -T2 -f //
#p #I #V1 #V2 #T1 #T2 #f #_ #_ #_ #_ #H elim (simple_inv_bind … H)
qed-.
