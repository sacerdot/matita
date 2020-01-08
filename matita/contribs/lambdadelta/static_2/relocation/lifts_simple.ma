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

include "static_2/syntax/term_simple.ma".
include "static_2/relocation/lifts.ma".

(* GENERIC RELOCATION FOR TERMS *********************************************)

(* Forward lemmas with simple terms *****************************************)

(* Basic_2A1: includes: lift_simple_dx *)
lemma lifts_simple_dx: ∀f,T1,T2. ⇧*[f] T1 ≘ T2 → 𝐒❪T1❫ → 𝐒❪T2❫.
#f #T1 #T2 #H elim H -f -T1 -T2 //
#f #p #I #V1 #V2 #T1 #T2 #_ #_ #_ #_ #H elim (simple_inv_bind … H)
qed-.

(* Basic_2A1: includes: lift_simple_sn *)
lemma lifts_simple_sn: ∀f,T1,T2. ⇧*[f] T1 ≘ T2 → 𝐒❪T2❫ → 𝐒❪T1❫.
#f #T1 #T2 #H elim H -f -T1 -T2 //
#f #p #I #V1 #V2 #T1 #T2 #_ #_ #_ #_ #H elim (simple_inv_bind … H)
qed-.
