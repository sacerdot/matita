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

include "basic_2/syntax/term_weight.ma".
include "basic_2/relocation/lifts.ma".

(* GENERIC RELOCATION FOR TERMS *********************************************)

(* Forward lemmas with weight for terms *************************************)

(* Basic_2A1: includes: lift_fwd_tw *)
lemma lifts_fwd_tw: ∀f,T1,T2. ⬆*[f] T1 ≘ T2 → ♯{T1} = ♯{T2}.
#f #T1 #T2 #H elim H -f -T1 -T2 normalize //
qed-.
