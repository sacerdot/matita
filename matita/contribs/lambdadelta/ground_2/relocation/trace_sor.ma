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
include "ground_2/relocation/trace.ma".

(* RELOCATION TRACE *********************************************************)

inductive sor: relation3 trace trace trace ≝
   | sor_empty: sor (◊) (◊) (◊)
   | sor_inh  : ∀cs1,cs2,cs. sor cs1 cs2 cs →
                ∀b1,b2. sor (b1 @ cs1) (b2 @ cs2) ((b1 ∨ b2) @ cs).

interpretation
   "union (trace)"
   'RUnion L1 L2 L = (sor L2 L1 L).

(* Basic properties *********************************************************)

lemma sor_sym: ∀cs1,cs2,cs. cs1 ⋓ cs2 ≡ cs → cs2 ⋓ cs1 ≡ cs.
#cs1 #cs2 #cs #H elim H -cs1 -cs2 -cs /2 width=1 by sor_inh/
qed-.
