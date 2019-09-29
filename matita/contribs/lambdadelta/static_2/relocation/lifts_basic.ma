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

include "ground_2/relocation/rtmap_basic_after.ma".
include "static_2/notation/relations/rlift_4.ma".
include "static_2/relocation/lifts.ma".

(* GENERIC RELOCATION FOR TERMS *********************************************)

interpretation "basic relocation (term)"
   'RLift m n T1 T2 = (lifts (basic m n) T1 T2).

(* Properties with basic relocation *****************************************)

lemma lifts_lref_lt (m,n,i): i < m → ⇧[m,n] #i ≘ #i.
/3 width=1 by lifts_lref, at_basic_lt/ qed.

lemma lifts_lref_ge (m,n,i): m ≤ i → ⇧[m,n] #i ≘ #(n+i).
/3 width=1 by lifts_lref, at_basic_ge/ qed.

lemma lifts_lref_ge_minus (m,n,i): n+m ≤ i → ⇧[m,n] #(i-n) ≘ #i.
#m #n #i #Hi
>(plus_minus_m_m i n) in ⊢ (???%);
/3 width=2 by lifts_lref_ge, le_plus_to_minus_l, le_plus_b/
qed.
