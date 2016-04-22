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

include "basic_2/relocation/drops.ma".
include "basic_2/rt_transition/cpg.ma".

(* CONTEXT-SENSITIVE GENERIC PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Properties with length for local environments ****************************)

lemma cpg_inv_lref1_ge: ∀h,r,G,L,T2,i. ⦃G, L⦄ ⊢ #i ➡[h, r] T2 → |L| ≤ i → T2 = #i.
#h #r #G #L #T2 #i #H elim (cpg_inv_lref1 … H) -H // *
#I #K #V1 #V2 #HLK #_ #_ #HL -h -G -V2 lapply (drop_fwd_length_lt2 … HLK) -K -I -V1
#H elim (lt_refl_false i) /2 width=3 by lt_to_le_to_lt/
qed-.
