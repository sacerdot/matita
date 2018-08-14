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

include "static_2/syntax/tdeq.ma".
include "basic_2/rt_transition/cpm_drops.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Inversion lemmas with degree-based equivalence for terms *****************)

lemma cpm_tdeq_inv_lref (n) (h) (o) (G) (L) (i):
                        ∀X.  ⦃G, L⦄ ⊢ #i ➡[n,h] X → #i ≛[h,o] X →
                        ∧∧ X = #i & n = 0.
#n #h #o #G #L #i #X #H1 #H2
lapply (tdeq_inv_lref1 … H2) -H2 #H destruct
elim (cpm_inv_lref1_drops … H1) -H1 // * [| #m ]
#K #V1 #V2 #_ #_ #H -V1
elim (lifts_inv_lref2_uni_lt … H) -H //
qed-.
