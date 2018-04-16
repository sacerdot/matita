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

include "basic_2/s_computation/fqup_drops.ma".
include "basic_2/s_computation/fqus_fqup.ma".

(* STAR-ITERATED SUPCLOSURE *************************************************)

(* Properties with generic slicing for local environments *******************)

lemma fqus_drops: ∀b,G,L,K,T,U,i. ⬇*[i] L ≘ K → ⬆*[i] T ≘ U →
                  ⦃G, L, U⦄ ⊐*[b] ⦃G, K, T⦄.
#b #G #L #K #T #U * /3 width=3 by fqup_drops_succ, fqup_fqus/
#HLK #HTU <(lifts_fwd_isid … HTU) -U // <(drops_fwd_isid … HLK) -K //
qed.
