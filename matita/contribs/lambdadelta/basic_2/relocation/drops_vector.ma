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

include "basic_2/relocation/lifts_vector.ma".
include "basic_2/relocation/drops.ma".

(* GENERAL SLICING FOR LOCAL ENVIRONMENTS ***********************************)

definition d_liftable1_all: relation2 lenv term → predicate bool ≝
                            λR,c. ∀L,K,f. ⬇*[c, f] L ≡ K →
                            ∀Ts,Us. ⬆*[f] Ts ≡ Us →
                            all … (R K) Ts → all … (R L) Us.

(* Properties on general relocation for term vectors ************************)

(* Basic_2A1: was: d1_liftables_liftables_all *)
lemma d1_liftable_liftable_all: ∀R,c. d_liftable1 R c → d_liftable1_all R c.
#R #c #HR #L #K #f #HLK #Ts #Us #H elim H -Ts -Us normalize //
#Ts #Us #T #U #HTU #_ #IHTUs * /3 width=7 by conj/
qed.
