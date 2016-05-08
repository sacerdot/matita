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

(* GENERIC SLICING FOR LOCAL ENVIRONMENTS ***********************************)

definition d_liftable1_all: relation2 lenv term → predicate bool ≝
                            λR,b. ∀f,L,K. ⬇*[b, f] L ≡ K →
                            ∀Ts,Us. ⬆*[f] Ts ≡ Us →
                            all … (R K) Ts → all … (R L) Us.

(* Properties with generic relocation for term vectors **********************)

(* Basic_2A1: was: d1_liftables_liftables_all *)
lemma d1_liftable_liftable_all: ∀R,b. d_liftable1 R b → d_liftable1_all R b.
#R #b #HR #f #L #K #HLK #Ts #Us #H elim H -Ts -Us normalize //
#Ts #Us #T #U #HTU #_ #IHTUs * /3 width=7 by conj/
qed.
