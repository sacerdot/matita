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

include "static_2/relocation/lifts_vector.ma".
include "static_2/relocation/drops.ma".

(* GENERIC SLICING FOR LOCAL ENVIRONMENTS ***********************************)

definition d_liftable1_all: predicate (relation2 lenv term) ≝
                            λR. ∀K,Ts. all … (R K) Ts →
                            ∀b,f,L. ⇩*[b,f] L ≘ K →
                            ∀Us. ⇧*[f] Ts ≘ Us → all … (R L) Us.

(* Properties with generic relocation for term vectors **********************)

(* Basic_2A1: was: d1_liftables_liftables_all *)
lemma d1_liftable_liftable_all: ∀R. d_liftable1 R → d_liftable1_all R.
#R #HR #K #Ts #HTs #b #f #L #HLK #Us #H
generalize in match HTs; -HTs elim H -Ts -Us normalize //
#Ts #Us #T #U #HTU #_ #IHTUs * /3 width=7 by conj/
qed.
