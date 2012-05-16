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

include "basic_2/grammar/term_vector.ma".
include "basic_2/grammar/tstc.ma".

(* SAME TOP TERM CONSTRUCTOR ************************************************)

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was only: iso_flats_lref_bind_false iso_flats_flat_bind_false *)
lemma tstc_inv_bind_appls_simple: ∀I,Vs,V2,T1,T2. ⒶVs.T1 ≃ ⓑ{I} V2. T2 →
                                  𝐒[T1] → ⊥.
#I #Vs #V2 #T1 #T2 #H
elim (tstc_inv_pair2 … H) -H #V0 #T0
elim Vs -Vs normalize
[ #H destruct #H
  @(simple_inv_bind … H)
| #V #Vs #_ #H destruct
]
qed.

