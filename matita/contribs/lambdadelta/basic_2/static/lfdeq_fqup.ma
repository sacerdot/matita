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

include "basic_2/static/lfxs_fqup.ma".
include "basic_2/static/lfdeq.ma".

(* DEGREE-BASED EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ******)

(* Advanced properties ******************************************************)

lemma lfdeq_refl: ∀h,o,T. reflexive … (lfdeq h o T).
/2 width=1 by lfxs_refl/ qed.

lemma lfdeq_pair: ∀h,o,V1,V2. V1 ≡[h, o] V2 →
                  ∀I,L. ∀T:term. L.ⓑ{I}V1 ≡[h, o, T] L.ⓑ{I}V2.
/2 width=1 by lfxs_pair/ qed.