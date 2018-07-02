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

include "static_2/static/rex_fqup.ma".
include "static_2/static/rdeq.ma".

(* DEGREE-BASED EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ******)

(* Advanced properties ******************************************************)

lemma rdeq_refl: ∀h,o,T. reflexive … (rdeq h o T).
/2 width=1 by rex_refl/ qed.

lemma rdeq_pair_refl: ∀h,o,V1,V2. V1 ≛[h, o] V2 →
                      ∀I,L. ∀T:term. L.ⓑ{I}V1 ≛[h, o, T] L.ⓑ{I}V2.
/2 width=1 by rex_pair_refl/ qed.

(* Advanced inversion lemmas ************************************************)

lemma rdeq_inv_bind_void: ∀h,o,p,I,L1,L2,V,T. L1 ≛[h, o, ⓑ{p,I}V.T] L2 →
                          L1 ≛[h, o, V] L2 ∧ L1.ⓧ ≛[h, o, T] L2.ⓧ.
/2 width=3 by rex_inv_bind_void/ qed-.

(* Advanced forward lemmas **************************************************)

lemma rdeq_fwd_bind_dx_void: ∀h,o,p,I,L1,L2,V,T.
                             L1 ≛[h, o, ⓑ{p,I}V.T] L2 → L1.ⓧ ≛[h, o, T] L2.ⓧ.
/2 width=4 by rex_fwd_bind_dx_void/ qed-.
