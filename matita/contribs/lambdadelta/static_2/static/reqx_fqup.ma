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
include "static_2/static/reqx.ma".

(* SORT-IRRELEVANT EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ***)

(* Advanced properties ******************************************************)

lemma reqx_refl: ∀T. reflexive … (reqx T).
/2 width=1 by rex_refl/ qed.

lemma reqx_pair_refl: ∀V1,V2. V1 ≛ V2 →
                      ∀I,L. ∀T:term. L.ⓑ{I}V1 ≛[T] L.ⓑ{I}V2.
/2 width=1 by rex_pair_refl/ qed.

(* Advanced inversion lemmas ************************************************)

lemma reqx_inv_bind_void: ∀p,I,L1,L2,V,T. L1 ≛[ⓑ{p,I}V.T] L2 →
                          L1 ≛[V] L2 ∧ L1.ⓧ ≛[T] L2.ⓧ.
/2 width=3 by rex_inv_bind_void/ qed-.

(* Advanced forward lemmas **************************************************)

lemma reqx_fwd_bind_dx_void: ∀p,I,L1,L2,V,T.
                             L1 ≛[ⓑ{p,I}V.T] L2 → L1.ⓧ ≛[T] L2.ⓧ.
/2 width=4 by rex_fwd_bind_dx_void/ qed-.
