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
include "static_2/static/reqg.ma".

(* GEBERIC EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ***********)

(* Advanced properties ******************************************************)

lemma reqg_refl (S):
      reflexive … S →
      c_reflexive … (reqg S).
/3 width=1 by rex_refl, teqg_refl/ qed.

lemma reqg_pair_refl (S):
      reflexive … S →
      ∀V1,V2. V1 ≛[S] V2 →
      ∀I,L. ∀T:term. L.ⓑ[I]V1 ≛[S,T] L.ⓑ[I]V2.
/3 width=1 by rex_pair_refl, teqg_refl/ qed.

(* Advanced inversion lemmas ************************************************)

lemma reqg_inv_bind_void (S):
      ∀p,I,L1,L2,V,T. L1 ≛[S,ⓑ[p,I]V.T] L2 →
      ∧∧ L1 ≛[S,V] L2 & L1.ⓧ ≛[S,T] L2.ⓧ.
/2 width=3 by rex_inv_bind_void/ qed-.

(* Advanced forward lemmas **************************************************)

lemma reqg_fwd_bind_dx_void (S):
      ∀p,I,L1,L2,V,T.
      L1 ≛[S,ⓑ[p,I]V.T] L2 → L1.ⓧ ≛[S,T] L2.ⓧ.
/2 width=4 by rex_fwd_bind_dx_void/ qed-.
