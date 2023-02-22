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

include "static_2/relocation/lifts_teqg.ma".
include "static_2/syntax/teqx.ma".

(* GENERIC RELOCATION FOR TERMS *********************************************)

(* Properties with sort-irrelevant equivalence for terms ********************)

lemma teqx_lifts_sn: liftable2_sn teqx.
/2 width=3 by teqg_lifts_sn/ qed-.

lemma teqx_lifts_dx: liftable2_dx teqx.
/2 width=3 by teqg_lifts_dx/ qed-.

lemma teqx_lifts_bi: liftable2_bi teqx.
/2 width=6 by teqg_lifts_bi/ qed-.

(* Inversion lemmas with sort-irrelevant equivalence for terms **************)

lemma teqx_inv_lifts_sn: deliftable2_sn teqx.
/2 width=3 by teqg_inv_lifts_sn/ qed-.

lemma teqx_inv_lifts_dx: deliftable2_dx teqx.
/2 width=3 by teqg_inv_lifts_dx/ qed-.

lemma teqx_inv_lifts_bi: deliftable2_bi teqx.
/2 width=6 by teqg_inv_lifts_bi/ qed-.

lemma teqx_lifts_inv_pair_sn (I) (f):
      ∀X,T. ⇧*[f]X ≘ T → ∀V. ②[I]V.T ≅ X → ⊥.
/2 width=8 by teqg_lifts_inv_pair_sn/ qed-.
