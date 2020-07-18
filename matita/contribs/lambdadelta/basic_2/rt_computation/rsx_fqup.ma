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

include "static_2/static/reqg_fqup.ma".
include "basic_2/rt_computation/rsx.ma".

(* STRONGLY NORMALIZING REFERRED LOCAL ENVS FOR EXTENDED RT-TRANSITION ******)

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: lsx_atom *)
lemma lfsx_atom (G) (T): G ⊢ ⬈*𝐒[T] ⋆.
#G #T
@rsx_intro #Y #H #HnT
lapply (lpx_inv_atom_sn … H) -H #H destruct
elim HnT -HnT /2 width=1 by rex_refl/
qed.

(* Advanced forward lemmas **************************************************)

(* Basic_2A1: uses: lsx_fwd_bind_dx *)
(* Note: the exclusion binder (ⓧ) makes this more elegant and much simpler *)
(* Note: the old proof without the exclusion binder requires lreq *)
lemma rsx_fwd_bind_dx_void (G):
      ∀p,I,L,V,T. G ⊢ ⬈*𝐒[ⓑ[p,I]V.T] L → G ⊢ ⬈*𝐒[T] L.ⓧ.
#G #p #I #L #V #T #H
@(rsx_ind … H) -L #L1 #_ #IH
@rsx_intro #Y #H #HT
elim (lpx_inv_unit_sn … H) -H #L2 #HL12 #H destruct
/4 width=4 by reqg_fwd_bind_dx_void/
qed-.

(* Advanced inversion lemmas ************************************************)

(* Basic_2A1: uses: lsx_inv_bind *)
lemma rsx_inv_bind_void (G):
      ∀p,I,L,V,T. G ⊢ ⬈*𝐒[ⓑ[p,I]V.T] L →
      ∧∧ G ⊢ ⬈*𝐒[V] L & G ⊢ ⬈*𝐒[T] L.ⓧ.
/3 width=4 by rsx_fwd_pair_sn, rsx_fwd_bind_dx_void, conj/ qed-.
