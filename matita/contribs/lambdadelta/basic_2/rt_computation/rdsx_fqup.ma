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

include "static_2/static/rdeq_fqup.ma".
include "basic_2/rt_computation/rdsx.ma".

(* STRONGLY NORMALIZING REFERRED LOCAL ENV.S FOR UNBOUND RT-TRANSITION ******)

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: lsx_atom *)
lemma lfsx_atom (h) (G) (T): G ⊢ ⬈*[h, T] 𝐒⦃⋆⦄.
#h #G #T
@rdsx_intro #Y #H #HnT
lapply (lpx_inv_atom_sn … H) -H #H destruct
elim HnT -HnT //
qed.

(* Advanced forward lemmas **************************************************)

(* Basic_2A1: uses: lsx_fwd_bind_dx *)
(* Note: the exclusion binder (ⓧ) makes this more elegant and much simpler *)
(* Note: the old proof without the exclusion binder requires lreq *)
lemma rdsx_fwd_bind_dx (h) (G):
                       ∀p,I,L,V,T. G ⊢ ⬈*[h, ⓑ{p,I}V.T] 𝐒⦃L⦄ →
                       G ⊢ ⬈*[h, T] 𝐒⦃L.ⓧ⦄.
#h #G #p #I #L #V #T #H
@(rdsx_ind … H) -L #L1 #_ #IH
@rdsx_intro #Y #H #HT
elim (lpx_inv_unit_sn … H) -H #L2 #HL12 #H destruct
/4 width=4 by rdeq_fwd_bind_dx_void/
qed-.

(* Advanced inversion lemmas ************************************************)

(* Basic_2A1: uses: lsx_inv_bind *)
lemma rdsx_inv_bind (h) (G):
      ∀p,I,L,V,T. G ⊢ ⬈*[h, ⓑ{p,I}V.T] 𝐒⦃L⦄ →
      ∧∧ G ⊢ ⬈*[h, V] 𝐒⦃L⦄ & G ⊢ ⬈*[h, T] 𝐒⦃L.ⓧ⦄.
/3 width=4 by rdsx_fwd_pair_sn, rdsx_fwd_bind_dx, conj/ qed-.
