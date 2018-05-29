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

include "basic_2/static/lfdeq_fqup.ma".
include "basic_2/rt_computation/rdsx.ma".

(* STRONGLY NORMALIZING REFERRED LOCAL ENV.S FOR UNBOUND RT-TRANSITION ******)

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: lsx_atom *)
lemma lfsx_atom (h) (o) (G) (T): G ⊢ ⬈*[h, o, T] 𝐒⦃⋆⦄.
#h #o #G #T
@rdsx_intro #Y #H #HnT
lapply (lpx_inv_atom_sn … H) -H #H destruct
elim HnT -HnT //
qed.

(* Advanced forward lemmas **************************************************)

(* Basic_2A1: uses: lsx_fwd_bind_dx *)
(* Note: the exclusion binder (ⓧ) makes this more elegant and much simpler *)
(* Note: the old proof without the exclusion binder requires lreq *)
lemma rdsx_fwd_bind_dx (h) (o) (G):
                       ∀p,I,L,V,T. G ⊢ ⬈*[h, o, ⓑ{p,I}V.T] 𝐒⦃L⦄ →
                       G ⊢ ⬈*[h, o, T] 𝐒⦃L.ⓧ⦄.
#h #o #G #p #I #L #V #T #H
@(rdsx_ind … H) -L #L1 #_ #IH
@rdsx_intro #Y #H #HT
elim (lpx_inv_unit_sn … H) -H #L2 #HL12 #H destruct
/4 width=4 by lfdeq_fwd_bind_dx_void/
qed-.

(* Advanced inversion lemmas ************************************************)

(* Basic_2A1: uses: lsx_inv_bind *)
lemma rdsx_inv_bind (h) (o) (G): ∀p,I,L,V,T. G ⊢ ⬈*[h, o, ⓑ{p,I}V.T] 𝐒⦃L⦄ →
                                 ∧∧ G ⊢ ⬈*[h, o, V] 𝐒⦃L⦄ & G ⊢ ⬈*[h, o, T] 𝐒⦃L.ⓧ⦄.
/3 width=4 by rdsx_fwd_pair_sn, rdsx_fwd_bind_dx, conj/ qed-.
