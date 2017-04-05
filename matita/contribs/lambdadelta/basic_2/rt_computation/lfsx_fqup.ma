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
include "basic_2/rt_computation/lfsx.ma".

(* STRONGLY NORMALIZING LOCAL ENV.S FOR UNCOUNTED PARALLEL RT-TRANSITION ****)

(* Advanced properties ******************************************************)

(* Basic_2A1: was: lsx_atom *)
lemma lfsx_atom: ∀h,o,G,T. G ⊢ ⬈*[h, o, T] 𝐒⦃⋆⦄.
#h #o #G #T @lfsx_intro
#Y #H #HI lapply (lfpx_inv_atom_sn … H) -H
#H destruct elim HI -HI //
qed.
