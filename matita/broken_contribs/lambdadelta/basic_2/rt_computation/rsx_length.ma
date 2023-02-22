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

include "static_2/static/reqg_length.ma".
include "basic_2/rt_transition/lpx_length.ma".
include "basic_2/rt_computation/rsx.ma".

(* STRONGLY NORMALIZING REFERRED LOCAL ENVS FOR EXTENDED RT-TRANSITION ******)

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: lsx_sort *)
lemma rsx_sort (G): ∀L,s. G ⊢ ⬈*𝐒[⋆s] L.
#G #L1 #s @rsx_intro #L2 #H #Hs
elim Hs -Hs /3 width=3 by lpx_fwd_length, reqg_sort_length/
qed.

(* Basic_2A1: uses: lsx_gref *)
lemma rsx_gref (G): ∀L,l. G ⊢ ⬈*𝐒[§l] L.
#G #L1 #s @rsx_intro #L2 #H #Hs
elim Hs -Hs /3 width=3 by lpx_fwd_length, reqg_gref_length/
qed.

lemma rsx_unit (G): ∀I,L. G ⊢ ⬈*𝐒[#0] L.ⓤ[I].
#G #I #L1 @rsx_intro
#Y #HY #HnY elim HnY -HnY
elim (lpx_inv_unit_sn … HY) -HY #L2 #HL12 #H destruct
/3 width=3 by lpx_fwd_length, reqg_unit_length/
qed.
