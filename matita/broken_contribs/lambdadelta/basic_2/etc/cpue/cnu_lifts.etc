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

include "static_2/relocation/lifts_tueq.ma".
include "basic_2/rt_transition/cnu.ma".

(* NORMAL TERMS FOR T-UNUNBOUND RT-TRANSITION *******************************)

(* Advanced properties with uniform relocation for terms ********************)

lemma cnu_lref (h) (I) (G) (L):
      ∀i. ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃#i⦄ → ⦃G,L.ⓘ{I}⦄ ⊢ ⥲[h] 𝐍⦃#↑i⦄.
#h #I #G #L #i #Hi #n #X #H
elim (cpm_inv_lref1 … H) -H *
[ #H #_ destruct //
| #J #K #V #HV #HVX #H destruct
  lapply (Hi … HV) -Hi -HV #HV
  elim (tueq_lifts_dx … HV … HVX) -V #Xi #Hi #HX
  lapply (lifts_inv_lref1_uni … Hi) -Hi #H destruct //
]
qed.
