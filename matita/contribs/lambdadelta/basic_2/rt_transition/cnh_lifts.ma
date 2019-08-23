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

include "static_2/relocation/lifts.ma".
include "basic_2/rt_transition/cnh.ma".

(* NORMAL TERMS FOR HEAD T-UNUNBOUND RT-TRANSITION **************************)

(* Advanced properties with uniform relocation for terms ********************)

lemma cnh_lref (h) (I) (G) (L):
      ∀i. ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃#i⦄ → ⦃G,L.ⓘ{I}⦄ ⊢ ⥲[h] 𝐍⦃#↑i⦄.
#h #I #G #L #i #Hi #n #X #H
elim (cpm_inv_lref1 … H) -H *
[ #H #_ destruct //
| #J #K #V #HV #HVX #H destruct
  lapply (Hi … HV) -Hi -HV #HV
  lapply (theq_inv_lref1 … HV) -HV #H destruct
  lapply (lifts_inv_lref1_uni … HVX) -HVX #H destruct //
]
qed.
