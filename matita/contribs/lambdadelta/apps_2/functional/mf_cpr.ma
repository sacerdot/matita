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

include "basic_2/rt_transition/cpm_drops.ma".
include "basic_2/rt_transition/cpr.ma".
include "apps_2/functional/mf_exteq.ma".

(* MULTIPLE FILLING FOR TERMS ***********************************************)

(* Properties with relocation ***********************************************)

lemma mf_delta_drops (h) (G): ∀K,V1,V2. ⦃G,K⦄ ⊢ V1 ➡[h] V2 →
                              ∀T,L,l. ⇩*[l] L ≘ K.ⓓV1 →
                              ∀gv,lv. ⦃G,L⦄ ⊢ ●[gv,⇡[l←#l]lv]T ➡[h] ●[gv,⇡[l←↑[↑l]V2]lv]T.
#h #G #K #V1 #V2 #HV #T elim T -T * //
[ #i #L #l #HKL #gv #lv
  >mf_lref >mf_lref
  elim (lt_or_eq_or_gt i l) #Hl destruct
  [ >(mf_vpush_lt … Hl) >(mf_vpush_lt … Hl) //
  | >mf_vpush_eq >mf_vpush_eq
    /2 width=6 by cpm_delta_drops/
  | >(mf_vpush_gt … Hl) >(mf_vpush_gt … Hl) //
  ]
| #p #I #V #T #IHV #IHT #L #l #HLK #gv #lv
  >mf_bind >mf_bind
  >(mf_comp … T) in ⊢ (?????%?);
  [2: @mf_vpush_swap // |4: @exteq_refl |3,5: skip ]
  >(mf_comp … T) in ⊢ (??????%);
  [2: @mf_vpush_swap // |4: @exteq_refl |3,5: skip ]
  >(flifts_lref_uni 1 l) >(flifts_compose_uni 1 (↑l))
  /4 width=1 by cpm_bind, drops_drop/
| #I #V #T #IHV #IHT #L #l #HLK #gv #lv
  >mf_flat >mf_flat /3 width=1 by cpr_flat/
]
qed.
