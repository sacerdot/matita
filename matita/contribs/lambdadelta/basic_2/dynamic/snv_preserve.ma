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

include "basic_2/computation/fsb_aaa.ma".
include "basic_2/dynamic/snv_da_lpr.ma".
include "basic_2/dynamic/snv_lstas.ma".
include "basic_2/dynamic/snv_lstas_lpr.ma".
include "basic_2/dynamic/snv_lpr.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Main preservation properties *********************************************)

lemma snv_preserve: ∀h,g,G,L,T. ⦃G, L⦄ ⊢ T ¡[h, g] →
                    ∧∧ IH_da_cpr_lpr h g G L T
                     & IH_snv_cpr_lpr h g G L T
                     & IH_snv_lstas h g G L T
                     & IH_lstas_cpr_lpr h g G L T.
#h #g #G #L #T #HT elim (snv_fwd_aaa … HT) -HT
#A #HT @(aaa_ind_fpbg h g … HT) -G -L -T -A
#G #L #T #A #_ #IH -A @and4_intro
[ letin aux ≝ da_cpr_lpr_aux | letin aux ≝ snv_cpr_lpr_aux
| letin aux ≝ snv_lstas_aux | letin aux ≝ lstas_cpr_lpr_aux
]
@(aux … G L T) // #G0 #L0 #T0 #H elim (IH … H) -IH -H //
qed-.

theorem da_cpr_lpr: ∀h,g,G,L,T. IH_da_cpr_lpr h g G L T.
#h #g #G #L #T #HT elim (snv_preserve … HT) /2 width=1 by/
qed-.

theorem snv_cpr_lpr: ∀h,g,G,L,T. IH_snv_cpr_lpr h g G L T.
#h #g #G #L #T #HT elim (snv_preserve … HT) /2 width=1 by/
qed-.

theorem snv_lstas: ∀h,g,G,L,T. IH_snv_lstas h g G L T.
#h #g #G #L #T #HT elim (snv_preserve … HT) /2 width=5 by/
qed-.

theorem lstas_cpr_lpr: ∀h,g,G,L,T. IH_lstas_cpr_lpr h g G L T.
#h #g #G #L #T #HT elim (snv_preserve … HT) /2 width=3 by/
qed-.

(* Advanced preservation properties *****************************************)
