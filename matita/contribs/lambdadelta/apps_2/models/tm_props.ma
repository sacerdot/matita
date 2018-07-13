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

include "basic_2/rt_equivalence/cpcs_cpcs.ma".
include "apps_2/models/model_props.ma".
include "apps_2/models/tm.ma".

(* TERM MODEL ***************************************************************)

lemma tm_md (h): ∀T,V,gv,lv. ⟦+ⓓV.T⟧[gv,lv] ≗{TM h} ⟦T⟧[gv,⫯[O←⟦V⟧[gv,lv]]lv].
#h #T elim T *
[ /4 width=3 by cpc_cpcs, cpm_zeta, or_introl/
| #i #V #gv #lv
  elim (eq_or_gt i) #Hi destruct
  [ elim (lifts_total (⟦V⟧[gv,lv]) (𝐔❴1❵)) #W #HVW
    >tm_ti_lref >vpush_eq
    >tm_ti_bind >tm_ti_lref >tm_vpush_eq
    /5 width=3 by cpc_cpcs, cpm_zeta, cpm_delta, or_introl/
  | >tm_ti_lref >vpush_gt //
    >tm_ti_bind >tm_ti_lref >tm_vpush_gt //
    /4 width=3 by cpc_cpcs, cpm_zeta, or_introl/
  ]
| #l #V #gv #lv
  >tm_ti_bind >tm_ti_gref >tm_ti_gref
  /4 width=3 by cpc_cpcs, cpm_zeta, or_introl/
| #p #I #W #T #IHW #IHT #V #gv #lv
  >tm_ti_bind in ⊢ (???%);
(*
  
  >tm_ti_bind >tm_ti_bind
  @cpc_cpcs @or_introl
  @cpm_bind 
  
  /4 width=3 by cpc_cpcs, cpm_zeta, or_introl/

definition is_tm (h): is_model (TM h) ≝ mk_is_model …. //
[ 
|
| #gv #lv #p #V #T
  @cpcs_cprs_dx
  @cprs_step_sn
  [2: @cpm_bind // | skip ]  
*)
