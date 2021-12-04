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

include "basic_2/rt_equivalence/cpcs_drops.ma".
include "basic_2/rt_equivalence/cpcs_cpcs.ma".
include "apps_2/functional/mf_lifts.ma".
include "apps_2/functional/mf_cpr.ma".
include "apps_2/models/model_props.ma".
include "apps_2/models/tm_vpush.ma".

(* TERM MODEL ***************************************************************)

lemma cpcs_repl (h) (G) (L): replace_2 … (cpcs h G L) (cpcs h G L) (cpcs h G L).
/3 width=5 by cpcs_trans, cpcs_sym/ qed-.
(*
lemma pippo (h) (gv) (lv) (T): ●[gv,lv]T = ⟦T⟧{TM h}[gv,lv].
// qed.

lemma tm_mi (h) (gv1) (gv2) (lv1) (lv2) (p) (W) (T):
            ⟦W⟧[gv1,lv1] ≗{TM h} ⟦W⟧[gv2,lv2] →
            (∀d. ⟦T⟧[gv1,⫯[0←d]lv1] ≗ ⟦T⟧[gv2,⫯[0←d]lv2]) →
            ⟦ⓛ[p]W.T⟧[gv1,lv1] ≗ ⟦ⓛ[p]W.T⟧[gv2,lv2].
#h #gv1 #gv2 #lv1 #lv2 #p #W #T #HW #HT
>tm_ti_bind >tm_ti_bind
@(cpcs_bind1 … HW)



<pippo in ⊢ (????%?); >(mf_comp … T) in ⊢ (????%?);
[2: ;;tm_vpush_vlift_join_O

<pippo in ⊢ (????%?);

lapply (HT (#0)) -HT #HT
*)

lemma tm_md (h) (p) (gv) (lv) (V) (T):
            ⓓ[p]V.⟦T⟧{TM h}[⇡[0]gv,⇡[0←#0]lv] ≗{TM h} V⊕{TM h}[p]⟦T⟧{TM h}[gv,⫯{TM h}[0←V]lv].
#h #p #gv #lv #V #T
>tm_co_rw >(mf_lifts_basic_SO_dx T 0)
>(mf_comp … T) in ⊢ (???%);
[2: @tm_vpush_vlift_join_O |4: @exteq_refl |3,5: skip ]
/6 width=4 by mf_delta_drops, cpcs_bind1, cpc_cpcs, drops_refl, or_introl/
qed.

lemma tm_mz (h) (V) (T): V ⊕[Ⓣ] T ≗{TM h} T.
/4 width=3 by cpc_cpcs, cpm_zeta, or_introl/ qed.

lemma tm_me (h) (gv) (lv) (U) (T):
            ⟦ⓝU.T⟧[gv,lv] ≗{TM h} ⟦T⟧[gv,lv].
/4 width=1 by cpc_cpcs, cpm_eps, or_introl/ qed.

lemma tm_mb (h) (p) (gv) (lv) (d) (W) (T):
            d@⟦ⓛ[p]W.T⟧[gv,lv] ≗{TM h} d⊕[p]⟦T⟧[gv,⫯[0←d]lv].
#h #p #gv #lv #d #W #T
@cpcs_repl [5: @tm_md |4: /4 width=2 by cpc_cpcs, cpm_beta, or_intror/ |1,2: skip ]
/5 width=1 by cpcs_bind1, cpc_cpcs, cpm_eps, or_introl/
qed.

lemma ti_mh (h) (p) (d1) (d2) (d3):
            d1@(d2⊕[p]d3) ≗{TM h} d2⊕[p](d1@d3).
/4 width=3 by cpc_cpcs, cpm_theta, or_introl/ qed.

definition is_tm (h): is_model (TM h) ≝ mk_is_model …. //
[ @cpcs_repl
| #p #V1 #V2 #HV #T1 #T2 #HT
  @(cpcs_bind1 … HV) @(cpcs_lifts_bi … HT)
  /2 width=5 by drops_drop/
| #V1 #V2 #HV #T1 #T2 #HT
  @(cpcs_flat … HV … HT)
|
].
