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

include "delayed_updating/reduction/ibfr.ma".

include "delayed_updating/unwind/unwind2_preterm_fsubst.ma".
include "delayed_updating/unwind/unwind2_preterm_eq.ma".
include "delayed_updating/unwind/unwind2_prototerm_lift.ma".
include "delayed_updating/unwind/unwind2_rmap_crux.ma".

include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".

include "delayed_updating/syntax/path_closed_structure.ma".
include "delayed_updating/syntax/path_structure_depth.ma".

(* IMMEDIATE BALANCED FOCUSED REDUCTION *************************************)

(* Constructions with unwind2 ***********************************************)

lemma ibfr_unwind_bi (f) (t1) (t2) (r):
      t1 ϵ 𝐓 → r ϵ 𝐈 →
      t1 ➡𝐢𝐛𝐟[r] t2 → ▼[f]t1 ➡𝐢𝐛𝐟[⊗r] ▼[f]t2.
#f #t1 #t2 #r #H1t1 #H2r
* #p #b #q #m #n #Hr #Hb #Hm #Hn #Ht1 #Ht2 destruct
@(ex6_5_intro … (⊗p) (⊗b) (⊗q) (♭b) (♭q))
[ -H1t1 -H2r -Hb -Hm -Hn -Ht1 -Ht2 //
| -H1t1 -H2r -Hm -Hn -Ht1 -Ht2 //
| -H1t1 -H2r -Hb -Hn -Ht1 -Ht2
  /2 width=2 by path_closed_structure_depth/
| -H1t1 -H2r -Hb -Hm -Ht1 -Ht2
  /2 width=2 by path_closed_structure_depth/
| lapply (in_comp_unwind2_path_term f … Ht1) -Ht2 -Ht1 -H1t1 -H2r -Hb
  <unwind2_path_d_dx <tr_pap_succ_nap <list_append_rcons_sn >list_append_assoc
  <nap_unwind2_rmap_append_closed_Lq_dx //
| lapply (unwind2_term_eq_repl_dx f … Ht2) -Ht2 #Ht2
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (unwind2_term_fsubst_pic …))
  [ @fsubst_eq_repl [ // | // ]
    @(subset_eq_canc_sn … (lift_term_eq_repl_dx …))
    [ @unwind2_term_grafted_S /2 width=2 by ex_intro/ | skip ] -Ht1
    @(subset_eq_trans … (lift_unwind2_term_after …))
    @(subset_eq_canc_dx … (unwind2_lift_term_after …))
    @unwind2_term_eq_repl_sn
(* Note: crux of the proof begins *)
    /2 width=1 by unwind2_rmap_uni_crux/
(* Note: crux of the proof ends *)
  | //
  | /2 width=2 by ex_intro/
  | //
  ]
]
qed-.
