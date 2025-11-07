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

include "delayed_updating/reduction/dbf_step_focus.ma".
include "delayed_updating/reduction/ibf_step_focus.ma".
include "delayed_updating/reduction/preterm_delayed_unwind2.ma".
include "delayed_updating/reduction/preterm_focus_unwind2.ma".
include "delayed_updating/reduction/prototerm_focus_eq.ma".
include "delayed_updating/unwind/unwind2_preterm_fsubst.ma".
include "delayed_updating/syntax/path_closed_structure.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Main constructions with ibfs *********************************************)

(* UPDATE *)

theorem ibfs_unwind2_sx_dbfs (f) (t1) (u2) (s):
        t1 ϵ 𝐓 → ▼[f]t1 ➡𝐢𝐛𝐟[s] u2 →
        ∃∃t2,r. t1 ➡𝐝𝐛𝐟[r] t2 & ▼[f]t2 ⇔ u2 & ▼[f]r = s.
#f #t1 #u2 #s #H1t1 #H0
elim (ibfs_inv_brf … H0) -H0 #p #b #q #n
* #Hs #Hb #Hq * #x0 #H2t1 #H0 #Hu2 destruct
elim (eq_inv_unwind2_path_beta … H0) -H0 #p0 #b0 #q0 #n0 #H1 #H2 #H3 #H4 #Hn destruct
lapply (pcc_inv_structure … Hq) -Hq #H0 destruct
<structure_idem in Hb; #Hb
elim (eq_inv_succ_fbr_xapp … Hn) -Hn #Hq0 #Hn0
>Hn0 in H2t1; -Hn0 #Ht1
@(ex3_2_intro … (⬕[𝐅❨t1,p0,b0,q0,⫰n0❩←𝐃❨t1,p0,b0,q0,⫰n0❩]t1) (⓪𝐫❨p0,b0,q0,⫰n0❩))
[ @(dbfs_mk_brf … p0 b0 q0 (⫰n0))
  [ @xprc_mk [1,2: // ]
    @(eq_depth_unwind2_rmap_p3beta_lapp_pcc … Hq0)
  | //
  ]
| @(subset_eq_canc_sx … Hu2) -u2
  @(subset_eq_trans … (unwind2_term_fsubst_le …)) [2,3: // ]
  @fsubst_eq_repl [ // ]
  [ >Hq0 -Hq0 /2 width=1 by brf_unwind2/
  | /2 width=1 by brd_unwind2/
  ]
| <path_clear_beta <path_clear_beta <unwind2_path_beta //
]
qed-.

(* Main inversions with ibfs ************************************************)

theorem dbfs_inv_ibfs (f) (t1) (t2) (r):
        t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 →
        ▼[f]t1 ➡𝐢𝐛𝐟[▼[f]r] ▼[f]t2.
#f #t1 #t2 #r #H0t1 #H0 elim (dbfs_inv_brf … H0) -H0
#p #b #q #n #Hr cases Hr #H0 #Hb #Hq #Ht1 #Ht2 destruct
lapply (pcc_eq_depth_unwind2_rmap_p3beta_lapp f p b … Hq) #Hn
@(ibfs_mk_brf … (⊗p) (⊗b) (⊗q) (♭q)) [ @and4_intro ]
[ <path_clear_beta <path_clear_beta <unwind2_path_beta //
| // | //
| lapply (in_comp_unwind2_bi f … Ht1) -H0t1 -Hb -Ht2 -Ht1
  <unwind2_path_beta <fbr_xapp_succ_lapp <Hn //
| lapply (unwind2_term_eq_repl_dx f … Ht2) -Ht2 #Ht2
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (unwind2_term_fsubst_le …)) [2,3: // ]
  @fsubst_eq_repl [ // ]
  [ >Hn -Hn /2 width=1 by brf_unwind2/
  | /2 width=1 by brd_unwind2/
  ]
]
qed-.
