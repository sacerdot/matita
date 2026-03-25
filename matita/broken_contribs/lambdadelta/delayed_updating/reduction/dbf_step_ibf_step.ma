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
#f #t1 #u2 #s #Ht1 #H0
elim (ibfs_inv_brf … H0) -H0 #p #b #q #n
* * #x0 #Hx0 #H1 * #H2 #Hb #Hq #Hu2 destruct
elim (eq_inv_unwind2_path_beta … (sym_eq … H2)) -H2
#p0 #b0 #q0 #n0 #H1 #H2 #H3 #H4 #Hn destruct
lapply (pcc_inv_structure … Hq) -Hq #H0 destruct
<structure_idem in Hb; #Hb
elim (eq_inv_succ_fbr_xapp … Hn) -Hn #Hq0 #Hn0
>Hn0 in Hx0; -Hn0 #Hx0
@(ex3_2_intro … (⬕[𝐅❨t1,p0,b0,q0,⫰n0❩←𝐃❨t1,p0,b0,q0,⫰n0❩]t1) (𝐫❨p0,b0,q0,⁤↑⫰n0❩))
[ @(dbfs_mk_brf … p0 b0 q0 (⫰n0))
  [ @pcxr_mk [1,2: // ]
    @(eq_depth_unwind2_rmap_p3beta_lapp_pcc … Hq0)
  | //
  ]
| @(subset_eq_canc_sx … Hu2) -u2
  @(subset_eq_trans … (unwind2_term_fsubst_le …)) [2,3: // ]
  @fsubst_eq_repl [ // ]
  [ >Hq0 -Hq0 /2 width=1 by brf_unwind2/
  | /2 width=1 by brd_unwind2/
  ]
| //
]
qed-.

(* Main inversions with ibfs ************************************************)

theorem dbfs_inv_ibfs (f) (t1) (t2) (r):
        t1 ϵ 𝐓 → t1 ➡𝐝𝐛𝐟[r] t2 →
        ▼[f]t1 ➡𝐢𝐛𝐟[▼[f]r] ▼[f]t2.
#f #t1 #t2 #r #Ht1 #H0 elim (dbfs_inv_brf … H0) -H0 #p #b #q #n
* #Hr * #H0 #Hb #Hq #Ht2 destruct
lapply (pcc_eq_depth_unwind2_rmap_p3beta_lapp f p b … Hq) #Hn
@(ibfs_mk_brf … (⊗p) (⊗b) (⊗q) (♭q)) [ @subset_and_in [| @and3_intro ] ]
[ lapply (in_comp_unwind2_bi f … Hr) -Hr -Hb -Ht2 -Ht1
  <unwind2_path_beta <fbr_xapp_succ_lapp <Hn //
| <unwind2_path_beta >Hn >fbr_dapp_succ_lapp //
| // | //
| lapply (unwind2_term_eq_repl_dx f … Ht2) -Ht2 #Ht2
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (unwind2_term_fsubst_le …)) [2,3: // ]
  @fsubst_eq_repl [ // ]
  [ >Hn -Hn /2 width=1 by brf_unwind2/
  | /2 width=1 by brd_unwind2/
  ]
]
qed-.
