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

include "delayed_updating/reduction/ibf_step_focus.ma".
include "delayed_updating/reduction/prototerm_immediate_lift.ma".
include "delayed_updating/reduction/prototerm_focus_lift.ma".
include "delayed_updating/substitution/fsubst_lift.ma".
include "delayed_updating/substitution/lift_path_structure.ma".

(* IMMEDIATE BALANCED FOCUSED REDUCTION *************************************)

(* UPDATE *)

(* Constructions with lift **************************************************)

theorem ibfs_lift_bi (f) (t1) (t2) (r):
        t1 ➡𝐢𝐛𝐟[r] t2 → 🠡[f]t1 ➡𝐢𝐛𝐟[🠡[f]r] 🠡[f]t2.
#f #t1 #t2 #r #H0 elim (ibfs_inv_brf … H0) -H0 #p #b #q #n
* #Hr * #H0 #Hb #Hq #Ht2 destruct
@(ibfs_mk_brf … (🠡[f]p) (🠡[🠢[p]f]b) (🠡[🠢[𝐫❨p,b❩]f]q) (🠢[𝐫❨p,b,q❩]f＠§❨n❩))
[ @subset_and_in [2: @and3_intro ]]
[ -Hb -Hq -Hr -Ht2 //
| -Hq -Hr -Ht2 //
| -Hb -Hr -Ht2
  <(lift_path_closed_des_gen … Hq)
  <(pcc_lift_rmap_p3beta_lapp … Hq) //
| lapply (in_comp_lift_bi f … Hr) -Hr -Ht2
  <lift_path_beta //
| lapply (lift_term_eq_repl_dx f … Ht2) -Ht2 #Ht2 -Hr
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (lift_term_fsubst …))
  @fsubst_eq_repl [ // | /2 width=1 by brf_lift/ | @bri_lift // ]
]
qed.

(* Inversions with lift *****************************************************)

lemma ibfs_inv_lift_sx (f) (t1) (u2) (s):
      (🠡[f]t1) ➡𝐢𝐛𝐟[s] u2 →
      ∃∃t2,r. t1 ➡𝐢𝐛𝐟[r] t2 & 🠡[f]t2 ⇔ u2 & 🠡[f]r = s.
#f #t1 #u2 #s #H0 elim (ibfs_inv_brf … H0) -H0 #p #b #q #n
* * #x0 #Hx0 #H1 * #H2 #Hb #Hq #Hu2 destruct
elim (eq_inv_lift_path_beta … (sym_eq … H2)) -H2
#p0 #b0 #q0 #n0 #H1 #H2 #H3 #H4 #H0 destruct
<structure_lift_path in Hb; #Hb
lapply (lift_path_inv_closed … Hq) -Hq #Hq0
elim (eq_inv_succ_fbr_xapp … H0) -H0 #H0 #Hn0 destruct
lapply (pcc_inv_lift_rmap_p3beta_lapp … Hq0) -Hq0 #Hq0
@(ex3_2_intro … (⬕[𝐅❨t1,p0,b0,q0,⫰n0❩←𝐈❨t1,p0,b0,q0,⫰n0❩]t1))
[4: // | skip
| @(ibfs_mk_brf … p0 b0 q0 (⫰n0)) [2: // ]
  /3 width=1 by subset_and_in, and3_intro/
| @(subset_eq_canc_sx … Hu2) -u2
  @(subset_eq_trans … (lift_term_fsubst …))
  @fsubst_eq_repl [ // | /2 width=1 by brf_lift/ | @bri_lift // ]
]
qed-.
