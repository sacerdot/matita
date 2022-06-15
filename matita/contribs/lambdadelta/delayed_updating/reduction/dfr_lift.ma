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

include "delayed_updating/reduction/dfr.ma".
include "delayed_updating/reduction/ifr.ma".
(*
include "delayed_updating/unwind/unwind2_constructors.ma".
include "delayed_updating/unwind/unwind2_preterm_fsubst.ma".
include "delayed_updating/unwind/unwind2_preterm_eq.ma".
include "delayed_updating/unwind/unwind2_prototerm_lift.ma".
include "delayed_updating/unwind/unwind2_rmap_head.ma".
*)
include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".
include "delayed_updating/substitution/lift_path_head.ma".

include "delayed_updating/syntax/prototerm_proper_constructors.ma".


(* DELAYED FOCUSED REDUCTION ************************************************)

(* Constructions with lift **************************************************)
(*
lemma pippo (f) (r):
      ↑[↑[r]f](rᴿ) = (↑[f]r)ᴿ.
#f #r @(list_ind_rcons … r) -r //
#p * [ #n ] #IH
[ <reverse_rcons <lift_path_d_sn <lift_rmap_d_dx
  <lift_path_d_dx <reverse_rcons
  <IH  
*)

theorem dfr_lift_bi (f) (p) (q) (t1) (t2): (*t1 ϵ 𝐓 → *)
        t1 ➡𝐝𝐟[p,q] t2 → ↑[f]t1 ➡𝐝𝐟[↑[f]p,↑[↑[p◖𝗔◖𝗟]f]q] ↑[f]t2.
#f #p #q #t1 #t2
* #n * #H1n #Ht1 #Ht2
@(ex_intro … ((↑[p●𝗔◗𝗟◗q]f)＠⧣❨n❩)) @and3_intro
[ -Ht1 -Ht2
  <lift_rmap_L_dx >lift_path_L_sn
  >list_append_rcons_sn in H1n; <reverse_append #H1n
  <(lift_path_head … H1n) -H1n //
| lapply (in_comp_lift_path_term f … Ht1) -Ht2 -Ht1 -H1n
  <lift_path_d_dx #Ht1 //
| lapply (lift_term_eq_repl_dx f … Ht2) -Ht2 #Ht2
  @(subset_eq_trans … Ht2) -t2
(*  
  @(subset_eq_trans … (unwind2_term_fsubst …))
  [ @fsubst_eq_repl [ // | // ]
    @(subset_eq_trans … (unwind2_term_iref …))
    @(subset_eq_canc_sn … (lift_term_eq_repl_dx …))
    [ @unwind2_term_grafted_S /2 width=2 by ex_intro/ | skip ] -Ht1
    @(subset_eq_trans … (unwind2_lift_term_after …))
    @unwind2_term_eq_repl_sn
(* Note: crux of the proof begins *)
    @nstream_eq_inv_ext #m
    <tr_compose_pap <tr_compose_pap
    <tr_uni_pap <tr_uni_pap <tr_pap_plus
    >list_append_rcons_sn in H1n; <reverse_append #H1n
    lapply (unwind2_rmap_append_pap_closed f … H1n) #H2n
    >nrplus_inj_dx in ⊢ (???%); <H2n -H2n
    lapply (tls_unwind2_rmap_append_closed f … H1n) #H2n
    <(tr_pap_eq_repl … H2n) -H2n -H1n //
(* Note: crux of the proof ends *)
  | //
  | /2 width=2 by ex_intro/
  | //
  ]
]
qed.
*)