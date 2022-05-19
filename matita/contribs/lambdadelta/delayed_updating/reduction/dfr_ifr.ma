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

include "delayed_updating/unwind1/unwind_fsubst.ma".
include "delayed_updating/unwind1/unwind_constructors.ma".
include "delayed_updating/unwind1/unwind_preterm_eq.ma".
include "delayed_updating/unwind1/unwind_structure_depth.ma".
include "delayed_updating/unwind1/unwind_depth.ma".

include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".
include "delayed_updating/syntax/prototerm_proper_constructors.ma".
include "delayed_updating/syntax/path_structure_depth.ma".
include "ground/relocation/tr_uni_compose.ma".
include "ground/relocation/tr_pap_pushs.ma".

(* DELAYED FOCUSED REDUCTION ************************************************)

(* COMMENT
axiom pippo (b) (q) (n):
      ↑❘q❘ = (↑[q]𝐢)＠⧣❨n❩ →
      ↑❘q❘+❘b❘= (↑[b●𝗟◗q]𝐢)＠⧣❨n+❘b❘❩.

lemma unwind_rmap_tls_eq_id (p) (n):
      ❘p❘ = ↑[p]𝐢＠⧣❨n❩ →
      (𝐢) ≗ ⇂*[n]↑[p]𝐢.
#p @(list_ind_rcons … p) -p
[ #n <depth_empty #H destruct
| #p * [ #m ] #IH #n
  [ <depth_d_dx <unwind_rmap_pap_d_dx #H0
    @(stream_eq_trans … (unwind_rmap_tls_d_dx …))
    @(stream_eq_trans … (IH …)) -IH //
  | /2 width=1 by/
  | <depth_L_dx <unwind_rmap_L_dx
    cases n -n [| #n ] #H0
    [
    | 
    ]
  | /2 width=1 by/
  | /2 width=1 by/
  ]
]


(*  (↑❘q❘+❘b❘=↑[b●𝗟◗q]𝐢＠⧣❨n+❘b❘❩ *)
(* [↑[p]𝐢＠⧣❨n❩]⫯*[❘p❘]f∘⇂*[n]↑[p]𝐢) *)
lemma unwind_rmap_tls_eq (f) (p) (n):
      ❘p❘ = ↑[p]𝐢＠⧣❨n❩ →
      f ≗ ⇂*[n]↑[p]f.
#f #p #n #Hp
@(stream_eq_canc_dx … (stream_tls_eq_repl …))
[| @unwind_rmap_decompose | skip ]
<tr_compose_tls <Hp

@(stream_eq_canc_dx) … (unwind_rmap_decompose …)) 

*)
lemma dfr_unwind_id_bi (p) (q) (t1) (t2): t1 ϵ 𝐓 →
      t1 ➡𝐝𝐟[p,q] t2 → ▼[𝐢]t1 ➡𝐟[⊗p,⊗q] ▼[𝐢]t2.
#p #q #t1 #t2 #H0t1
* #b #n * #Hb #Hn #Ht1 #Ht2
@(ex1_2_intro … (⊗b) (↑♭⊗q)) @and4_intro
[ //
| (*//*)
| lapply (in_comp_unwind_bi (𝐢) … Ht1) -Ht1 -H0t1 -Hb -Ht2
  <unwind_path_d_empty_dx <depth_structure //
| lapply (unwind_term_eq_repl_dx (𝐢) … Ht2) -Ht2 #Ht2
  @(subset_eq_trans … Ht2) -t2
  @(subset_eq_trans … (unwind_fsubst …))
  [ (*<unwind_rmap_append <unwind_rmap_A_sn <unwind_rmap_append <unwind_rmap_L_sn *)
    <structure_append <structure_A_sn <structure_append <structure_L_sn
    <depth_append <depth_L_sn <depth_structure <depth_structure
    @fsubst_eq_repl [ // ]
    @(subset_eq_trans … (unwind_iref …))

    elim Hb -Hb #Hb #H0 <H0 -H0 <nrplus_zero_dx <nplus_zero_dx <nsucc_unfold
    >Hn
    @(subset_eq_canc_sn … (lift_term_eq_repl_dx …))
    [ @unwind_grafted_S /2 width=2 by ex_intro/ | skip ]
    <Hn <Hn
(*    
    @(subset_eq_trans … (lift_term_eq_repl_dx …))
    [ @(unwind_term_eq_repl_sn … (tls_succ_unwind q …)) | skip ]
*)
(*
    
    @subset_eq_trans
    [2: @unwind_term_eq_repl_dx
    @(subset_eq_canc_sn … (unwind_term_eq_repl_dx …))

    @(subset_eq_canc_sn … (unwind_term_eq_repl_dx …))
    [ @unwind_grafted_S /2 width=2 by ex_intro/ | skip ]

    @(subset_eq_trans … (unwind_term_after …))
    @(subset_eq_canc_dx … (unwind_term_after …))
    @unwind_term_eq_repl_sn -t1
    @(stream_eq_trans … (tr_compose_uni_dx …))
    lapply (Hn (𝐢)) -Hn >tr_id_unfold #Hn
    lapply (pippo … b … Hn) -Hn #Hn
    @tr_compose_eq_repl
    [ <unwind_rmap_pap_le //
      <Hn <nrplus_inj_sn //
    |
    ]
*)
  | //
  | /2 width=2 by ex_intro/
  | //
  ]
]

(*
Hn : ↑❘q❘ = ↑[p●𝗔◗b●𝗟◗q]𝐢＠⧣❨n❩
---------------------------
↑[𝐮❨↑❘q❘+❘b❘❩] ↑[↑[p]𝐢] t ⇔ ↑[𝐮❨↑[p●𝗔◗b●𝗟◗q]𝐢＠⧣❨n+❘b❘❩❩] t
*)
(*
(↑[𝐮❨↑❘q❘❩]▼[⇂*[↑❘q❘]▼[p●𝗟◗q]𝐢](t1⋔(p◖𝗦))⇔▼[𝐮❨↑❘q❘❩∘▼[p●𝗔◗b●𝗟◗q]𝐢](t1⋔(p◖𝗦))
*)
