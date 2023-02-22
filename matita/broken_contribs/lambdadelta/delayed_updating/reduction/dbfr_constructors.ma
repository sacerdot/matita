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

include "delayed_updating/reduction/dbfr.ma".
include "delayed_updating/substitution/fsubst_constructors.ma".
include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/syntax/prototerm_constructors_eq.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Constructions with constructors for prototerm ****************************)

lemma dbfr_abst_hd (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t2 → 𝛌.t1 ➡𝐝𝐛𝐟[𝗟◗r] 𝛌.t2.
#t1 #t2 #r *
#p #b #q #m #n #Hr #Hb #Hm #Hn #Ht1 #Ht2 destruct
@(ex6_5_intro … (𝗟◗p) … Hb Hm Hn) -Hb -Hm -Hn
[ -Ht2 //
| -Ht2 /2 width=1 by in_comp_abst_hd/
| @(subset_eq_trans … (abst_eq_repl … Ht2)) -Ht1 -Ht2
  @(subset_eq_canc_sn … (fsubst_abst_hd …)) @abst_eq_repl
  @fsubst_eq_repl // @iref_eq_repl
  >list_cons_shift @(subset_eq_canc_sn … (grafted_abst_hd … )) //
]
qed.

lemma dbfr_appl_hd (v) (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t2 → ＠v.t1 ➡𝐝𝐛𝐟[𝗔◗r] ＠v.t2.
#v #t1 #t2 #r *
#p #b #q #m #n #Hr #Hb #Hm #Hn #Ht1 #Ht2 destruct
@(ex6_5_intro … (𝗔◗p) … Hb Hm Hn) -Hb -Hm -Hn
[ -Ht2 //
| -Ht2 /2 width=1 by in_comp_appl_hd/
| @(subset_eq_trans … (appl_eq_repl … Ht2)) -Ht1 -Ht2 [|*: // ]
  @(subset_eq_canc_sn … (fsubst_appl_hd …)) @appl_eq_repl [ // ]
  @fsubst_eq_repl // @iref_eq_repl
  >list_cons_shift @(subset_eq_canc_sn … (grafted_appl_hd … )) //
]
qed.

lemma dbfr_appl_sd (v1) (v2) (t) (r):
      v1 ➡𝐝𝐛𝐟[r] v2 → ＠v1.t ➡𝐝𝐛𝐟[𝗦◗r] ＠v2.t.
#v1 #v2 #t #r *
#p #b #q #m #n #Hr #Hb #Hm #Hn #Hv1 #Hv2 destruct
@(ex6_5_intro … (𝗦◗p) … Hb Hm Hn) -Hb -Hm -Hn
[ -Hv2 //
| -Hv2 /2 width=1 by in_comp_appl_sd/
| @(subset_eq_trans ????? (appl_eq_repl …)) [3: @Hv2 |2,4: // |5: skip ]
  @(subset_eq_canc_sn … (fsubst_appl_sd …)) @appl_eq_repl [| // ]
  @fsubst_eq_repl // @iref_eq_repl
  >list_cons_shift @(subset_eq_canc_sn … (grafted_appl_sd … )) //
]
qed.

lemma dbfr_beta_0 (v) (t) (q) (n):
      q ϵ 𝐂❨Ⓕ,n,𝟎❩ → q◖𝗱↑n ϵ t →
      ＠v.𝛌.t ➡𝐝𝐛𝐟[𝗔◗𝗟◗q] ＠v.𝛌.(t[⋔q←𝛕↑n.v]).
#v #t #q #n #Hn #Ht
@(ex6_5_intro … (𝐞) (𝐞) q (𝟎) … Hn) -Hn
[ //
| //
| //
| /3 width=1 by in_comp_appl_hd, in_comp_abst_hd/
| @(subset_eq_canc_sn … (fsubst_appl_hd …)) @appl_eq_repl [ // ]
  @(subset_eq_canc_sn … (fsubst_abst_hd …)) @abst_eq_repl
  @fsubst_eq_repl // <nplus_zero_sn @iref_eq_repl
  >list_cons_comm @(subset_eq_canc_sn … (grafted_appl_sd … ))
  @(subset_eq_canc_sn … (grafted_empty_dx … )) //
]
qed.
(*
lemma dbfr_beta_1 (v) (v1) (t) (q) (n):
      q ϵ 𝐂❨Ⓕ,n❩ → q◖𝗱↑n ϵ t →
      ＠v.＠v1.𝛌.𝛌.t ➡𝐝𝐛𝐟[𝗔◗𝗔◗𝗟◗𝗟◗q] ＠v.＠v1.𝛌.𝛌.(t[⋔q←𝛕↑↑n.v]).
#v #v1 #t #q #n #Hn #Ht
@(ex6_5_intro … (𝐞) (𝗔◗𝗟◗𝐞) q (𝟏) … Hn) -Hn
[ //
| /2 width=1 by pbc_empty, pbc_redex/
| /3 width=1 by pcc_A_sn, pcc_L_sn, pcc_empty/
| /5 width=1 by in_comp_appl_hd, in_comp_abst_hd/
| @(subset_eq_canc_sn … (fsubst_appl_hd …)) @appl_eq_repl [ // ]
  @(subset_eq_canc_sn … (fsubst_appl_hd …)) @appl_eq_repl [ // ]
  @(subset_eq_canc_sn … (fsubst_abst_hd …)) @abst_eq_repl
  @(subset_eq_canc_sn … (fsubst_abst_hd …)) @abst_eq_repl
  @fsubst_eq_repl // <nplus_unit_sn @lift_term_eq_repl_dx
  >list_cons_comm @(subset_eq_canc_sn … (grafted_appl_sd … ))
  @(subset_eq_canc_sn … (grafted_empty_dx … )) //
]
qed.
*)
