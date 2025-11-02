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

include "delayed_updating/reduction/dbf_step.ma".
include "delayed_updating/substitution/fsubst_constructors.ma".
include "delayed_updating/syntax/prototerm_constructors_eq.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Constructions with constructors for prototerm ****************************)

(* UPDATE *)

lemma dbfs_abst_hd (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t2 → 𝛌.t1 ➡𝐝𝐛𝐟[𝗟◗r] 𝛌.t2.
#t1 #t2 #r *
#p #b #q #n * #Hr #Hb #Hn #Ht1 #Ht2 destruct
>path_clear_L_sx >path_beta_append_p
@(dbfs_mk … (xprc_mk …  Hb Hn) …) -Hb -Hn
[| <brd_unfold ]
[ -Ht2 /2 width=1 by in_comp_abst_hd/
| @subset_eq_canc_sx [|| @(abst_eq_repl … Ht2) ] -Ht1 -Ht2
  @subset_eq_trans [| @fsubst_abst_hd ]
  @fsubst_eq_repl [ // | // ]
  @subset_eq_trans [| @pt_append_assoc ]
  @pt_append_eq_repl_bi [ // ]
  @term_grafted_abst_hd
]
qed.

lemma dbfs_appl_hd (v) (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t2 → ＠v.t1 ➡𝐝𝐛𝐟[𝗔◗r] ＠v.t2.
#v #t1 #t2 #r *
#p #b #q #n * #Hr #Hb #Hn #Ht1 #Ht2 destruct
>path_clear_A_sx >path_beta_append_p
@(dbfs_mk … (xprc_mk …  Hb Hn) …) -Hb -Hn
[| <brd_unfold ]
[ -Ht2 /2 width=1 by in_comp_appl_hd/
| @subset_eq_canc_sx [|| @(appl_eq_repl … Ht2) // ] -Ht1 -Ht2
  @subset_eq_trans [| @fsubst_appl_hd ]
  @fsubst_eq_repl [ // | // ]
  @subset_eq_trans [| @pt_append_assoc ]
  @pt_append_eq_repl_bi [ // ]
  @term_grafted_appl_hd
]
qed.

lemma dbfs_appl_sd (v1) (v2) (t) (r):
      v1 ➡𝐝𝐛𝐟[r] v2 → ＠v1.t ➡𝐝𝐛𝐟[𝗦◗r] ＠v2.t.
#v1 #v2 #t #r *
#p #b #q #n * #Hr #Hb #Hn #Hv1 #Hv2 destruct
>path_clear_S_sx >path_beta_append_p
@(dbfs_mk … (xprc_mk …  Hb Hn) …) -Hb -Hn
[| <brd_unfold ]
[ -Hv2 /2 width=1 by in_comp_appl_sd/
| @subset_eq_canc_sx [|| @(appl_eq_repl … Hv2) // ] -Hv1 -Hv2
  @subset_eq_trans [| @fsubst_appl_sd ]
  @fsubst_eq_repl [ // | // ]
  @subset_eq_trans [| @pt_append_assoc ]
  @pt_append_eq_repl_bi [ // ]
  @term_grafted_appl_sd
]
qed.

(* Note: improve by carrying b●𝛌⓪ out of the substitution *)
lemma dbfs_beta (v) (b) (t) (q) (n):
      ⊗b ϵ 𝐁 → q ϵ 𝐂❨n❩ → q◖𝗱(⁤↑n) ϵ t →
      (＠v.(b●𝛌.t)) ➡𝐝𝐛𝐟[⓪𝐫❨𝐞,b,q,⁤↑n❩] ＠v.(⬕[↑(b●𝗟◗q◖𝗱(⁤↑n))←(⓪b●𝗟◗q◖𝗱(⁤↑(♭b+n)))●v](b●𝛌.t)).
#v #b #t #q #n #Hb #Hn #Ht
@(dbfs_mk … (xprc_mk …  Hb Hn) …) -Hb -Hn
[ <path_beta_unfold_dx <list_append_empty_dx | <brxf_unfold <brd_unfold ]
[ /4 width=1 by in_comp_appl_hd, in_comp_abst_hd, pt_append_in/
| @subset_eq_canc_dx [3: @fsubst_appl_hd | skip ]
  @fsubst_eq_repl [ // ]
  [ @subset_eq_canc_dx [3: @term_slice_append | skip ] //
  | @subset_eq_canc_dx [3: @pt_append_assoc | skip ]
    @pt_append_eq_repl_bi [ <path_beta_unfold_dx <list_append_empty_dx // ]
    >list_cons_comm
    @subset_eq_canc_sx [| @term_grafted_appl_sd ]
    @subset_eq_sym //
  ]
]
qed.
