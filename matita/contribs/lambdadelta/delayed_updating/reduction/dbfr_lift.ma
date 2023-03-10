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

include "delayed_updating/substitution/fsubst_lift.ma".
include "delayed_updating/substitution/fsubst_eq.ma".
include "delayed_updating/substitution/lift_prototerm_constructors.ma".
include "delayed_updating/substitution/lift_path_structure.ma".
include "delayed_updating/substitution/lift_path_closed.ma".
include "delayed_updating/substitution/lift_rmap_closed.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Constructions with lift **************************************************)

theorem dbfr_lift_bi (f) (t1) (t2) (r):
        t1 โก๐๐๐[r] t2 โ ๐ ก[f]t1 โก๐๐๐[๐ ก[f]r] ๐ ก[f]t2.
#f #t1 #t2 #r
* #p #b #q #m #n #Hr #Hb #Hm #Hn #Ht1 #Ht2 destruct
@(ex6_5_intro โฆ (๐ ก[f]p) (๐ ก[๐ ข[f](pโ๐)]b) (๐ ก[๐ ข[f](pโ๐โbโ๐)]q) (๐ ข[f](pโ๐โb)๏ผ โจmโฉ) (๐ ข[f](pโ๐โbโ๐โq)๏ผ ยงโจnโฉ))
[ -Hb -Hm -Hn -Ht1 -Ht2 //
| -Hm -Hn -Ht1 -Ht2 //
| -Hb -Hn -Ht1 -Ht2
  /2 width=1 by lift_path_closed/
| -Hb -Hm -Ht1 -Ht2
  /2 width=1 by lift_path_rmap_closed_L/
| lapply (in_comp_lift_path_term f โฆ Ht1) -Ht2 -Ht1 -Hn
  <lift_path_d_dx #Ht1 //
| lapply (lift_term_eq_repl_dx f โฆ Ht2) -Ht2 #Ht2 -Ht1
  @(subset_eq_trans โฆ Ht2) -t2
  @(subset_eq_trans โฆ (lift_term_fsubst โฆ))
  @fsubst_eq_repl [ // | // ]
  @(subset_eq_trans โฆ (lift_term_iref_nap โฆ))
  <list_append_rcons_sn <list_append_rcons_sn >list_append_assoc
  >(nap_plus_lift_rmap_append_closed_Lq_dx โฆ Hn)
  @iref_eq_repl
  @(subset_eq_canc_sn โฆ (lift_term_grafted_S โฆ))
  @lift_term_eq_repl_sn
(* ๐ ข[f]p โ โ*[โ(m+n)]๐ ข[f](((pโ๐)โb)โ๐โq) *)
(* Note: crux of the proof begins *)
  >lift_rmap_A_dx
  /2 width=2 by tls_succ_plus_lift_rmap_append_closed_bLq_dx/
(* Note: crux of the proof ends *)
]
qed.
