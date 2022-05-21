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

include "delayed_updating/unwind/unwind2_path.ma".
include "delayed_updating/unwind/unwind2_rmap_eq.ma".
include "delayed_updating/unwind/unwind_gen_eq.ma".
include "ground/relocation/tr_compose_compose.ma".
include "ground/relocation/tr_compose_pn.ma".

(* UNWIND FOR PATH **********************************************************)

(* Constructions with stream_eq *********************************************)

lemma unwind2_path_eq_repl (p):
      stream_eq_repl … (λf1,f2. ▼[f1]p = ▼[f2]p).
/3 width=1 by unwind2_rmap_eq_repl, unwind_gen_eq_repl/
qed-.

(* Properties with tr_compose ***********************************************)

lemma unwind2_path_after (p) (f1) (f2):
      ▼[f2]▼[f1]p = ▼[f2∘f1]p.
#p @(path_ind_unwind … p) -p // [ #n #l #p | #p ] #IH #f1 #f2
[ <unwind2_path_d_lcons <unwind2_path_d_lcons
  >(unwind2_path_eq_repl … (tr_compose_assoc …)) //
| <(unwind2_path_L_sn … f1) <unwind2_path_L_sn <unwind2_path_L_sn
  >tr_compose_push_bi //
]
qed.
