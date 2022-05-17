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

include "delayed_updating/unwind/unwind2_rmap.ma".
include "ground/relocation/tr_compose_eq.ma".
include "ground/relocation/tr_pn_eq.ma".

(* UNWIND MAP FOR PATH ******************************************************)

(* Constructions with stream_eq *********************************************)

lemma unwind2_rmap_eq_repl (p):
      stream_eq_repl … (λf1,f2. ▶[f1]p ≗ ▶[f2]p).
#p elim p -p //
* [ #n ] #p #IH #f1 #f2 #Hf
[ /3 width=1 by tr_compose_eq_repl/
| /2 width=1 by/
| /3 width=1 by tr_push_eq_repl/
| /2 width=1 by/
| /2 width=1 by/
]
qed-.
