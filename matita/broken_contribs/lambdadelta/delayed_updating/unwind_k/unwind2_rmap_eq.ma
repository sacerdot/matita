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

include "delayed_updating/unwind_k/unwind2_rmap.ma".
include "delayed_updating/unwind_k/preunwind2_rmap_eq.ma".
include "ground/relocation/tr_uni_compose.ma".
include "ground/arith/nat_rplus_pplus.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Constructions with tr_map_eq *********************************************)

lemma unwind2_rmap_eq_repl (p):
      stream_eq_repl … (λf1,f2. ▶[f1]p ≗ ▶[f2]p).
#p elim p -p //
#l #p #IH #f1 #f2 #Hf
/3 width=1 by preunwind2_rmap_eq_repl/
qed-.

lemma tls_unwind2_rmap_d_dx (f) (p) (h) (k):
      ⇂*[h+k]▶[f]p ≗ ⇂*[h]▶[f](p◖𝗱k).
#f #p #h #k
<unwind2_rmap_d_dx >nrplus_inj_dx
/2 width=1 by tr_tls_compose_uni_dx/
qed.
