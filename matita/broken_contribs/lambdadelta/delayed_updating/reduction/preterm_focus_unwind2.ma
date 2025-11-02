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

include "ground/relocation/fb/fbr_lapp.ma".
include "delayed_updating/syntax/preterm_eq.ma".
include "delayed_updating/unwind/unwind2_path_beta.ma".
include "delayed_updating/unwind/unwind2_prototerm_eq.ma".
include "delayed_updating/unwind/unwind2_preterm.ma".
include "delayed_updating/reduction/prototerm_focus.ma".

(* BALANCED REDUCTION FOCUS *************************************************)

(* Constructions with unwind2 ***********************************************)

lemma brf_unwind2 (f) (t) (p) (b) (q) (n):
      t ϵ 𝐓 → 𝐫❨p,b,q,⁤↑n❩ ϵ t →
      (𝐅❨▼[f]t,⊗p,⊗b,⊗q,(▶[𝐫❨p,b,q❩]f)＠§❨n❩❩) ⇔ ▼[f](𝐅❨t,p,b,q,n❩).
#f #t #p #b #q #n #Ht #Hn
@(subset_eq_canc_sx … (term_slice_complete …))
[ /2 width=1 by in_comp_unwind2_bi/ | /2 width=1 by unwind2_preterm/ ]
@(subset_eq_trans … (unwind2_term_eq_repl_dx …))
[2: @(term_slice_complete … Ht Hn) |3: skip ]
@(subset_eq_trans … (unwind2_term_single …))
<unwind2_path_beta //
qed.
