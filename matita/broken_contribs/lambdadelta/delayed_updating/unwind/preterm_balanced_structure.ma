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

include "delayed_updating/syntax/preterm_balanced.ma".
include "delayed_updating/unwind/unwind2_preterm.ma".

(* PRETERM ******************************************************************)

(* Helper constructions *****************************************************)

lemma unwind2_path_help_pbLq (f) (p) (b) (q:ℙ):
      ⊗p●⊗b●𝗟◗▼[⫯▶[p●b]f]q = ▼[f](p●b●𝗟◗q).
#f #p #b #q
>list_append_assoc in ⊢ (???%);
<unwind2_path_append_ppc_dx //
qed.

(* Main destructions with pbc and structure *********************************)

theorem term_in_comp_structure_pbc_L_inj (t) (p) (b1) (b2) (q1) (q2):
        t ϵ 𝐓 → ⊗b1 ϵ 𝐁 → ⊗b2 ϵ 𝐁 →
        p●b1●𝗟◗q1 ϵ t → p●b2●𝗟◗q2 ϵ t → b1 = b2.
#t #p #b1 #b2 #q1 #q2 #Ht #Hb1 #Hb2 #H1t #H2t
lapply (in_comp_unwind2_bi (𝐢) … H1t)
lapply (in_comp_unwind2_bi (𝐢) … H2t)
<unwind2_path_help_pbLq <unwind2_path_help_pbLq #H4t #H3t
lapply (term_in_comp_pbc_L_inj … Hb1 … Hb2 … H3t H4t) -Hb1 -Hb2 -H3t -H4t 
[ /2 width=1 by unwind2_preterm/ ] #H0
@(term_root_eq_inv_structure_L_bi … p … Ht … H0)
/2 width=2 by term_in_root/
qed-.
