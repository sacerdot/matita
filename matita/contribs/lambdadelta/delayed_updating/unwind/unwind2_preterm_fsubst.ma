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

include "delayed_updating/unwind/unwind2_prototerm_eq.ma".
include "delayed_updating/unwind/unwind2_path_structure.ma".
include "delayed_updating/substitution/fsubst.ma".
include "delayed_updating/syntax/preterm.ma".
include "delayed_updating/syntax/prototerm_proper.ma".

(* UNWIND FOR PRETERM *******************************************************)

(* Constructions with fsubst ************************************************)

lemma unwind2_term_fsubst_sn (f) (t) (u) (p): u ϵ 𝐏 →
      (▼[f]t)[⋔(⊗p)←▼[▶[f]pᴿ]u] ⊆ ▼[f](t[⋔p←u]).
#f #t #u #p #Hu #ql * *
[ #rl * #r #Hr #H1 #H2 destruct
  >unwind2_path_append_proper_dx
  /4 width=5 by in_comp_unwind2_path_term, in_comp_tpc_trans, or_introl, ex2_intro/
| * #q #Hq #H1 #H0
  @(ex2_intro … H1) @or_intror @conj // *
  [ <list_append_empty_dx #H2 destruct
    elim (unwind2_path_root f q) #r #_ #Hr /2 width=2 by/
  | #l #r #H2 destruct
    @H0 -H0 [| <unwind2_path_append_proper_dx /2 width=3 by ppc_lcons/ ]
  ]
]
qed-.

lemma unwind2_term_fsubst_dx (f) (t) (u) (p): u ϵ 𝐏 → p ϵ ▵t → t ϵ 𝐓 →
      ▼[f](t[⋔p←u]) ⊆ (▼[f]t)[⋔(⊗p)←▼[▶[f]pᴿ]u].
#f #t #u #p #Hu #H1p #H2p #ql * #q * *
[ #r #Hu #H1 #H2 destruct
  @or_introl @ex2_intro
  [|| <unwind2_path_append_proper_dx /2 width=5 by in_comp_tpc_trans/ ]
  /2 width=3 by ex2_intro/
| #Hq #H0 #H1 destruct
  @or_intror @conj [ /2 width=1 by in_comp_unwind2_path_term/ ] *
  [ <list_append_empty_dx #Hr @(H0 … (𝐞)) -H0
    <list_append_empty_dx @H2p -H2p
    /2 width=2 by unwind_gen_des_structure, prototerm_in_comp_root/
  | #l #r #Hr
    elim (unwind2_path_inv_append_proper_dx … Hr) -Hr // #s1 #s2 #Hs1 #_ #H1 destruct
    lapply (H2p … Hs1) -H2p -Hs1 /2 width=2 by ex_intro/
  ]
]
qed-.

lemma unwind2_term_fsubst (f) (t) (u) (p): u ϵ 𝐏 → p ϵ ▵t → t ϵ 𝐓 →
      (▼[f]t)[⋔(⊗p)←▼[▶[f]pᴿ]u] ⇔ ▼[f](t[⋔p←u]).
/4 width=3 by unwind2_term_fsubst_sn, conj, unwind2_term_fsubst_dx/ qed.
