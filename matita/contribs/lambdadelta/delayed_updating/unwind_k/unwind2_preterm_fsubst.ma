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

include "delayed_updating/unwind_k/unwind2_prototerm_eq.ma".
include "delayed_updating/unwind_k/unwind2_path_append.ma".
include "delayed_updating/substitution/fsubst.ma".
include "delayed_updating/syntax/preterm.ma".
include "delayed_updating/syntax/prototerm_proper.ma".

(* TAILED UNWIND FOR PRETERM ************************************************)

(* Constructions with fsubst and pic ****************************************)

lemma unwind2_term_fsubst_pic_sn (f) (t) (u) (p): p ϵ 𝐈 →
      (▼[f]t)[⋔(⊗p)←▼[▶[f]p]u] ⊆ ▼[f](t[⋔p←u]).
#f #t #u #p #Hp #ql * *
[ #rl * #r #Hr #H1 #H2 destruct
  >unwind2_path_append_pic_sn
  /4 width=3 by in_comp_unwind2_path_term, or_introl, ex2_intro/
| * #q #Hq #H1 #H0
  @(ex2_intro … H1) @or_intror @conj // *
  [ <list_append_empty_sn #H2 destruct
    elim (unwind2_path_root f q) #r #_ #Hr /2 width=2 by/
  | #l #r #H2 destruct
    /3 width=2 by unwind2_path_append_pic_sn/
  ]
]
qed-.

lemma unwind2_term_fsubst_pic_dx (f) (t) (u) (p): p ϵ 𝐈 → p ϵ ▵t → t ϵ 𝐓 →
      ▼[f](t[⋔p←u]) ⊆ (▼[f]t)[⋔(⊗p)←▼[▶[f]p]u].
#f #t #u #p #Hp #H1p #H2p #ql * #q * *
[ #r #Hu #H1 #H2 destruct
  /5 width=3 by unwind2_path_append_pic_sn, ex2_intro, or_introl/
| #Hq #H0 #H1 destruct
  @or_intror @conj [ /2 width=1 by in_comp_unwind2_path_term/ ] *
  [ <list_append_empty_sn #Hr @(H0 … (𝐞)) -H0
    <list_append_empty_sn @H2p -H2p
    /2 width=2 by unwind2_path_des_structure, prototerm_in_comp_root/
  | #l #r #Hr
    elim (unwind2_path_inv_append_ppc_dx … Hr) -Hr // #s1 #s2 #Hs1 #_ #H1 destruct
    lapply (H2p … Hs1) -H2p -Hs1 /2 width=2 by ex_intro/
  ]
]
qed-.

lemma unwind2_term_fsubst_pic (f) (t) (u) (p): p ϵ 𝐈 → p ϵ ▵t → t ϵ 𝐓 →
      (▼[f]t)[⋔(⊗p)←▼[▶[f]p]u] ⇔ ▼[f](t[⋔p←u]).
/4 width=3 by unwind2_term_fsubst_pic_sn, conj, unwind2_term_fsubst_pic_dx/ qed.

(* Constructions with fsubst and ppc ****************************************)

lemma unwind2_term_fsubst_ppc_sn (f) (t) (u) (p): u ϵ 𝐏 →
      (▼[f]t)[⋔(⊗p)←▼[▶[f]p]u] ⊆ ▼[f](t[⋔p←u]).
#f #t #u #p #Hu #ql * *
[ #rl * #r #Hr #H1 #H2 destruct
  >unwind2_path_append_ppc_dx
  /4 width=5 by in_comp_unwind2_path_term, in_comp_tpc_trans, or_introl, ex2_intro/
| * #q #Hq #H1 #H0
  @(ex2_intro … H1) @or_intror @conj // *
  [ <list_append_empty_sn #H2 destruct
    elim (unwind2_path_root f q) #r #_ #Hr /2 width=2 by/
  | #l #r #H2 destruct
    @H0 -H0 [| <unwind2_path_append_ppc_dx /2 width=3 by ppc_rcons/ ]
  ]
]
qed-.

lemma unwind2_term_fsubst_ppc_dx (f) (t) (u) (p): u ϵ 𝐏 → p ϵ ▵t → t ϵ 𝐓 →
      ▼[f](t[⋔p←u]) ⊆ (▼[f]t)[⋔(⊗p)←▼[▶[f]p]u].
#f #t #u #p #Hu #H1p #H2p #ql * #q * *
[ #r #Hu #H1 #H2 destruct
  @or_introl @ex2_intro
  [|| <unwind2_path_append_ppc_dx /2 width=5 by in_comp_tpc_trans/ ]
  /2 width=3 by ex2_intro/
| #Hq #H0 #H1 destruct
  @or_intror @conj [ /2 width=1 by in_comp_unwind2_path_term/ ] *
  [ <list_append_empty_sn #Hr @(H0 … (𝐞)) -H0
    <list_append_empty_sn @H2p -H2p
    /2 width=2 by unwind2_path_des_structure, prototerm_in_comp_root/
  | #l #r #Hr
    elim (unwind2_path_inv_append_ppc_dx … Hr) -Hr // #s1 #s2 #Hs1 #_ #H1 destruct
    lapply (H2p … Hs1) -H2p -Hs1 /2 width=2 by ex_intro/
  ]
]
qed-.

lemma unwind2_term_fsubst_ppc (f) (t) (u) (p): u ϵ 𝐏 → p ϵ ▵t → t ϵ 𝐓 →
      (▼[f]t)[⋔(⊗p)←▼[▶[f]p]u] ⇔ ▼[f](t[⋔p←u]).
/4 width=3 by unwind2_term_fsubst_ppc_sn, conj, unwind2_term_fsubst_ppc_dx/ qed.
