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

include "delayed_updating/substitution/fsubst.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".
include "delayed_updating/substitution/lift_structure.ma".
include "delayed_updating/syntax/preterm.ma".
include "delayed_updating/syntax/prototerm_proper.ma".

(* FOCALIZED SUBSTITUTION ***************************************************)

lemma lift_fsubst_sn (f) (t) (u) (p): u ϵ 𝐏 →
      (↑[f]t)[⋔(⊗p)←↑[↑[p]f]u] ⊆ ↑[f](t[⋔p←u]).
#f #t #u #p #Hu #ql * *
[ #rl * #r #Hr #H1 #H2 destruct
  >lift_append_proper_dx
  /4 width=5 by in_comp_lift_bi, in_ppc_comp_trans, or_introl, ex2_intro/
| * #q #Hq #H1 #H0
  @(ex2_intro … H1) @or_intror @conj // *
  [ <list_append_empty_dx #H2 destruct
    elim (lift_root f q) #r #_ #Hr /2 width=2 by/
  | #l #r #H2 destruct
    @H0 -H0 [| <lift_append_proper_dx /2 width=3 by ppc_lcons/ ]
  ]
]
qed-.

lemma lift_fsubst_dx (f) (t) (u) (p): u ϵ 𝐏 → p ϵ ▵t → t ϵ 𝐓 →
      ↑[f](t[⋔p←u]) ⊆ (↑[f]t)[⋔(⊗p)←↑[↑[p]f]u].
#f #t #u #p #Hu #H1p #H2p #ql * #q * *
[ #r #Hu #H1 #H2 destruct
  @or_introl @ex2_intro
  [|| <lift_append_proper_dx /2 width=5 by in_ppc_comp_trans/ ]
  /2 width=3 by ex2_intro/
| #Hq #H0 #H1 destruct
  @or_intror @conj [ /2 width=1 by in_comp_lift_bi/ ] *
  [ <list_append_empty_dx #Hr @(H0 … (𝐞)) -H0
    <list_append_empty_dx @H2p -H2p /2 width=1 by prototerm_in_comp_root/
  | #l #r #Hr
    elim (lift_inv_append_proper_dx … Hr) -Hr // #s1 #s2 #Hs1 #_ #H1 destruct
    lapply (H2p … Hs1) -H2p -Hs1 /2 width=2 by ex_intro/
  ]
]
qed-.

lemma lift_fsubst (f) (t) (u) (p): u ϵ 𝐏 → p ϵ ▵t → t ϵ 𝐓 →
      (↑[f]t)[⋔(⊗p)←↑[↑[p]f]u] ⇔ ↑[f](t[⋔p←u]).
/4 width=3 by lift_fsubst_sn, conj, lift_fsubst_dx/ qed.
