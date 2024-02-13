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

include "delayed_updating/unwind/unwind2_preterm.ma".
include "delayed_updating/syntax/prototerm_eq.ma".
include "ground/lib/subset_and.ma".

(* TAILED UNWIND FOR PRETERM ************************************************)

(* Inversions with term_slice ***********************************************)

lemma in_comp_slice_inv_unwind2_bi (f) (t) (p) (r) (k):
      t ϵ 𝐓 → p◖𝗱k ϵ t → r ϵ t →
      ▼[f]r ϵ ↑⊗p → r ϵ ↑p.
#f #t #p #r #k #Ht #Hp #Hr * #s #_ #H0
elim (unwind2_path_des_append_pic_sn … (sym_eq … H0)) //
#p0 #s0 #Hp0 #H0 #H1 #H2 destruct
elim (term_root_pic_sn … Ht … (sym_eq … H0)) -H0
[|*: /2 width=2 by term_in_root/ ]
#q0 #H0 #Hq0 destruct
>list_append_lcons_sn in Hp; #Hp
lapply (term_comp_inv … Hr Hp ?) -Hp -Hr // #H0 destruct
/2 width=1 by append_in_comp_slice_bi/
qed-.

(* Constructions with subset_eq *********************************************)
(*
lemma unwind_term_and (f) (u1) (u2):
      ▼[f]u1 ∩ ▼[f]u2 ⇔ ▼[f](u1 ∩ u2).
#f #u1 #u2
@subset_and_ext_f1
#p1 #p2 #Hp1 #Hp2 #Hp
*)
lemma unwind2_term_grafted_pic_sn (f) (t) (p):
      p ϵ 𝐈 →
      ▼[▶[p]f]⋔[p]t ⊆ ⋔[⊗p]▼[f]t.
#f #t #p #Hp #q * #r #Hr #H0 destruct
/3 width=3 by unwind2_path_append_pic_sn, ex2_intro/
qed-.

lemma unwind2_term_grafted_pic_dx (f) (t) (p):
      t ϵ 𝐓 → p ϵ 𝐈 → p ϵ ▵t →
      (⋔[⊗p]▼[f]t) ⊆ ▼[▶[p]f]⋔[p]t.
#f #t #p #Ht #H1p #H2p #q * #r #Hr #H0
elim (unwind2_path_des_append_pic_sn … (sym_eq … H0)) -H0 //
#p0 #q0 #H1p0 #H2p0 #H1 #H2 destruct
lapply (term_root_pic_bi … Ht … H2p0) -H2p0 //
[ /2 width=2 by term_in_root/
| #H0 destruct -Ht -H1p0 -H1p -H2p
  /2 width=1 by in_comp_unwind2_bi/
]
qed-.

lemma unwind2_term_grafted_pic (f) (t) (p):
      t ϵ 𝐓 → p ϵ 𝐈 → p ϵ ▵t →
      ▼[▶[p]f]⋔[p]t ⇔ ⋔[⊗p]▼[f]t.
/3 width=1 by unwind2_term_grafted_pic_sn, unwind2_term_grafted_pic_dx, conj/
qed.

lemma unwind2_term_grafted_S_dx (f) (t) (p):
      t ϵ 𝐓 → p◖𝗔 ϵ ▵t →
      ▼[▶[p]f]⋔[p◖𝗦]t ⇔ ⋔[(⊗p)◖𝗦]▼[f]t.
#f #t #p #Ht #Hp
/3 width=1 by unwind2_term_grafted_pic, term_full_A_post/
qed.

lemma unwind2_term_grafted_ppc_sn (f) (t) (p):
      (⋔[p]t) ⊆ 𝐏 →
      ▼[▶[p]f]⋔[p]t ⊆ ⋔[⊗p]▼[f]t.
#f #t #p #Ht #q * #r #H1r #H0 destruct
lapply (Ht … H1r) -Ht #H2r
/3 width=3 by unwind2_path_append_ppc_dx, ex2_intro/
qed-.

lemma unwind2_slice_and_sn (f) (t) (p) (k):
      t ϵ 𝐓 → p◖𝗱k ϵ t →
      (▼[f]t) ∩ ↑⊗p ⇔ ▼[f](t ∩ ↑p).
#f #t #p #l #Ht #Hp
@conj #r
[ * * #s #Hs #H0 #Hr destruct
  /4 width=5 by subset_and_in, in_comp_unwind2_bi, in_comp_slice_inv_unwind2_bi/
| * #s * #H1s #H2s #H0 destruct
  @subset_and_in
  [ /2 width=1 by in_comp_unwind2_bi/
  | /2 width=5 by in_comp_slice_unwind2_bi/
  ]
]
qed.
