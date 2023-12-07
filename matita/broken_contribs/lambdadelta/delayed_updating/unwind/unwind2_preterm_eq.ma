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

include "delayed_updating/unwind/unwind2_prototerm.ma".
include "delayed_updating/unwind/unwind2_path_append.ma".
include "delayed_updating/syntax/preterm_inner.ma".
include "ground/lib/subset_eq.ma".

(* TAILED UNWIND FOR PRETERM ************************************************)

(* Constructions with subset_eq *********************************************)

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
/3 width=1 by unwind2_term_grafted_pic, term_full_A_ax/
qed.

lemma unwind2_term_grafted_ppc_sn (f) (t) (p):
      (⋔[p]t) ⊆ 𝐏 →
      ▼[▶[p]f]⋔[p]t ⊆ ⋔[⊗p]▼[f]t.
#f #t #p #Ht #q * #r #H1r #H0 destruct
lapply (Ht … H1r) -Ht #H2r
/3 width=3 by unwind2_path_append_ppc_dx, ex2_intro/
qed-.
