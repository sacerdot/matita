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

include "delayed_updating/unwind_k/unwind2_prototerm.ma".
include "delayed_updating/unwind_k/unwind2_path_append.ma".
include "delayed_updating/syntax/preterm.ma".
include "delayed_updating/syntax/path_structure_inner.ma".
include "ground/lib/subset_equivalence.ma".

(* TAILED UNWIND FOR PRETERM ************************************************)

(* Constructions with subset_equivalence ************************************)

lemma unwind2_term_grafted_sn (f) (t) (p): p Ļµ š ā
      ā¼[ā¶[f]p](tāp) ā (ā¼[f]t)ā(āp).
#f #t #p #Hp #q * #r #Hr #H0 destruct
@(ex2_intro ā¦ Hr) -Hr
<unwind2_path_append_pic_sn //
qed-.

lemma unwind2_term_grafted_dx (f) (t) (p): p Ļµ š ā p Ļµ āµt ā t Ļµ š ā
      (ā¼[f]t)ā(āp) ā ā¼[ā¶[f]p](tāp).
#f #t #p #H1p #H2p #Ht #q * #r #Hr #H0
elim (unwind2_path_des_append_pic_sn ā¦ (sym_eq ā¦ H0)) -H0 //
#p0 #q0 #Hp0 #Hq0 #H0 destruct
>(Ht ā¦ Hp0) [|*: /2 width=2 by ex_intro/ ] -p
/2 width=1 by in_comp_unwind2_path_term/
qed-.

lemma unwind2_term_grafted (f) (t) (p): p Ļµ š ā p Ļµ āµt ā t Ļµ š ā
      ā¼[ā¶[f]p](tāp) ā (ā¼[f]t)ā(āp).
/3 width=1 by unwind2_term_grafted_sn, unwind2_term_grafted_dx, conj/ qed.

lemma unwind2_term_grafted_S_dx (f) (t) (p): p Ļµ āµt ā t Ļµ š ā
      (ā¼[f]t)ā((āp)āš¦) ā ā¼[ā¶[f]p](tā(pāš¦)).
#f #t #p #Hp #Ht #q * #r #Hr
>list_append_rcons_sn #H0
elim (unwind2_path_inv_append_ppc_dx ā¦ (sym_eq ā¦ H0)) -H0 //
#p0 #q0 #Hp0 #Hq0 #H0 destruct
>(Ht ā¦ Hp0) [|*: /2 width=2 by ex_intro/ ] -p
elim (eq_inv_S_sn_unwind2_path ā¦ Hq0) -Hq0
#r1 #r2 #Hr1 #Hr2 #H0 destruct
lapply (preterm_in_root_append_inv_structure_empty_dx ā¦ p0 ā¦ Ht Hr1)
[ /2 width=2 by ex_intro/ ] -Hr1 #Hr1 destruct
/2 width=1 by in_comp_unwind2_path_term/
qed-.

lemma unwind2_term_grafted_S (f) (t) (p): p Ļµ āµt ā t Ļµ š ā
      ā¼[ā¶[f]p](tā(pāš¦)) ā (ā¼[f]t)ā((āp)āš¦).
#f #t #p #Hp #Ht
@conj
[ >unwind2_rmap_S_dx >structure_S_dx
  @unwind2_term_grafted_sn // (**) (* auto fails *)
| /2 width=1 by unwind2_term_grafted_S_dx/
]
qed.
