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

include "delayed_updating/unwind/unwind2_path.ma".
include "delayed_updating/unwind/unwind_gen_structure.ma".

(* UNWIND FOR PATH **********************************************************)

(* Constructions with list_rcons ********************************************)

lemma unwind2_path_d_dx (f) (p) (n) :
      (⊗p)◖𝗱((▶[f](pᴿ))＠⧣❨n❩) = ▼[f](p◖𝗱n).
#f #p #n <unwind2_path_unfold
<unwind_gen_d_dx //
qed.

lemma unwind2_path_m_dx (f) (p):
      ⊗p = ▼[f](p◖𝗺).
#f #p <unwind2_path_unfold //
qed.

lemma unwind2_path_L_dx (f) (p):
      (⊗p)◖𝗟 = ▼[f](p◖𝗟).
#f #p <unwind2_path_unfold //
qed.

lemma unwind2_path_A_dx (f) (p):
      (⊗p)◖𝗔 = ▼[f](p◖𝗔).
#f #p <unwind2_path_unfold //
qed.

lemma unwind2_path_S_dx (f) (p):
      (⊗p)◖𝗦 = ▼[f](p◖𝗦).
#f #p <unwind2_path_unfold //
qed.

lemma unwind2_path_root (f) (p):
      ∃∃r. 𝐞 = ⊗r & ⊗p●r = ▼[f]p.
#f #p
elim (unwind_gen_root)
/2 width=3 by ex2_intro/
qed-.

(* Constructions with proper condition for path *****************************)

lemma unwind2_path_append_proper_dx (f) (p1) (p2): p2 ϵ 𝐏 →
      (⊗p1)●(▼[▶[f]p1ᴿ]p2) = ▼[f](p1●p2).
#f #p1 #p2 #Hp2 <unwind2_path_unfold <unwind2_path_unfold
<unwind_gen_append_proper_dx // -Hp2 <reverse_append
@(list_ind_rcons … p2) -p2 // #q2 #l2 #_
<reverse_rcons <list_tl_lcons <list_tl_lcons //
qed-.

(* Constructions with inner condition for path ******************************)

lemma unwind2_path_append_inner_sn (f) (p1) (p2): p1 ϵ 𝐈 →
      (⊗p1)●(▼[▶[f]p1ᴿ]p2) = ▼[f](p1●p2).
#f #p1 #p2 #Hp1 <unwind2_path_unfold <unwind2_path_unfold
<unwind_gen_append_inner_sn // -Hp1 <reverse_append
@(list_ind_rcons … p2) -p2 // #q2 #l2 #_
<reverse_rcons <list_tl_lcons <list_tl_lcons //
qed-.

(* Inversions with list_lcons ***********************************************)

lemma unwind2_path_inv_S_sn (f) (p) (q):
      (𝗦◗q) = ▼[f]p →
      ∃∃r1,r2. 𝐞 = ⊗r1 & q = ▼[▶[f]r1ᴿ]r2 & r1●𝗦◗r2 = p.
#f #p #q #H0
elim (unwind_gen_inv_S_sn … H0) -H0 #r1 #r2 #Hr1 #H1 #H2 destruct
<reverse_append <reverse_lcons
@(list_ind_rcons … r2) -r2 [ /2 width=5 by ex3_2_intro/ ] #r2 #l2 #_
<reverse_rcons <list_append_lcons_sn <list_append_rcons_sn
<list_tl_lcons <unwind2_rmap_append <unwind2_rmap_S_sn
/2 width=5 by ex3_2_intro/
qed-.

(* Inversions with proper condition for path ********************************)

lemma unwind2_path_inv_append_proper_dx (f) (p) (q1) (q2):
      q2 ϵ 𝐏 → q1●q2 = ▼[f]p →
      ∃∃p1,p2. ⊗p1 = q1 & ▼[▶[f]p1ᴿ]p2 = q2 & p1●p2 = p.
#f #p #q1 #q2 #Hq2 #H0
elim (unwind_gen_inv_append_proper_dx … Hq2 H0) -Hq2 -H0
#p1 #p2 #H1 #H2 #H3 destruct <reverse_append
@(list_ind_rcons … p2) -p2 [ /2 width=5 by ex3_2_intro/ ] #q2 #l2 #_
<reverse_rcons <list_tl_lcons <unwind2_rmap_append
@ex3_2_intro [4: |*: // ] <unwind2_path_unfold // (**) (* auto fails *)
qed-.

(* Inversions with inner condition for path *********************************)

lemma unwind2_path_inv_append_inner_sn (f) (p) (q1) (q2):
      q1 ϵ 𝐈 → q1●q2 = ▼[f]p →
      ∃∃p1,p2. ⊗p1 = q1 & ▼[▶[f]p1ᴿ]p2 = q2 & p1●p2 = p.
#f #p #q1 #q2 #Hq1 #H0
elim (unwind_gen_inv_append_inner_sn … Hq1 H0) -Hq1 -H0
#p1 #p2 #H1 #H2 #H3 destruct <reverse_append
@(list_ind_rcons … p2) -p2 [ /2 width=5 by ex3_2_intro/ ] #q2 #l2 #_
<reverse_rcons <list_tl_lcons <unwind2_rmap_append
@ex3_2_intro [4: |*: // ] <unwind2_path_unfold // (**) (* auto fails *)
qed-.
