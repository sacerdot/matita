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

include "delayed_updating/syntax/path_clear_help.ma".
include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/syntax/prototerm_clear.ma".
include "delayed_updating/reduction/prototerm_reducible.ma".
include "delayed_updating/reduction/prototerm_delayed.ma".

(* BALANCED REDUCTION DELAYED SUBREDUCT *************************************)

(* Constructions with xprc **************************************************)

lemma clear_brd_xprc_dx (t1) (t2) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t1,p,b,q,n❩ →
      r● 𝛕𝟎.⓪⋔[p◖𝗦]t2 ⊆ ⓪𝐃❨t2,p,b,q,n❩.
#t1 #t2 #r #p #b #q #n #Hr #s1 #Hs1
lapply ((pt_append_assoc_sn …) … Hs1) -Hs1
>path_clear_empty >(path_clear_d_dx … (⁤↑(♭b+n))) #Hs1
lapply (xprc_des_r … Hr) -Hr >path_clear_reduct #H0 destruct
>path_clear_append in Hs1; * #s2 * #s #Hs #H2 #H1 destruct
>path_clear_append <list_append_assoc <brd_unfold
/4 width=1 by in_comp_term_clear, in_comp_iref_hd, pt_append_in/
qed-.

lemma clear_brd_xprc_sx (t1) (t2) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t1,p,b,q,n❩ →
      ⓪𝐃❨t2,p,b,q,n❩ ⊆ r● 𝛕𝟎.⓪⋔[p◖𝗦]t2.
#t1 #t2 #r #p #b #q #n #Hr #sz * #sd * #si #Hsi #H2 #H1 destruct
elim (in_comp_inv_iref … Hsi) -Hsi #s #H0 #Hs destruct
<path_clear_append <path_clear_d_sn
lapply (xprc_des_r … Hr) -Hr >path_clear_reduct #H0 destruct
/4 width=1 by in_comp_term_clear, in_comp_iref_hd, pt_append_in/
qed-.

lemma clear_brd_xprc (t1) (t2) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t1,p,b,q,n❩ →
      r● 𝛕𝟎.⓪⋔[p◖𝗦]t2 ⇔ ⓪𝐃❨t2,p,b,q,n❩.
/3 width=6 by clear_brd_xprc_sx, clear_brd_xprc_dx, conj/
qed.
