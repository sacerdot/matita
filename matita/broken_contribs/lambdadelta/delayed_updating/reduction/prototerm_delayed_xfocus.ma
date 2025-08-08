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

include "delayed_updating/syntax/path_beta_clear.ma".
include "delayed_updating/syntax/prototerm_clear.ma".
include "delayed_updating/reduction/prototerm_xfocus_eq.ma".
include "delayed_updating/reduction/prototerm_delayed.ma".

(* BALANCED REDUCTION DELAYED SUBREDUCT *************************************)

(* Constructions with brxf **************************************************)

lemma brd_le_brxf (t) (p) (b) (q) (n):
      (⓪𝐃❨t,p,b,q,n❩) ⊆ ⓪𝐅❨p,b,q,n❩.
#t #p #b #q #n #rz * #r <brd_unfold <brxf_unfold #Hr #H0 destruct
elim Hr -Hr #s #Hs #H0 destruct
<path_clear_append <(path_clear_beta_b … (⁤↑n) (⁤↑(♭b+n))) >path_clear_append
/2 width=1 by in_comp_term_clear/
qed.

lemma brd_brxf_append_p (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      (𝐅❨𝐫❨p2,⓪b2,q2,⁤↑(♭b2+n2)❩●p1,b1,q1,n1❩) ⇔
      (𝐃❨𝐅❨p2◖𝗦●p1,b1,q1,n1❩,p2,b2,q2,n2❩).
#p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2
@(subset_eq_canc_sn … (brxf_append_p …))
@pt_append_eq_repl_bi [ // ]
@(subset_eq_canc_sn … (grafted_brxf_append_p …)) //
qed.

lemma brd_brxf_append_q (p1) (b1) (b2) (q11) (q12) (q2) (n1) (n2):
      (𝐅❨p1,b1,𝐫❨q11,⓪b2,q2,⁤↑(♭b2+n2)❩●q12,n1❩) ⇔
      (𝐃❨𝐅❨p1,b1,q11◖𝗦●q12,n1❩,𝐫❨p1,b1,q11❩,b2,q2,n2❩).
#p1 #b1 #b2 #q11 #q12 #q2 #n1 #n2
@(subset_eq_canc_sn … (brxf_append_q …)) >path_beta_swap_pq
@pt_append_eq_repl_bi [ // ]
@(subset_eq_trans … (grafted_brxf_append_q …))
[4: @term_grafted_eq_repl_bi [| @subset_eq_refl ] |1,2,3: skip ] //
qed.
