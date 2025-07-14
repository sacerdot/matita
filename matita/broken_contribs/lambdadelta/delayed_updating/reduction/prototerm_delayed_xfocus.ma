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
include "delayed_updating/syntax/prototerm_clear.ma".
include "delayed_updating/reduction/prototerm_xfocus_eq.ma".
include "delayed_updating/reduction/prototerm_delayed.ma".

(* BALANCED REDUCTION DELAYED SUBREDUCT *************************************)

(* Constructions with brxf **************************************************)

lemma brd_le_brxf (t) (p) (b) (q) (n):
      (⓪𝐃❨t,p,b,q,n❩) ⊆ ⓪𝐅❨p,b,q❩.
#t #p #b #q #n #rz * #r <brd_unfold <brxf_unfold #Hr #H0 destruct
elim Hr -Hr #s #Hs #H0 destruct
<path_clear_append <path_clear_reduct >path_clear_append
/2 width=1 by in_comp_term_clear/
qed.

lemma brd_brxf_append_p (p1) (p2) (b1) (b2) (q1) (q2) (n2):
      (𝐅❨(p2●𝗔◗⓪b2●𝗟◗q2◖𝗱⁤↑(♭b2+n2))●p1,b1,q1❩) ⇔ 𝐃❨𝐅❨p2●𝗦◗p1,b1,q1❩,p2,b2,q2,n2❩.
#p1 #p2 #b1 #b2 #q1 #q2 #n2
<brxf_unfold >(list_append_rcons_sn … p1) <list_append_assoc
@(subset_eq_canc_sn … (term_slice_append …))
@pt_append_eq_repl_bi [ // ]
<list_append_assoc
@(subset_eq_canc_sn … (term_slice_append …))
@pt_append_eq_repl_bi [ // ]
/2 width=1 by grafted_brxf_append_p/
qed.

lemma brd_brxf_append_q (p1) (b1) (b2) (q11) (q12) (q2) (n2):
      (𝐅❨p1,b1,q11●𝗔◗⓪b2●𝗟◗q2●𝗱⁤↑(♭b2+n2)◗q12❩) ⇔ 𝐃❨𝐅❨p1,b1,q11●𝗦◗q12❩,p1●𝗔◗b1●𝗟◗q11,b2,q2,n2❩.
#p1 #b1 #b2 #q11 #q12 #q2 #n2
<brxf_unfold <path_append_pAbLqAbLq_4
@(subset_eq_canc_sn … (term_slice_append …))
@pt_append_eq_repl_bi [ // ]
@(subset_eq_canc_sn … (term_slice_append …))
@pt_append_eq_repl_bi [ // ]
/2 width=1 by grafted_brxf_append_q/
qed.
