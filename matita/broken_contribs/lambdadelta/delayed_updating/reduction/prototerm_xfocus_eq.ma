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

include "delayed_updating/syntax/path_help.ma".
include "delayed_updating/syntax/prototerm_eq.ma".
include "delayed_updating/reduction/prototerm_xfocus.ma".

(* BALANCED REDUCTION EXTENDED FOCUS ****************************************)

(* Constructions with term_eq ***********************************************)

lemma brxf_append_p (p2) (p1) (b1) (q1):
      p2●𝐅❨p1,b1,q1❩ ⇔ 𝐅❨p2●p1,b1,q1❩.
#p2 #p1 #b1 #q1 //
qed.

lemma grafted_brxf_append_p (p2) (p1) (b1) (q1):
     (𝐅❨p1,b1,q1❩)⇔⋔[p2]𝐅❨p2●p1,b1,q1❩.
#p2 #p1 #b1 #q1
@(subset_eq_trans … (term_grafted_pt_append … p2))
@term_grafted_eq_repl
@brxf_append_p
qed.

lemma grafted_brxf_append_q (p) (b) (q1) (q2):
      ↑q2 ⇔ ⋔[p●𝗔◗b●𝗟◗q1]𝐅❨p,b,q1●q2❩.
#p #b #q1 #q2
<brxf_unfold <path_append_pAbLq_11
@(subset_eq_trans … (term_grafted_pt_append … (p●𝗔◗b●𝗟◗q1)))
/2 width=1 by term_grafted_eq_repl/
qed.
