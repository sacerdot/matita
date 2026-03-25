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
include "delayed_updating/reduction/prototerm_x_focus.ma".

(* BALANCED REDUCTION EXTENDED FOCUS ****************************************)

(* Constructions with term_eq ***********************************************)

lemma brxf_append_p (p2) (p1) (b) (q) (n):
      p2●𝐅❨p1,b,q,n❩ ⇔ 𝐅❨p2●p1,b,q,n❩.
#p2 #p1 #b #q #n
<brxf_unfold <brxf_unfold <path_beta_append_p //
qed.

lemma brxf_append_q (p) (b) (q1) (q2) (n):
      (𝐫❨p,b,q1❩)●↑𝐫❨q2,⁤↑n❩ ⇔ 𝐅❨p,b,q1●q2,n❩.
#p #b #q1 #q2 #n
<brxf_unfold <path_beta_append_q
@(subset_eq_trans … (term_slice_append …))
@subset_eq_refl
qed.

lemma grafted_brxf_append_p (p2) (p1) (b1) (q1) (n1):
      (𝐅❨p1,b1,q1,n1❩)⇔⋔[p2]𝐅❨p2●p1,b1,q1,n1❩.
#p2 #p1 #b1 #q1 #n1
@(subset_eq_trans … (term_grafted_eq_repl …))
[| @brxf_append_p | skip ]
@term_grafted_pt_append
qed.

lemma grafted_brxf_append_q (p) (b) (q1) (q2) (n):
      ↑𝐫❨q2,⁤↑n❩ ⇔ ⋔[𝐫❨p,b,q1❩]𝐅❨p,b,q1●q2,n❩.
#p #b #q1 #q2 #n
@(subset_eq_trans … (term_grafted_eq_repl …))
[| @brxf_append_q | skip ]
@term_grafted_pt_append
qed.

lemma grafted_brxf_full (p) (b) (q) (n):
      ↑𝐞 ⇔ ⋔[𝐫❨p,b,q,⁤↑n❩]𝐅❨p,b,q,n❩.
#p #b #q #n <brxf_unfold
@(subset_eq_trans … (term_grafted_pt_append …))
[2: @term_grafted_eq_repl | skip ]
@(subset_eq_trans … (term_slice_append …)) //
qed.
