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

include "ground/subsets/subset_le.ma".
include "delayed_updating/syntax/path_clear_help.ma".
include "delayed_updating/syntax/prototerm_clear.ma".
include "delayed_updating/reduction/prototerm_xfocus.ma".
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
