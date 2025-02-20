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

include "ground/subsets/subset_and_ol.ma".
include "delayed_updating/reduction/prototerm_xfocus_reducible.ma".
include "delayed_updating/reduction/prototerm_focus.ma".

(* BALANCED REDUCTION FOCUS *************************************************)

(* Constructions with xprc **************************************************)

lemma brf_ol_sn (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → t ≬ 𝐅❨t,p,b,q❩.
#t #r #p #b #q #n #Hr
/3 width=3 by brxf_ol_sn, subset_ol_and_dx_refl_sn/
qed.
