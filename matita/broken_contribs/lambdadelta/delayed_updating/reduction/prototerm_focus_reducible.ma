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

include "ground/subsets/subset_ol.ma".
include "delayed_updating/reduction/prototerm_reducible.ma".
include "delayed_updating/reduction/prototerm_focus.ma".

(* BALANCED REDUCTION FOCUS *************************************************)

(* Constructions with xprc **************************************************)

lemma brf_ol_sn (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → t ≬ 𝐅❨p,b,q❩.
#t #r #p #b #q #n #Hr
lapply (xprc_des_n … Hr) -Hr #Hn
<brf_unfold
/2 width=3 by subset_ol_i/
qed.
