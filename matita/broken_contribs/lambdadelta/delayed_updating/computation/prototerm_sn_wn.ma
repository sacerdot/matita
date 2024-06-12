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

include "delayed_updating/computation/prototerm_wn.ma".
include "delayed_updating/computation/prototerm_sn.ma".

(* STRONG NORMALIZATION FOR PROTOTERM ***************************************)

(* Destructions with twn ****************************************************)

(* Note: this holds if we can decide whether 𝐑❨t❩ is empty *)
lemma tsn_des_twn (t):
      t ϵ 𝐒𝐍 → t ϵ 𝐖𝐍.
#t #Ht elim Ht -t
#t1 #Ht1 #IH @IH
