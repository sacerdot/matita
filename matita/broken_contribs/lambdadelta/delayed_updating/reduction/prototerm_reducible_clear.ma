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

include "delayed_updating/syntax/prototerm_clear.ma".
include "delayed_updating/reduction/prototerm_reducible.ma".

(* EXPLICIT REDEX POINTER ***************************************************)

(* Destructions with term_clear *********************************************)

lemma xprc_des_r_clear (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → r◖𝗱𝟎 ϵ ⓪t.
#t #r #p #b #q #n #Hr
lapply (xprc_des_n … Hr) #Hn
lapply (xprc_des_r … Hr) -Hr #H0 destruct
>(path_clear_d_dx … (⁤↑n))
/2 width=1 by in_comp_term_clear/
qed-.
