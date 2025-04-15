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

include "delayed_updating/syntax/prototerm_clear_ol_eq.ma".
include "delayed_updating/reduction/prototerm_reducible.ma".

(* EXPLICIT REDEX POINTER ***************************************************)

(* Constructions with term_clear ********************************************)

lemma term_in_comp_clear_root_slice_dec_xprc (t) (r) (p1) (p2) (b) (q) (n):
      r ϵ 𝐑❨t,p1,b,q,n❩ →
      Decidable (r ϵ ⓪▵↑p2).
#t #r #p1 #p2 #b #q #n #Hr
<(xprc_des_clear … Hr) -Hr
@term_in_comp_clear_bi_root_slice_dec
qed-.

(* Destructions with term_clear *********************************************)

lemma xprc_des_r_clear (t) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → r◖𝗱𝟎 ϵ ⓪t.
#t #r #p #b #q #n #Hr
lapply (xprc_des_n … Hr) #Hn
lapply (xprc_des_r … Hr) -Hr #H0 destruct
>(path_clear_d_dx … (⁤↑n))
/2 width=1 by in_comp_term_clear/
qed-.
