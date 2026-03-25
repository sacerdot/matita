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

include "delayed_updating/syntax/path_root_eq_clear.ma".
include "delayed_updating/syntax/path_beta_clear.ma".
include "delayed_updating/reduction/prototerm_x_redex.ma".
include "delayed_updating/reduction/prototerm_delayed_eq.ma".

(* BALANCED REDUCTION DELAYED SUBREDUCT *************************************)

(* Destructions with pcr ****************************************************)

lemma term_in_root_brd_des_pxr (t) (s) (r) (p) (b) (q) (n):
      s ϵ ▵𝐃❨t,p,b,q,n❩ → r ϵ 𝐑❨p,b,q,n❩ → ⓪s ≚ ⓪r.
#t #s #r #p #b #q #n #Hs #Hr
lapply (pxr_des_eq … Hr) -Hr #H0 destruct
>(path_clear_beta_b ???? (⁤↑(♭b+n)))
lapply (term_le_root_bi_brd_slice … Hs) -Hs #Hs
lapply (path_req_mk_in_root_slice … Hs) -Hs #Hs
/3 width=1 by path_req_clear_bi, path_req_sym/
qed-.
