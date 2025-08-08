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

include "delayed_updating/syntax/prototerm_clear_eq.ma".
include "delayed_updating/reduction/prototerm_reducible.ma".
include "delayed_updating/reduction/prototerm_delayed_eq.ma".

(* BALANCED REDUCTION DELAYED SUBREDUCT *************************************)

(* Constructions with xprc **************************************************)

lemma clear_brd_xprc (t1) (t2) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t1,p,b,q,n❩ →
      r●⓪⋔[p◖𝗦]t2 ⇔ ⓪𝐃❨t2,p,b,q,n❩.
#t1 #t2 #r #p #b #q #n #Hr
lapply (xprc_des_r … Hr) -Hr >(path_clear_beta_b ???? (⁤↑(♭b+n))) #H0 destruct
@(subset_eq_trans … (clear_pt_append …))
@clear_eq_repl @subset_eq_refl (* ** auto too slow *)
qed.

(* Destructions with xprc ***************************************************)

lemma term_in_root_brd_des_xprc (t) (r) (s) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ →
      s ϵ ▵𝐃❨t,p,b,q,n❩ → r ϵ ⓪▵↑s.
#t #r #s #p #b #q #n #Hr #Hs
lapply (xprc_des_r … Hr) -Hr #Hr destruct
>(path_clear_beta_b ???? (⁤↑(♭b+n)))
/4 width=3 by term_le_root_bi_brd_slice, term_in_root_slice_sym, in_comp_term_clear/
qed-.
