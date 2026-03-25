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
(*
include "delayed_updating/syntax/prototerm_clear_eq.ma".
*)
include "delayed_updating/reduction/prototerm_cx_redex.ma".
include "delayed_updating/reduction/prototerm_delayed_x_redex.ma".

(* BALANCED REDUCTION DELAYED SUBREDUCT *************************************)
(*
(* Constructions with pcxr **************************************************)

lemma clear_brd_pcxr (t1) (t2) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t1,p,b,q,n❩ →
      r●⓪⋔[p◖𝗦]t2 ⇔ ⓪𝐃❨t2,p,b,q,n❩.
#t1 #t2 #r #p #b #q #n #Hr
lapply (pcxr_des_r … Hr) -Hr >(path_clear_beta_b ???? (⁤↑(♭b+n))) #H0 destruct
@(subset_eq_trans … (clear_pt_append …))
@clear_eq_repl @subset_eq_refl (* ** auto too slow *)
qed.
*)

(* Destructions with pcxr ***************************************************)

lemma term_in_root_brd_des_pcxr (t2) (t1) (s) (r) (p) (b) (q) (n):
      s ϵ ▵𝐃❨t2,p,b,q,n❩ → r ϵ 𝐑❨t1,p,b,q,n❩ → ⓪s ≚ ⓪r.
/3 width=8 by pcxr_des_x, term_in_root_brd_des_pxr/
qed-.
