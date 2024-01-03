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

include "ground/relocation/fb/fbr_xapp.ma".
include "ground/relocation/fb/fbr_lapp.ma".
include "ground/arith/nat_pred.ma".

(* EXTENDED DEPTH APPLICATION FOR FINITE RELOCATION MAPS WITH BOOLEANS ******)

(* Constructions with fbr_lapp **********************************************)

lemma fbr_lapp_xapp (f) (n):
      (⫰(f＠❨⁤↑n❩)) = f＠§❨n❩.
// qed.

lemma fbr_xapp_succ_lapp (f) (n):
      (⁤↑(f＠§❨n❩)) = f＠❨⁤↑n❩.
// qed.

(* Inversions with fbr_lapp *************************************************)

lemma eq_inv_succ_fbr_xapp (f) (n) (m):
      (⁤↑n) = f＠❨m❩ →
      ∧∧ n = f＠§❨⫰m❩ & m ϵ 𝐏.
#f #n #m #H1m
lapply (eq_des_succ_fbr_xapp … H1m) #H2m
generalize in match H1m; -H1m
>H2m in ⊢ (%→?); <fbr_xapp_succ_lapp #H0
lapply (eq_inv_nsucc_bi … H0) -H0 #H1m
/2 width=1 by conj/
qed-.
