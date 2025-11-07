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

include "ground/xoa/ex_5_4.ma".
include "delayed_updating/syntax/path_beta.ma".
include "delayed_updating/substitution/lift_path.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with path_beta *********************************************)

lemma lift_path_beta (f) (p) (b) (q) (n):
      (𝐫❨🠡[f]p,🠡[🠢[p]f]b,🠡[🠢[𝐫❨p,b❩]f]q,🠢[𝐫❨p,b,q❩]f＠❨n❩❩) = 🠡[f]𝐫❨p,b,q,n❩.
#f #p #b #q #n
<lift_path_d_dx <lift_path_append <lift_path_L_dx <lift_path_append //
qed.

lemma lift_path_p3beta (f) (p) (b) (q):
      (𝐫❨🠡[f]p,🠡[🠢[p]f]b,🠡[🠢[𝐫❨p,b❩]f]q❩) = 🠡[f]𝐫❨p,b,q❩.
#f #p #b #q
<lift_path_append <lift_path_L_dx <lift_path_append //
qed.

(* Inversions with path_beta ************************************************)

lemma eq_inv_lift_path_beta (f) (x) (p2) (b2) (q2) (n2):
      (🠡[f]x) = 𝐫❨p2,b2,q2,n2❩ →
      ∃∃p1,b1,q1,n1. x =  𝐫❨p1,b1,q1,n1❩ &
                     p2 = 🠡[f]p1 & b2 = 🠡[🠢[p1]f]b1 & q2 = 🠡[🠢[𝐫❨p1,b1❩]f]q1 &
                     n2 = 🠢[𝐫❨p1,b1,q1❩]f＠❨n1❩
.
#f #x #p2 #b2 #q2 #n2 #H0
elim (eq_inv_d_dx_lift_path … (sym_eq … H0)) -H0 #x1 #n1 #H0 #Hn0 #H1 destruct
elim (eq_inv_append_lift_path … H0) -H0 #x2 #q1 #H0 #H1 #H2 destruct
elim (eq_inv_L_dx_lift_path … H0) -H0 #x3 #H0 #H1 destruct
elim (eq_inv_append_lift_path … H0) -H0 #x4 #b1 #H0 #H1 #H2 destruct
elim (eq_inv_A_dx_lift_path … H0) -H0 #p1 #H1 #H2 destruct
@(ex5_4_intro … p1 b1 q1 n1) //
qed-.
