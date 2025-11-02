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
include "delayed_updating/unwind/unwind2_path.ma".

(* TAILED UNWIND FOR PATH ***************************************************)

(* Constructions with path_beta *********************************************)

lemma unwind2_path_beta (f) (p) (b) (q) (n):
      (𝐫❨⊗p,⊗b,⊗q,(▶[𝐫❨p,b,q❩]f)＠❨n❩❩) = ▼[f]𝐫❨p,b,q,n❩.
#f #p #b #q #n
<unwind2_path_d_dx <structure_append
<structure_L_dx <structure_append //
qed.

(* Inversions with path_beta ************************************************)

lemma eq_inv_unwind2_path_beta (f) (x) (p2) (b2) (q2) (n2):
      ▼[f]x = 𝐫❨p2,b2,q2,n2❩ →
      ∃∃p1,b1,q1,n1. x =  𝐫❨p1,b1,q1,n1❩ & 
                     p2 = ⊗p1 & b2 = ⊗b1 & q2 = ⊗q1 &
                     n2 = (▶[𝐫❨p1,b1,q1❩]f)＠❨n1❩
.
#f #x #p2 #b2 #q2 #n2 #H0
elim (eq_inv_d_dx_unwind2_path … (sym_eq … H0)) -H0 #x1 #n1 #H0 #Hn0 #H1 destruct
elim (eq_inv_append_structure … H0) -H0 #x2 #qb #H0 #H1 #H2 destruct
elim (eq_inv_L_dx_structure … H0) -H0 #x3 #qa #H0 #Hq #H1 destruct
elim (eq_inv_append_structure … H0) -H0 #x4 #bb #H0 #H1 #H2 destruct
elim (eq_inv_A_dx_structure … H0) -H0 #p1 #ba #H1 #Hb #H2 destruct
@(ex5_4_intro … p1 (ba●bb) (qa●qb) n1)
[ <path_beta_unfold_sx <list_append_rcons_sx <list_append_rcons_sx //
| //
| <structure_append //
| <structure_append <Hq -qa //
| <path_pbeta_unfold_sx <list_append_rcons_sx <list_append_rcons_sx //
]
qed-.
