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

include "static_2/static/feqg_length.ma".

(* GENERIC EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES *********************)

(* Properties with structural successor for closures ************************)

lemma fqu_fneqg (S) (b) (G1) (G2) (L1) (L2) (T1) (T2):
      ❪G1,L1,T1❫ ⬂[b] ❪G2,L2,T2❫ → ❪G1,L1,T1❫ ≛[S] ❪G2,L2,T2❫ → ⊥.
#S #b #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ /3 width=8 by feqg_fwd_length, nsucc_inv_refl/
| /3 width=9 by teqg_inv_pair_xy_x, feqg_fwd_teqg/
| /3 width=9 by teqg_inv_pair_xy_y, feqg_fwd_teqg/
| /3 width=9 by teqg_inv_pair_xy_y, feqg_fwd_teqg/
| /3 width=9 by teqg_inv_pair_xy_y, feqg_fwd_teqg/
| /3 width=8 by feqg_fwd_length, nsucc_inv_refl/
]
qed-.
