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

include "delayed_updating/substitution/lift_eq.ma".
include "delayed_updating/syntax/path_proper.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with proper condition for path *****************************)

lemma lift_path_proper (f) (p):
      p ϵ 𝐏 → ↑[f]p ϵ 𝐏.
#f *
[ #H0 elim (ppc_inv_empty … H0)
| * [ #n ] #p #_
  [ <lift_path_d_sn /2 width=3 by ppc_lcons/
  | <lift_path_m_sn /2 width=3 by ppc_lcons/
  | <lift_path_L_sn /2 width=3 by ppc_lcons/
  | <lift_path_A_sn /2 width=3 by ppc_lcons/
  | <lift_path_S_sn /2 width=3 by ppc_lcons/
  ]
]
qed.

(* Inversions with proper condition for path ********************************)

lemma lift_path_inv_proper (f) (p):
      ↑[f]p ϵ 𝐏 → p ϵ 𝐏.
#f * //
#H0 elim (ppc_inv_empty … H0)
qed-.
