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

include "delayed_updating/syntax/path_proper.ma".
include "delayed_updating/syntax/path_clear.ma".

(* CLEAR FOR PATH ***********************************************************)

(* Constructions with ppc ***************************************************)

lemma path_clear_ppc (p):
      p ϵ 𝐏 → ⓪p ϵ 𝐏 .
#p #Hp #H0
lapply (eq_inv_path_empty_clear … H0) -H0 #H0 destruct
/2 width=1 by ppc_inv_empty/
qed.

(* Inversions with ppc ******************************************************)

lemma path_clear_inv_ppc (p):
      ⓪p ϵ 𝐏 → p ϵ 𝐏 .
#p #Hp #H0 destruct
<path_clear_empty in Hp;
/2 width=1 by ppc_inv_empty/
qed-.
