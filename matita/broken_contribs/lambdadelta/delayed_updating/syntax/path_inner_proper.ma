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

include "delayed_updating/syntax/path_inner.ma".
include "delayed_updating/syntax/path_proper.ma".

(* INNER CONDITION FOR PATH *************************************************)

(* Constructions with proper condition for path *****************************)

lemma pic_ppc_append_sx (p) (q):
      q ϵ 𝐈 → q ϵ 𝐏 → p●q ϵ 𝐈.
#p #q * // #H0
elim (ppc_inv_empty … H0)
qed.

(* Destructions with proper condition for path ******************************)

lemma path_des_outer_proper (p):
      p ⧸ϵ 𝐈 → p ϵ 𝐏.
#p #H1 #H2 destruct
@H1 -H1 // (**) (* auto fails *)
qed-.
