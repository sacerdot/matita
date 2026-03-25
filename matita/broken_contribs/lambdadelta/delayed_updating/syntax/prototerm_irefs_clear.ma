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

include "ground/subsets/subset_eq.ma".
include "delayed_updating/syntax/path_clear_proper.ma".
include "delayed_updating/syntax/prototerm_clear.ma".
include "delayed_updating/syntax/prototerm_irefs.ma".

(* SUBSET OF INNER REFERENCES ***********************************************)

(* Constructions with prototerm_clear and subset_le *************************)

lemma pir_clear_ge (t):
      (⓪𝐈❨t❩) ⊆ 𝐈❨⓪t❩.
#t #x0 * #x * #p #q #n #H1 #Hq #Hp #H2 destruct
<path_clear_d_dx
/3 width=4 by pir_mk, path_clear_ppc, in_comp_term_clear/
qed.

lemma pir_clear_le (t):
      (𝐈❨⓪t❩) ⊆ ⓪𝐈❨t❩.
#t #x * #p #q #n #H1 #Hq * #y0 #Hy0 #H2 destruct
elim (eq_inv_path_append_clear … H2) -H2 #p0 #x0 #H0 #H1 #H2 destruct
elim (eq_inv_path_d_dx_clear … H0) -H0 #q0 #n0 #H1 #H2 #H3 destruct
>(path_clear_d_dx … n0)
/4 width=3 by pir_mk, path_clear_inv_ppc, in_comp_term_clear/
qed.

(* Constructions with prototerm_clear and subset_le *************************)

lemma pir_clear (t):
      (⓪𝐈❨t❩) ⇔ 𝐈❨⓪t❩.
/3 width=1 by conj, pir_clear_ge, pir_clear_le/
qed.
