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

include "ground/subsets/subset_le.ma".
include "delayed_updating/syntax/path_clear_proper.ma".
include "delayed_updating/syntax/prototerm_clear.ma".
include "delayed_updating/syntax/prototerm_irefs.ma".

(* SUBSET OF INNER REFERENCES ***********************************************)

(* Constructions with subset_le and prototerm_clear *************************)

lemma term_le_pirc_bi_clear_dx (t):
      (𝐈❨t❩) ⊆ 𝐈❨⓪t❩.
#t #r * #p #q #n #H0 #Hq #Hp destruct
>path_clear_idem
/3 width=4 by path_in_pirc, in_comp_term_clear, path_clear_ppc/
qed.

lemma term_le_pirc_bi_clear_sx (t):
      (𝐈❨⓪t❩) ⊆ 𝐈❨t❩.
#t #r * #p #q #n #H1 #Hq * #s #Hs #H2 destruct
elim (eq_inv_path_append_clear … H2) -H2 #p0 #x0 #H0 #H1 #H2 destruct
elim (eq_inv_path_d_dx_clear … H0) -H0 #q0 #n0 #H1 #H2 #H3 destruct
<path_clear_idem
/3 width=4 by path_in_pirc, path_clear_inv_ppc/
qed.
