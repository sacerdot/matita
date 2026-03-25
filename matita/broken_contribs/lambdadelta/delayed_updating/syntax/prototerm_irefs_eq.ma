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

include "ground/lib/functions.ma".
include "ground/subsets/subset_eq.ma".
include "ground/subsets/subset_listed_1.ma".
include "ground/subsets/subsets_inhabited.ma".
include "delayed_updating/syntax/prototerm.ma".
include "delayed_updating/syntax/prototerm_irefs.ma".

(* SUBSET OF INNER REFERENCES ***********************************************)

(* Constructions with subset_le *********************************************)

lemma subset_le_pir_bi:
      compatible_2_fwd … (subset_le …) (subset_le …) pir.
#t1 #t2 #Ht #r * #p #q #n #Hr #Hq #Hp destruct
/3 width=4 by pir_mk/
qed.

lemma term_le_pir_grafted_sx (t) (p):
      (𝐈❨⋔[p]t❩) ⊆ ⋔[p]𝐈❨t❩.
#t #p #r * #s1 #s2 #k #H0 #Hs2 #Hs destruct
lapply (term_grafted_inv_gen … Hs) -Hs #Hs
@term_grafted_gen <list_append_lcons_sx
@(pir_mk … Hs2) -Hs2 //
qed.

lemma pir_le_single_append (t) (p):
      t ϵ ⊙ → 𝐈❨❴p❵❩ ⊆ 𝐈❨p●t❩.
#t #p #Ht #r * #s1 #s2 #n #Hs1 #Hs2 * #q1 #q2 #H0 destruct
elim (subsets_inh_inv_in … Ht) -Ht #q #Hq
elim (eq_inv_list_lcons_append ????? (sym_eq … H0)) -H0 *
[ #H1 #H0 destruct
  /3 width=6 by pir_mk, ex2_intro, in_comp_ppc_append_sx/
| -q #q #_ #H0 -q1 -Hs2
  elim (eq_inv_list_empty_append … H0) #_ #H0 -q destruct
]
qed.

(* Constructions with subset_eq *********************************************)

lemma subset_eq_pir_bi:
      compatible_2_fwd … (subset_eq …) (subset_eq …) pir.
#t1 #t2 * #H12 #Ht21
/3 width=3 by conj, subset_le_pir_bi/
qed.
