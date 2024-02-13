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

include "delayed_updating/syntax/path_clear_structure.ma".
include "delayed_updating/syntax/prototerm_structure.ma".
include "delayed_updating/syntax/prototerm_clear.ma".
include "delayed_updating/syntax/preterm_structure.ma".

(* PRETERM ******************************************************************)

(* Destructions with path_clear *********************************************)

lemma term_slice_des_clear_bi (t) (p) (q1) (q2):
      t ϵ 𝐓 → p●q1 ϵ ▵t → p●q2 ϵ ▵t → ⓪q1 ϵ ↑⓪q2 → q1 ϵ ↑q2.
#t #p #q1 #q2 #Ht #Hq1 #Hq2 #Hq
lapply (term_slice_structure … Hq)
<path_structure_clear <path_structure_clear #H0
elim (term_slice_des_structure_bi … Ht Hq1 Hq2 H0) -t -p -H0 //
* #r #_ #H0 destruct
<(term_slice_antisym_clear … Hq) -Hq //
qed-.

(* Inversions with path_clear ***********************************************)

lemma term_clear_inj (t) (q1) (q2):
      t ϵ 𝐓 → q1 ϵ ▵t → q2 ϵ ▵t → ⓪q1 = ⓪q2 → q1 = q2.
#t #q1 #q2 #Ht #Hq1 #Hq2 #Hq
lapply (term_slice_des_clear_bi … (𝐞) q1 q2 Ht ???) // #H1
lapply (term_slice_des_clear_bi … (𝐞) q2 q1 Ht ???) // #H2
/2 width=1 by term_slice_antisym/
qed-.

(* Constructions with term_clear ********************************************)
(*
lemma preterm_clear (t):
      t ϵ 𝐓 → ⓪t ϵ 𝐓.
#t * #H1 #H2 #H3 #H4
@mk_preterm_posts
[ #p1 #p2 * #r1 #Hr1 #H1 * #r2 #Hr2 #H2 * #q2 #_ #H0 destruct
*)
