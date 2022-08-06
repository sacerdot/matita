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

include "delayed_updating/unwind/unwind2_prototerm_eq.ma".
include "delayed_updating/unwind/unwind2_path_append.ma".
include "delayed_updating/syntax/prototerm_constructors.ma".

(* TAILED UNWIND FOR PROTOTERM **********************************************)

(* Constructions with constructors ******************************************)

lemma unwind2_term_iref_sn (f) (t) (k:pnat):
      ▼[f∘𝐮❨k❩]t ⊆ ▼[f](𝛕k.t).
#f #t #k #p * #q #Hq #H0 destruct
@(ex2_intro … (𝗱k◗𝗺◗q))
/2 width=1 by in_comp_iref/
qed-.

lemma unwind2_term_iref_dx (f) (t) (k:pnat):
      ▼[f](𝛕k.t) ⊆ ▼[f∘𝐮❨k❩]t.
#f #t #k #p * #q #Hq #H0 destruct
elim (in_comp_inv_iref … Hq) -Hq #p #Hp #Ht destruct
/2 width=1 by in_comp_unwind2_path_term/
qed-.

lemma unwind2_term_iref (f) (t) (k:pnat):
      ▼[f∘𝐮❨k❩]t ⇔ ▼[f](𝛕k.t).
/3 width=2 by conj, unwind2_term_iref_sn, unwind2_term_iref_dx/
qed.
