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

include "basic_2/notation/relations/pconvstar_7.ma".
include "basic_2/rt_computation/cpms.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-EQUIVALENCE FOR TERMS **************)

(* Basic_2A1: uses: scpes *)
definition cpes (h) (n1) (n2): relation4 genv lenv term term ≝
           λG,L,T1,T2.
           ∃∃T. ❨G,L❩ ⊢ T1 ➡*[h,n1] T & ❨G,L❩ ⊢ T2 ➡*[h,n2] T.

interpretation "t-bound context-sensitive parallel rt-equivalence (term)"
   'PConvStar h n1 n2 G L T1 T2 = (cpes h n1 n2 G L T1 T2).

(* Basic properties *********************************************************)

(* Basic_2A1: uses: scpds_div *)
lemma cpms_div (h) (n1) (n2):
      ∀G,L,T1,T. ❨G,L❩ ⊢ T1 ➡*[h,n1] T →
      ∀T2. ❨G,L❩ ⊢ T2 ➡*[h,n2] T → ❨G,L❩ ⊢ T1 ⬌*[h,n1,n2] T2.
/2 width=3 by ex2_intro/ qed.

lemma cpes_refl (h): ∀G,L. reflexive … (cpes h 0 0 G L).
/2 width=3 by cpms_div/ qed.

(* Basic_2A1: uses: scpes_sym *)
lemma cpes_sym (h) (n1) (n2):
      ∀G,L,T1,T2. ❨G,L❩ ⊢ T1 ⬌*[h,n1,n2] T2 → ❨G,L❩ ⊢ T2 ⬌*[h,n2,n1] T1.
#h #n1 #n2 #G #L #T1 #T2 * /2 width=3 by cpms_div/
qed-.
