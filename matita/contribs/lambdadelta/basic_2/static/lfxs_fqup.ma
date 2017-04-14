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

include "basic_2/static/frees_fqup.ma".
include "basic_2/static/lfxs.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: llpx_sn_refl *)
lemma lfxs_refl: ∀R. (∀L. reflexive … (R L)) → ∀L,T. L ⦻*[R, T] L.
#R #HR #L #T elim (frees_total L T) /3 width=3 by lexs_refl, ex2_intro/
qed.

lemma lfxs_pair: ∀R. (∀L. reflexive … (R L)) →
                 ∀L,V1,V2. R L V1 V2 → ∀I,T. L.ⓑ{I}V1 ⦻*[R, T] L.ⓑ{I}V2.
#R #HR #L #V1 #V2 #HV12 #I #T
elim (frees_total (L.ⓑ{I}V1) T) #f #Hf
elim (pn_split f) * #g #H destruct
/4 width=3 by lexs_refl, lexs_next, lexs_push, ex2_intro/
qed.
