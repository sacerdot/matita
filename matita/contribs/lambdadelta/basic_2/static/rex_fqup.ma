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
include "basic_2/static/rex.ma".

(* GENERIC EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ****)

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: llpx_sn_refl *)
lemma rex_refl: ∀R. (∀L. reflexive … (R L)) → ∀L,T. L ⪤[R, T] L.
#R #HR #L #T elim (frees_total L T)
/4 width=3 by sex_refl, ext2_refl, ex2_intro/
qed.

lemma rex_pair_refl: ∀R. (∀L. reflexive … (R L)) →
                     ∀L,V1,V2. R L V1 V2 → ∀I,T. L.ⓑ{I}V1 ⪤[R, T] L.ⓑ{I}V2.
#R #HR #L #V1 #V2 #HV12 #I #T
elim (frees_total (L.ⓑ{I}V1) T) #f #Hf
elim (pn_split f) * #g #H destruct
/5 width=3 by sex_refl, sex_next, sex_push, ext2_refl, ext2_pair, ex2_intro/
qed.

(* Advanced inversion lemmas ************************************************)

lemma rex_inv_bind_void: ∀R,p,I,L1,L2,V,T. L1 ⪤[R, ⓑ{p,I}V.T] L2 →
                         L1 ⪤[R, V] L2 ∧ L1.ⓧ ⪤[R, T] L2.ⓧ.
#R #p #I #L1 #L2 #V #T * #f #Hf #HL elim (frees_inv_bind_void … Hf) -Hf
/6 width=6 by sle_sex_trans, sex_inv_tl, sor_inv_sle_dx, sor_inv_sle_sn, ex2_intro, conj/
qed-.

(* Advanced forward lemmas **************************************************)

lemma rex_fwd_bind_dx_void: ∀R,p,I,L1,L2,V,T. L1 ⪤[R, ⓑ{p,I}V.T] L2 →
                            L1.ⓧ ⪤[R, T] L2.ⓧ.
#R #p #I #L1 #L2 #V #T #H elim (rex_inv_bind_void … H) -H //
qed-.
