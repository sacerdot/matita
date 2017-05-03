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

include "basic_2/static/lfxs_fqup.ma".
include "basic_2/i_static/tc_lfxs.ma".

(* ITERATED EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ***)

(* Advanced properties ******************************************************)

lemma tc_lfxs_refl: ∀R. (∀L. reflexive … (R L)) → ∀T. reflexive … (tc_lfxs R T).
/3 width=1 by lfxs_refl, inj/ qed.

(* Basic_2A1: uses: TC_lpx_sn_pair TC_lpx_sn_pair_refl *)
lemma tc_lfxs_pair: ∀R. (∀L. reflexive … (R L)) →
                    ∀L,V1,V2. LTC … R L V1 V2 → ∀I,T. L.ⓑ{I}V1 ⪤**[R, T] L.ⓑ{I}V2.
#R #HR #L #V1 #V2 #H elim H -V2
/3 width=3 by tc_lfxs_step_dx, lfxs_pair, inj/
qed.

(* Advanced eliminators *****************************************************)

lemma tc_lfxs_ind_sn: ∀R. (∀L. reflexive … (R L)) →
                      ∀L1,T. ∀R0:predicate …. R0 L1 →
                      (∀L,L2. L1 ⪤**[R, T] L → L ⪤*[R, T] L2 → R0 L → R0 L2) →
                      ∀L2. L1 ⪤**[R, T] L2 → R0 L2.
#R #HR #L1 #T #R0 #HL1 #IHL1 #L2 #HL12
@(TC_star_ind … HL1 IHL1 … HL12) /2 width=1 by lfxs_refl/
qed-.

lemma tc_lfxs_ind_dx: ∀R. (∀L. reflexive … (R L)) →
                      ∀L2,T. ∀R0:predicate …. R0 L2 →
                      (∀L1,L. L1 ⪤*[R, T] L → L ⪤**[R, T] L2 → R0 L → R0 L1) →
                      ∀L1. L1 ⪤**[R, T] L2 → R0 L1.
#R #HR #L2 #R0 #HL2 #IHL2 #L1 #HL12
@(TC_star_ind_dx … HL2 IHL2 … HL12) /2 width=4 by lfxs_refl/
qed-.
