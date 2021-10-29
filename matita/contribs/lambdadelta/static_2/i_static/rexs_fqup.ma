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

include "static_2/static/rex_fqup.ma".
include "static_2/i_static/rexs.ma".

(* ITERATED EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ***)

(* Advanced properties ******************************************************)

lemma rexs_refl: ∀R. c_reflexive … R →
                 ∀T. reflexive … (rexs R T).
/3 width=1 by rex_refl, inj/ qed.

(* Basic_2A1: uses: TC_lpx_sn_pair TC_lpx_sn_pair_refl *)
lemma rexs_pair_refl: ∀R. c_reflexive … R →
                      ∀L,V1,V2. CTC … R L V1 V2 → ∀I,T. L.ⓑ[I]V1 ⪤*[R,T] L.ⓑ[I]V2.
#R #HR #L #V1 #V2 #H elim H -V2
/3 width=3 by rexs_step_dx, rex_pair_refl, inj/
qed.

lemma rexs_tc: ∀R,L1,L2,T,f. 𝐈❨f❩ → TC … (sex cfull (cext2 R) f) L1 L2 →
               L1 ⪤*[R,T] L2.
#R #L1 #L2 #T #f #Hf #H elim H -L2
[ elim (frees_total L1 T) | #L elim (frees_total L T) ]
/5 width=7 by sex_sdj, rexs_step_dx, pr_sdj_isi_sn, inj, ex2_intro/
qed.

(* Advanced eliminators *****************************************************)

lemma rexs_ind_sn: ∀R. c_reflexive … R →
                   ∀L1,T. ∀Q:predicate …. Q L1 →
                   (∀L,L2. L1 ⪤*[R,T] L → L ⪤[R,T] L2 → Q L → Q L2) →
                   ∀L2. L1 ⪤*[R,T] L2 → Q L2.
#R #HR #L1 #T #Q #HL1 #IHL1 #L2 #HL12
@(TC_star_ind … HL1 IHL1 … HL12) /2 width=1 by rex_refl/
qed-.

lemma rexs_ind_dx: ∀R. c_reflexive … R →
                   ∀L2,T. ∀Q:predicate …. Q L2 →
                   (∀L1,L. L1 ⪤[R,T] L → L ⪤*[R,T] L2 → Q L → Q L1) →
                   ∀L1. L1 ⪤*[R,T] L2 → Q L1.
#R #HR #L2 #Q #HL2 #IHL2 #L1 #HL12
@(TC_star_ind_dx … HL2 IHL2 … HL12) /2 width=4 by rex_refl/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma rexs_inv_bind_void: ∀R. c_reflexive … R →
                          ∀p,I,L1,L2,V,T. L1 ⪤*[R,ⓑ[p,I]V.T] L2 →
                          ∧∧ L1 ⪤*[R,V] L2 & L1.ⓧ ⪤*[R,T] L2.ⓧ.
#R #HR #p #I #L1 #L2 #V #T #H @(rexs_ind_sn … HR … H) -L2
[ /3 width=1 by rexs_refl, conj/
| #L #L2 #_ #H * elim (rex_inv_bind_void … H) -H /3 width=3 by rexs_step_dx, conj/
]
qed-.

(* Advanced forward lemmas **************************************************)

lemma rexs_fwd_bind_dx_void: ∀R. c_reflexive … R →
                             ∀p,I,L1,L2,V,T. L1 ⪤*[R,ⓑ[p,I]V.T] L2 →
                             L1.ⓧ ⪤*[R,T] L2.ⓧ.
#R #HR #p #I #L1 #L2 #V #T #H elim (rexs_inv_bind_void … H) -H //
qed-.
