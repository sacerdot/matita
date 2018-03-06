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

include "basic_2/static/lfxs_length.ma".
include "basic_2/static/lfxs_fsle.ma".
include "basic_2/static/lfeq.ma".

(* SYNTACTIC EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES *********)

(* Properties with free variables inclusion for restricted closures *********)

lemma lfeq_fsle_comp: lfxs_fsle_compatible ceq.
#L1 #L2 #T #HL12
elim (frees_total L1 T)
/4 width=8 by frees_lfeq_conf, lfxs_fwd_length, lveq_length_eq, sle_refl, ex4_4_intro/
qed.

(* Forward lemmas with free variables inclusion for restricted closures *****)

lemma lfeq_lfxs_trans: ∀R. lfeq_transitive R →
                       ∀L1,L,T. L1 ≡[T] L → ∀L2. L ⪤*[R, T] L2 → L1 ⪤*[R, T] L2.
/4 width=16 by lfeq_fsle_comp, lfxs_trans_fsle, lfxs_trans_next/ qed-.
