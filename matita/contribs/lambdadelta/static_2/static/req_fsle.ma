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

include "static_2/static/rex_length.ma".
include "static_2/static/rex_fsle.ma".
include "static_2/static/req.ma".

(* SYNTACTIC EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES *********)

(* Properties with free variables inclusion for restricted closures *********)

lemma req_fsle_comp: rex_fsle_compatible ceq.
#L1 #L2 #T #HL12
elim (frees_total L1 T)
/4 width=8 by frees_req_conf, rex_fwd_length, lveq_length_eq, sle_refl, ex4_4_intro/
qed.

(* Forward lemmas with free variables inclusion for restricted closures *****)

lemma req_rex_trans: ∀R. req_transitive R →
                     ∀L1,L,T. L1 ≡[T] L → ∀L2. L ⪤[R,T] L2 → L1 ⪤[R,T] L2.
/4 width=16 by req_fsle_comp, rex_trans_fsle, rex_trans_next/ qed-.
