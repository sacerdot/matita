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

include "basic_2/static/frees_lreq.ma".
include "basic_2/static/lfeq.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES *******************)

(* Inversion lemmas with ranged equivalence for local environments **********)

lemma lfeq_inv_lreq: ∀L1,L2,T. L1 ≡[T] L2 → ∃∃f. L1 ⊢ 𝐅*⦃T⦄ ≡ f & L1 ≡[f] L2.
#L1 #L2 #T * /2 width=3 by ex2_intro/
qed-.

(* Properties with ranged equivalence for local environments ****************)

lemma lreq_lfeq: ∀f,L1,L2,T. L1 ⊢ 𝐅*⦃T⦄ ≡ f → L1 ≡[f] L2 → L1 ≡[T] L2.
/2 width=3 by ex2_intro/ qed.

(* Advanced properties ******************************************************)

lemma lfeq_sym: ∀T. symmetric … (lfeq T).
#T #L1 #L2 #H elim (lfeq_inv_lreq … H) -H
/3 width=3 by lreq_lfeq, frees_lreq_conf, lreq_sym/
qed-.
