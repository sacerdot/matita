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

include "basic_2/relocation/lexs_lexs.ma".
include "basic_2/relocation/lreq.ma".

(* RANGED EQUIVALENCE FOR LOCAL ENVIRONMENTS ********************************)

(* Main properties **********************************************************)

theorem lreq_trans: ∀f. Transitive … (lreq f).
/2 width=3 by lexs_trans/ qed-.

theorem lreq_canc_sn: ∀f. left_cancellable … (lreq f).
/3 width=3 by lexs_canc_sn, lreq_trans, lreq_sym/ qed-.

theorem lreq_canc_dx: ∀f. right_cancellable … (lreq f).
/3 width=3 by lexs_canc_dx, lreq_trans, lreq_sym/ qed-.

theorem lreq_join: ∀f1,L1,L2. L1 ≡[f1] L2 → ∀f2. L1 ≡[f2] L2 →
                   ∀f. f1 ⋓ f2 ≡ f → L1 ≡[f] L2.
/2 width=5 by lexs_join/ qed-.

theorem lreq_meet: ∀f1,L1,L2. L1 ≡[f1] L2 → ∀f2. L1 ≡[f2] L2 →
                   ∀f. f1 ⋒ f2 ≡ f → L1 ≡[f] L2.
/2 width=5 by lexs_meet/ qed-.
