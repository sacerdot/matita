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

include "ground/arith/pnat_iter.ma".

(* POSITIVE INTEGERS ********************************************************)

definition pplus: pnat → pnat → pnat ≝
           λp,q. psucc^q p.

interpretation
  "plus (positive integers"
  'plus p q = (pplus p q).

(* Basic rewrites ***********************************************************)

lemma pplus_one_dx (p): ↑p = p + 𝟏.
// qed.

lemma pplus_succ_dx (p) (q): ↑(p+q) = p + ↑q.
// qed.

(* Semigroup properties *****************************************************)

lemma pplus_succ_sn (p) (q): ↑(p+q) = ↑p + q.
#p #q @(piter_appl … psucc)
qed.

lemma pplus_one_sn (p): ↑p = 𝟏 + p.
#p elim p -p //
qed.

lemma pplus_comm: commutative … pplus.
#p elim p -p //
qed.

lemma pplus_assoc: associative … pplus.
#p #q #r elim r -r //
#r #IH <pplus_succ_dx <pplus_succ_dx <IH -IH //
qed.
