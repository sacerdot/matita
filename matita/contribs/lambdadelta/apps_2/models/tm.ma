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

include "basic_2/rt_equivalence/cpcs.ma".
include "apps_2/functional/mf.ma".
include "apps_2/models/model.ma".

(* TERM MODEL ***************************************************************)

definition tm_dd ≝ term.

definition tm_sq (h) (T1) (T2) ≝  ⦃⋆,⋆⦄ ⊢ T1 ⬌*[h] T2.

definition tm_sv (s) ≝ ⋆s.

definition tm_co (p) (V) (T) ≝ ⓓ{p}V.(↑[1]T).

definition tm_ap (V) (T) ≝ ⓐV.T.

definition tm_ti (gv) (lv) (T) ≝ ●[gv,lv]T.

definition TM (h): model ≝ mk_model … .
[ @tm_dd
| @(tm_sq h) |7,8: skip
| @tm_sv
| @tm_co
| @tm_ap
| @tm_ti
].
defined-.

(* Basic properties *********************************************************)

lemma tm_co_rw (h) (p) (V) (T): V⊕{TM h}[p]T = ⓓ{p}V.(↑[1]T).
// qed.

lemma tm_ti_sort (h) (gv) (lv): ∀s. ⟦⋆s⟧{TM h}[gv,lv] = sv … s.
// qed.

lemma tm_ti_lref (h): ∀gv,lv,i. ⟦#i⟧{TM h}[gv,lv] = lv i.
// qed.

lemma tm_ti_gref (h): ∀gv,lv,l. ⟦§l⟧{TM h}[gv,lv] = gv l.
// qed.

lemma tm_ti_bind (h) (p) (I): ∀gv,lv,V,T.
                              ⟦ⓑ{p,I}V.T⟧{TM h}[gv,lv] = ⓑ{p,I}⟦V⟧[gv,lv].⟦T⟧{TM h}[⇡[0]gv,⇡[0←#0]lv].
// qed.
