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
include "apps_2/functional/flifts_basic.ma".
include "apps_2/models/model.ma".
include "apps_2/notation/models/dotteduparrow_2.ma".
include "apps_2/notation/models/dotteduparrow_3.ma".

(* TERM MODEL ***************************************************************)

definition tm_dd ≝ term.

definition tm_evaluation ≝ nat → tm_dd.

definition tm_sq (h) (T1) (T2) ≝  ⦃⋆, ⋆⦄ ⊢ T1 ⬌*[h] T2.

definition tm_sv (s) ≝ ⋆s.

definition tm_ap (V) (T) ≝ ⓐV.T.

definition tm_vlift (j) (gv): tm_evaluation ≝ λi. ↑[j,1](gv i).

interpretation "lift (term model evaluation)"
  'DottedUpArrow i gv = (tm_vlift i gv).

definition tm_vpush (j) (T) (lv): tm_evaluation ≝
                    λi. tri … i j (lv i) T (↑[j,1](lv (↓i))).

interpretation "push (term model evaluation)"
  'DottedUpArrow i d lv = (tm_vpush i d lv).

rec definition tm_ti gv lv T on T ≝ match T with
[ TAtom I     ⇒ match I with
  [ Sort _ ⇒ T
  | LRef i ⇒ lv i
  | GRef l ⇒ gv l
  ]
| TPair I V T ⇒ match I with
  [ Bind2 _ _ ⇒ TPair I (tm_ti gv lv V) (tm_ti (⇡[0]gv) (⇡[0←#0]lv) T)
  | Flat2 _   ⇒ TPair I (tm_ti gv lv V) (tm_ti gv lv T)
  ]
].

definition tm_lc: tm_evaluation ≝ λi.#i.

definition tm_gc: tm_evaluation ≝ λl.§l.

definition TM (h): model ≝ mk_model … .
[ @tm_dd
| @(tm_sq h) |6,7: skip
| @tm_sv
| @tm_ap
| @tm_ti
].
defined-.

(* Basic properties *********************************************************)

lemma tm_vlift_rw (j) (gv): ∀i. (⇡[j]gv) i = ↑[j,1](gv i).
// qed.

lemma tm_vpush_lt (lv) (j) (T): ∀i. i < j → (⇡[j←T]lv) i = lv i.
/2 width=1 by tri_lt/ qed-.

lemma tm_vpush_eq: ∀lv,T,i. (⇡[i←T]lv) i = T.
/2 width=1 by tri_eq/ qed.

lemma tm_vpush_gt: ∀lv,T,j,i. j < i → (⇡[j←T]lv) i = ↑[j,1](lv (↓i)).
/2 width=1 by tri_gt/ qed-.

lemma tm_ti_lref (h): ∀gv,lv,i. ⟦#i⟧{TM h}[gv,lv] = lv i.
// qed.

lemma tm_ti_gref (h): ∀gv,lv,l. ⟦§l⟧{TM h}[gv,lv] = gv l.
// qed.

lemma tm_ti_bind (h) (p) (I): ∀gv,lv,V,T.
                              ⟦ⓑ{p,I}V.T⟧{TM h}[gv,lv] = ⓑ{p,I}⟦V⟧[gv,lv].⟦T⟧{TM h}[⇡[0]gv,⇡[0←#0]lv].
// qed.
