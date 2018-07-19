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

include "apps_2/notation/functional/blackcircle_3.ma".
include "apps_2/functional/mf_vlift.ma".
include "apps_2/functional/mf_vpush.ma".

(* MULTIPLE FILLING FOR TERMS ***********************************************)

rec definition mf gv lv T on T ≝ match T with
[ TAtom I     ⇒ match I with
  [ Sort _ ⇒ T
  | LRef i ⇒ lv i
  | GRef l ⇒ gv l
  ]
| TPair I V T ⇒ match I with
  [ Bind2 _ _ ⇒ TPair I (mf gv lv V) (mf (⇡[0]gv) (⇡[0←#0]lv) T)
  | Flat2 _   ⇒ TPair I (mf gv lv V) (mf gv lv T)
  ]
].

interpretation "term filling (multiple filling)"
  'BlackCircle gv lv T = (mf gv lv T).

(* Basic Properties *********************************************************)

lemma mf_sort: ∀gv,lv,s. ●[gv,lv]⋆s = ⋆s.
// qed.

lemma mf_lref: ∀gv,lv,i. ●[gv,lv]#i = lv i.
// qed.

lemma mf_gref: ∀gv,lv,l. ●[gv,lv]§l = gv l.
// qed.

lemma mf_bind (p) (I): ∀gv,lv,V,T.
                       ●[gv,lv]ⓑ{p,I}V.T = ⓑ{p,I}●[gv,lv]V.●[⇡[0]gv,⇡[0←#0]lv]T.
// qed.

lemma mf_flat (I): ∀gv,lv,V,T.
                   ●[gv,lv]ⓕ{I}V.T = ⓕ{I}●[gv,lv]V.●[gv,lv]T.
// qed.
