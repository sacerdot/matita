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

include "ground_2/notation/functions/uparrowstar_2.ma".
include "apps_2/notation/functional/uparrow_2.ma".
include "static_2/relocation/lifts.ma".

(* GENERIC FUNCTIONAL RELOCATION ********************************************)

rec definition flifts f U on U ≝ match U with
[ TAtom I     ⇒ match I with
  [ Sort _ ⇒ U
  | LRef i ⇒ #(f@❴i❵)
  | GRef _ ⇒ U
  ]
| TPair I V T ⇒ match I with
  [ Bind2 p I ⇒ ⓑ{p,I}(flifts f V).(flifts (⫯f) T)
  | Flat2 I   ⇒ ⓕ{I}(flifts f V).(flifts f T)
  ]
].

interpretation "generic functional relocation (term)"
   'UpArrowStar f T = (flifts f T).

interpretation "uniform functional relocation (term)"
   'UpArrow i T = (flifts (uni i) T).

(* Basic properties *********************************************************)

lemma flifts_lref (f) (i): ↑*[f](#i) = #(f@❴i❵).
// qed.

lemma flifts_bind (f) (p) (I) (V) (T): ↑*[f](ⓑ{p,I}V.T) = ⓑ{p,I}↑*[f]V.↑*[⫯f]T.
// qed.

lemma flifts_flat (f) (I) (V) (T): ↑*[f](ⓕ{I}V.T) = ⓕ{I}↑*[f]V.↑*[f]T.
// qed.

(* Main properties **********************************************************)

theorem flifts_lifts: ∀T,f. ⬆*[f]T ≘ ↑*[f]T.
#T elim T -T *
/2 width=1 by lifts_sort, lifts_lref, lifts_gref, lifts_bind, lifts_flat/
qed.

(* Main inversion properties ************************************************)

theorem flifts_inv_lifts: ∀f,T1,T2. ⬆*[f]T1 ≘ T2 → ↑*[f]T1 = T2.
#f #T1 #T2 #H elim H -f -T1 -T2 //
[ #f #i1 #i2 #H <(at_inv_total … H) //
| #f #p #I #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT <IHV <IHT -V2 -T2 //
| #f #I #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT <IHV <IHT -V2 -T2 //
]
qed-.

(* Derived properties *******************************************************)

lemma flifts_comp: ∀f1,f2. f1 ≡ f2 → ∀T. ↑*[f1]T = ↑*[f2]T.
/3 width=3 by flifts_inv_lifts, lifts_eq_repl_fwd/ qed.

(* Derived properties with uniform relocation *******************************)

lemma flifts_lref_uni: ∀l,i. ↑[l](#i) = #(l+i).
/3 width=1 by flifts_inv_lifts, lifts_lref_uni/ qed.
