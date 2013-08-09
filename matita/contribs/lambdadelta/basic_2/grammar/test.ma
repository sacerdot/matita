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

include "arithmetics/nat.ma".

(* notations ****************************************************************)

include "basic_2/notation/constructors/snbind2_4.ma".
include "basic_2/notation/constructors/dxbind2_3.ma".
include "basic_2/notation/functions/weight_1.ma".
include "basic_2/notation/functions/weight_3.ma".

(* definitions **************************************************************)

inductive list2 (A1,A2:Type[0]) : Type[0] :=
  | nil2 : list2 A1 A2
  | cons2: A1 → A2 → list2 A1 A2 → list2 A1 A2.


inductive item0: Type[0] ≝
   | Sort: nat → item0
   | LRef: nat → item0
   | GRef: nat → item0
.

inductive bind2: Type[0] ≝
  | Abbr: bind2
  | Abst: bind2 
.

inductive flat2: Type[0] ≝
  | Appl: flat2
  | Cast: flat2
.

inductive item2: Type[0] ≝
  | Bind2: bool → bind2 → item2
  | Flat2: flat2 → item2
.

inductive term: Type[0] ≝
  | TAtom: item0 → term
  | TPair: item2 → term → term → term 
.

let rec tw T ≝ match T with
[ TAtom _     ⇒ 1
| TPair _ V T ⇒ tw V + tw T + 1
].

inductive lenv: Type[0] ≝
| LAtom: lenv
| LPair: lenv → bind2 → term → lenv
.

let rec lw L ≝ match L with
[ LAtom       ⇒ 0
| LPair L _ V ⇒ lw L + tw V
].

definition genv ≝ list2 bind2 term.

definition fw: genv → lenv → term → ? ≝ λG,L,T. (lw L) + (tw T).

(* interpretations **********************************************************)

interpretation "term binding construction (binary)"
   'SnBind2 a I T1 T2 = (TPair (Bind2 a I) T1 T2).

interpretation "weight (term)" 'Weight T = (tw T).

interpretation "weight (local environment)" 'Weight L = (lw L).

interpretation "weight (closure)" 'Weight G L T = (fw G L T).

(* first set *)

interpretation "environment binding construction (binary)"
   'DxBind2 L I T = (LPair L I T).

(* second set *)

interpretation "environment binding construction (binary)"
   'DxBind2 L I T = (cons2 bind2 term I T L).

(* statements ***************************************************************)

lemma fw_shift: ∀a,I,G,K,V,T. ♯{G, K.ⓑ{I}V, T} < ♯{G, K, ⓑ{a,I}V.T}.
normalize //
qed.
