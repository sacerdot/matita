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

include "ground_2/arith.ma".

(* ITEMS ********************************************************************)

(* atomic items *)
inductive item0: Type[0] ≝
   | Sort: nat → item0 (* sort: starting at 0 *)
   | LRef: nat → item0 (* reference by index: starting at 0 *)
   | GRef: nat → item0 (* reference by position: starting at 0 *)
.

(* binary binding items *)
inductive bind2: Type[0] ≝
  | Abbr: bind2 (* abbreviation *)
  | Abst: bind2 (* abstraction *)
.

(* binary non-binding items *)
inductive flat2: Type[0] ≝
  | Appl: flat2 (* application *)
  | Cast: flat2 (* explicit type annotation *)
.

(* binary items *)
inductive item2: Type[0] ≝
  | Bind2: bool → bind2 → item2 (* polarized binding item *)
  | Flat2: flat2 → item2        (* non-binding item *)
.

(* TERMS ********************************************************************)

include "basic_2/notation/constructors/item0_1.ma".
include "basic_2/notation/constructors/snitem2_3.ma".
include "basic_2/notation/constructors/snbind2_4.ma".
include "basic_2/notation/constructors/snbind2pos_3.ma".
include "basic_2/notation/constructors/snbind2neg_3.ma".
include "basic_2/notation/constructors/snflat2_3.ma".
include "basic_2/notation/constructors/star_1.ma".
include "basic_2/notation/constructors/lref_1.ma".
include "basic_2/notation/constructors/gref_1.ma".
include "basic_2/notation/constructors/snabbr_3.ma".
include "basic_2/notation/constructors/snabbrpos_2.ma".
include "basic_2/notation/constructors/snabbrneg_2.ma".
include "basic_2/notation/constructors/snabst_3.ma".
include "basic_2/notation/constructors/snabstpos_2.ma".
include "basic_2/notation/constructors/snabstneg_2.ma".
include "basic_2/notation/constructors/snappl_2.ma".
include "basic_2/notation/constructors/sncast_2.ma".
include "basic_2/grammar/item.ma".

(* terms *)
inductive term: Type[0] ≝
  | TAtom: item0 → term               (* atomic item construction *)
  | TPair: item2 → term → term → term (* binary item construction *)
.

interpretation "term construction (atomic)"
   'Item0 I = (TAtom I).

interpretation "term construction (binary)"
   'SnItem2 I T1 T2 = (TPair I T1 T2).

interpretation "term binding construction (binary)"
   'SnBind2 a I T1 T2 = (TPair (Bind2 a I) T1 T2).

interpretation "term positive binding construction (binary)"
   'SnBind2Pos I T1 T2 = (TPair (Bind2 true I) T1 T2).

interpretation "term negative binding construction (binary)"
   'SnBind2Neg I T1 T2 = (TPair (Bind2 false I) T1 T2).

interpretation "term flat construction (binary)"
   'SnFlat2 I T1 T2 = (TPair (Flat2 I) T1 T2).

interpretation "sort (term)"
   'Star k = (TAtom (Sort k)).

interpretation "local reference (term)"
   'LRef i = (TAtom (LRef i)).

interpretation "global reference (term)"
   'GRef p = (TAtom (GRef p)).

interpretation "abbreviation (term)"
   'SnAbbr a T1 T2 = (TPair (Bind2 a Abbr) T1 T2).

interpretation "positive abbreviation (term)"
   'SnAbbrPos T1 T2 = (TPair (Bind2 true Abbr) T1 T2).

interpretation "negative abbreviation (term)"
   'SnAbbrNeg T1 T2 = (TPair (Bind2 false Abbr) T1 T2).

interpretation "abstraction (term)"
   'SnAbst a T1 T2 = (TPair (Bind2 a Abst) T1 T2).

interpretation "positive abstraction (term)"
   'SnAbstPos T1 T2 = (TPair (Bind2 true Abst) T1 T2).

interpretation "negative abstraction (term)"
   'SnAbstNeg T1 T2 = (TPair (Bind2 false Abst) T1 T2).

interpretation "application (term)"
   'SnAppl T1 T2 = (TPair (Flat2 Appl) T1 T2).

interpretation "native type annotation (term)"
   'SnCast T1 T2 = (TPair (Flat2 Cast) T1 T2).

(* WEIGHT OF A TERM *********************************************************)

include "basic_2/notation/functions/weight_1.ma".

let rec tw T ≝ match T with
[ TAtom _     ⇒ 1
| TPair _ V T ⇒ tw V + tw T + 1
].

interpretation "weight (term)" 'Weight T = (tw T).

(* LOCAL ENVIRONMENTS *******************************************************)

include "basic_2/notation/constructors/star_0.ma".
include "basic_2/notation/constructors/dxbind2_3.ma".
include "basic_2/notation/constructors/dxabbr_2.ma".
include "basic_2/notation/constructors/dxabst_2.ma".

(* local environments *)
inductive lenv: Type[0] ≝
| LAtom: lenv                       (* empty *)
| LPair: lenv → bind2 → term → lenv (* binary binding construction *)
.

interpretation "sort (local environment)"
   'Star = LAtom.

interpretation "environment binding construction (binary)"
   'DxBind2 L I T = (LPair L I T).

interpretation "abbreviation (local environment)"
   'DxAbbr L T = (LPair L Abbr T).

interpretation "abstraction (local environment)"
   'DxAbst L T = (LPair L Abst T).

(* WEIGHT OF A LOCAL ENVIRONMENT ********************************************)

let rec lw L ≝ match L with
[ LAtom       ⇒ 0
| LPair L _ V ⇒ lw L + ♯{V}
].

interpretation "weight (local environment)" 'Weight L = (lw L).

(* GLOBAL ENVIRONMENTS ******************************************************)

include "ground_2/list.ma".

(* global environments *)
definition genv ≝ list2 bind2 term.

interpretation "sort (global environment)"
   'Star = (nil2 bind2 term).

interpretation "environment binding construction (binary)"
   'DxBind2 L I T = (cons2 bind2 term I T L).

interpretation "abbreviation (global environment)"
   'DxAbbr L T = (cons2 bind2 term Abbr T L).

interpretation "abstraction (global environment)"
   'DxAbst L T = (cons2 bind2 term Abst T L).

(* WEIGHT OF A CLOSURE ******************************************************)

include "basic_2/notation/functions/weight_3.ma".

(* activate genv *)
definition fw: genv → lenv → term → ? ≝ λG,L,T. ♯{L} + ♯{T}.

interpretation "weight (closure)" 'Weight G L T = (fw G L T).

(* Basic properties *********************************************************)

(* Basic_1: was: flt_shift *)
lemma fw_shift: ∀a,I,G,K,V,T. ♯{G, K.ⓑ{I}V, T} < ♯{G, K, ⓑ{a,I}V.T}.
normalize //
qed.
