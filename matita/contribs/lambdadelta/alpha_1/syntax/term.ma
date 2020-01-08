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

include "static_2/notation/functions/snitem2_3.ma".
include "static_2/notation/functions/star_0.ma".
include "static_2/notation/functions/snabstpos_2.ma".
include "static_2/notation/functions/snabbr_3.ma".
include "static_2/notation/functions/snabbrpos_2.ma".
include "static_2/notation/functions/snabbrneg_2.ma".
include "alpha_1/notation/functions/snitem1_2.ma".
include "alpha_1/notation/functions/snstar_2.ma".
include "alpha_1/notation/functions/snlref_2.ma".
include "alpha_1/notation/functions/sngref_2.ma".
include "alpha_1/notation/functions/snabstneg_1.ma".
include "alpha_1/notation/functions/snproj_3.ma".
include "alpha_1/notation/functions/snprojpos_2.ma".
include "alpha_1/notation/functions/snprojneg_2.ma".
include "alpha_1/syntax/item.ma".

(* TERMS ********************************************************************)

(* terms *)
inductive term: Type[0] ≝
  | TAtom:         term                (* atomic item construction *)
  | TUnit: item1 → term → term         (* unary item construction *)
  | TPair: item2 → term → term → term  (* binary item construction *)
.

interpretation "top (term)"
   'Star = TAtom.

interpretation "term construction (unary)"
   'SnItem1 I T = (TUnit I T).

interpretation "term construction (binary)"
   'SnItem2 I T1 T2 = (TPair I T1 T2).

interpretation "character (term)"
   'SnStar s T = (TUnit (Char s) T).

interpretation "local reference (term)"
   'SnLRef i T = (TUnit (LRef i) T).

interpretation "global reference (term)"
   'SnGRef l T = (TUnit (GRef l) T).

interpretation "negative abbreviation (term)"
   'SnAbbrNeg T = (TUnit Decl T).

interpretation "positive abstraction (term)"
   'SnAbstPos T1 T2 = (TPair Abst T1 T2).

interpretation "abbreviation (term)"
   'SnAbbr p T1 T2 = (TPair (Abbr p) T1 T2).

interpretation "positive abbreviation (term)"
   'SnAbbrPos T1 T2 = (TPair (Abbr true) T1 T2).

interpretation "negative abbreviation (term)"
   'SnAbbrNeg T1 T2 = (TPair (Abbr false) T1 T2).

interpretation "projection (term)"
   'SnProj p T1 T2 = (TPair (Proj p) T1 T2).

interpretation "positive projection (term)"
   'SnProjPos T1 T2 = (TPair (Proj true) T1 T2).

interpretation "negative projection (term)"
   'SnProjNeg T1 T2 = (TPair (Proj false) T1 T2).
