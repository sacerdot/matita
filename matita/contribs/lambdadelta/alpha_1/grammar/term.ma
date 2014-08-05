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

include "basic_2/notation/constructors/snitem2_3.ma".
include "basic_2/notation/constructors/star_0.ma".
include "basic_2/notation/constructors/snabstpos_2.ma".
include "basic_2/notation/constructors/snabbr_3.ma".
include "basic_2/notation/constructors/snabbrpos_2.ma".
include "basic_2/notation/constructors/snabbrneg_2.ma".
include "alpha_1/notation/constructors/snitem1_2.ma".
include "alpha_1/notation/constructors/snstar_2.ma".
include "alpha_1/notation/constructors/snlref_2.ma".
include "alpha_1/notation/constructors/sngref_2.ma".
include "alpha_1/notation/constructors/snabstneg_1.ma".
include "alpha_1/notation/constructors/snproj_3.ma".
include "alpha_1/notation/constructors/snprojpos_2.ma".
include "alpha_1/notation/constructors/snprojneg_2.ma".
include "alpha_1/grammar/item.ma".

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
   'SnStar k T = (TUnit (Char k) T).

interpretation "local reference (term)"
   'SnLRef i T = (TUnit (LRef i) T).

interpretation "global reference (term)"
   'SnGRef p T = (TUnit (GRef p) T).

interpretation "negative abbreviation (term)"
   'SnAbbrNeg T = (TUnit Decl T).

interpretation "positive abstraction (term)"
   'SnAbstPos T1 T2 = (TPair Abst T1 T2).

interpretation "abbreviation (term)"
   'SnAbbr a T1 T2 = (TPair (Abbr a) T1 T2).

interpretation "positive abbreviation (term)"
   'SnAbbrPos T1 T2 = (TPair (Abbr true) T1 T2).

interpretation "negative abbreviation (term)"
   'SnAbbrNeg T1 T2 = (TPair (Abbr false) T1 T2).

interpretation "projection (term)"
   'SnProj a T1 T2 = (TPair (Proj a) T1 T2).

interpretation "positive projection (term)"
   'SnProjPos T1 T2 = (TPair (Proj true) T1 T2).

interpretation "negative projection (term)"
   'SnProjNeg T1 T2 = (TPair (Proj false) T1 T2).
