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

(* THE FORMAL SYSTEM λα: MATITA SOURCE FILES
 * Initial invocation: - Patience on me to gain peace and perfection! -
 * Conceived since: 2014 July 25
 * Developed since: 2021 June 17
 *)

include "ground/arith/nat.ma".
include "static_2/notation/functions/star_1.ma".
include "static_2/notation/functions/gref_1.ma".
include "static_2/notation/functions/snappl_2.ma".
include "static_2/notation/functions/snabbr_2.ma".
include "alpha_1/notation/functions/snabst_1.ma".

(* TERMS ********************************************************************)

(* terms *)
inductive term: Type[0] ≝
  | TChar: nat → term          (* character: starts at 0 *)
  | TGRef: nat → term          (* reference by level: starts at 0 *)
  | TAbst: term → term         (* abstraction: scope *)
  | TAbbr: term → term → term  (* abbreviation: definition, scope *)
  | TCons: term → term → term  (* group: body, tail *)
.

interpretation
  "character (terms)"
  'Star c = (TChar c).

interpretation
  "reference (terms)"
  'GRef l = (TGRef l).

interpretation
  "group (terms)"
  'SnAppl T1 T2 = (TCons T1 T2).

interpretation
  "abbreviation (terms)"
  'SnAbbr T1 T2 = (TAbbr T1 T2).

interpretation
  "abstraction (terms)"
  'SnAbst T = (TAbst T).
