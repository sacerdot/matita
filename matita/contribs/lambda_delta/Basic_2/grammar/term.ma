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

include "Basic_2/grammar/item.ma".

(* TERMS ********************************************************************)

(* terms *)
inductive term: Type[0] ≝
  | TAtom: item0 → term               (* atomic item construction *)
  | TPair: item2 → term → term → term (* binary item construction *)
.

interpretation "sort (term)" 'Star k = (TAtom (Sort k)).

interpretation "local reference (term)" 'LRef i = (TAtom (LRef i)).

interpretation "term construction (atomic)" 'SItem I = (TAtom I).

interpretation "term construction (binary)" 'SItem I T1 T2 = (TPair I T1 T2).

interpretation "term binding construction (binary)" 'SBind I T1 T2 = (TPair (Bind I) T1 T2).

interpretation "term flat construction (binary)" 'SFlat I T1 T2 = (TPair (Flat I) T1 T2).
