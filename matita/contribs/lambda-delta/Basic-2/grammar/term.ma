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

include "Basic-2/grammar/item.ma".

(* TERMS ********************************************************************)

(* terms *)
inductive term: Type[0] ≝
| TSort: nat → term                 (* sort: starting at 0 *)
| TLRef: nat → term                 (* reference by index: starting at 0 *)
| TPair: item2 → term → term → term (* binary item construction *)
.

interpretation "sort (term)" 'Star k = (TSort k).

interpretation "local reference (term)" 'LRef i = (TLRef i).

interpretation "term construction (binary)" 'SItem I T1 T2 = (TPair I T1 T2).

interpretation "term binding construction (binary)" 'SBind I T1 T2 = (TPair (Bind I) T1 T2).

interpretation "term flat construction (binary)" 'SFlat I T1 T2 = (TPair (Flat I) T1 T2).
