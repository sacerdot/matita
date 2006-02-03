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

set "baseuri" "cic:/matita/LAMBDA-TYPES/lref_map_defs".

include "terms_defs.ma".

inductive tlref_map (A: Set) (N: Set) (map: nat \to nat): nat \to (T A N) \to (T A N) \to Prop \def
   | tlref_map_sort: \forall i. \forall k. \forall y. (tlref_map A N map i (TSort A N y k) (TSort A N y k))
   | tlref_map_lref_lt: \forall j. \forall i. \forall y. j < i \to (tlref_map A N map i (TLRef A N y j) (TLRef A N y j))
   | tlref_map_lref_ge: \forall j. \forall i. \forall y. i \le j \to (tlref_map A N map i (TLRef A N y j) (TLRef A N y (map j))).
