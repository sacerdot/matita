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

include "basics/logic.ma".
include "ground/notation/generated/times_2.ma".
include "ground/notation/generated/tuple_4.ma".
include "ground/notation/generated/tuple2_0.ma".

(* GENERATED LIBRARY ********************************************************)

record prod_2 (A1,A2:Type[0]): Type[0] ≝
  { proj_2_1: A1
  ; proj_2_2: A2
  }.

interpretation
  "product 2"
  'Times A1 A2 = (prod_2 A1 A2).

interpretation
  "tuple 2"
  'Tuple A1 A2 a1 a2 = (mk_prod_2 A1 A2 a1 a2).

interpretation
  "abstract tuple 2"
  'Tuple2 = (mk_prod_2 ? ?).
