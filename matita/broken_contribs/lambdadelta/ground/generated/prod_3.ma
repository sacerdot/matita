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
include "ground/notation/generated/times_3.ma".
include "ground/notation/generated/tuple_6.ma".
include "ground/notation/generated/tuple3_0.ma".

(* GENERATED LIBRARY ********************************************************)

record prod_3 (A1,A2,A3:Type[0]): Type[0] ≝
  { proj_3_1: A1
  ; proj_3_2: A2
  ; proj_3_3: A3
  }.

interpretation
  "product 3"
  'Times A1 A2 A3 = (prod_3 A1 A2 A3).

interpretation
  "tuple 3"
  'Tuple A1 A2 A3 a1 a2 a3 = (mk_prod_3 A1 A2 A3 a1 a2 a3).

interpretation
  "abstract tuple 3"
  'Tuple3 = (mk_prod_3 ? ? ?).
