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
include "ground/notation/generated/times_4.ma".
include "ground/notation/generated/tuple_8.ma".
include "ground/notation/generated/tuple4_0.ma".

(* GENERATED LIBRARY ********************************************************)

record prod_4 (A1,A2,A3,A4:Type[0]): Type[0] ≝
  { proj_4_1: A1
  ; proj_4_2: A2
  ; proj_4_3: A3
  ; proj_4_4: A4
  }.

interpretation
  "product 4"
  'Times A1 A2 A3 A4 = (prod_4 A1 A2 A3 A4).

interpretation
  "tuple 4"
  'Tuple A1 A2 A3 A4 a1 a2 a3 a4 = (mk_prod_4 A1 A2 A3 A4 a1 a2 a3 a4).

interpretation
  "abstract tuple 4"
  'Tuple4 = (mk_prod_4 ? ? ? ?).
