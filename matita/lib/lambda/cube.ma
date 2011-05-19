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

include "convertibility.ma".
include "types.ma".

(* PURE TYPE SYSTEMS OF THE λ-CUBE ********************************************)

inductive Cube_Ax (i,j:nat): Prop ≝
  | star_box: i = 0 → j = 1 → Cube_Ax i j
.

(* The λPω pure type system (a.k.a. λC or CC) *********************************)

inductive CC_Re (i,j,k:nat): Prop ≝
   | star_star: i = 0 → j = 0 → k = 0 → CC_Re i j k
   | box_star : i = 1 → j = 0 → k = 0 → CC_Re i j k
   | box_box  : i = 1 → j = 1 → k = 1 → CC_Re i j k
   | star_box : i = 0 → j = 1 → k = 1 → CC_Re i j k
.

definition CC: pts ≝ mk_pts Cube_Ax CC_Re conv.

(* The λω pure type system (a.k.a. Fω) ****************************************)

inductive FO_Re (i,j,k:nat): Prop ≝
   | star_star: i = 0 → j = 0 → k = 0 → FO_Re i j k
   | box_star : i = 1 → j = 0 → k = 0 → FO_Re i j k
   | box_box  : i = 1 → j = 1 → k = 1 → FO_Re i j k
.

definition FO: pts ≝ mk_pts Cube_Ax FO_Re conv.
