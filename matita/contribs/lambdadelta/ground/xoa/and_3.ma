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

(* This file was generated by xoa.native: do not edit *********************)

include "basics/pts.ma".

include "ground/notation/xoa/and_3.ma".

(* multiple conjunction connective (3) *)

inductive and3 (P0,P1,P2:Prop) : Prop ≝
   | and3_intro: P0 → P1 → P2 → and3 ? ? ?
.

interpretation "multiple conjunction connective (3)" 'And P0 P1 P2 = (and3 P0 P1 P2).
