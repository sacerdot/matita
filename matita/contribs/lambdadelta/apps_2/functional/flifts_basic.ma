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

include "ground_2/relocation/rtmap_basic.ma".
include "apps_2/functional/flifts.ma".
include "apps_2/notation/functional/uparrow_3.ma".

(* GENERIC FUNCTIONAL RELOCATION ********************************************)

interpretation "basic functional relocation (term)"
   'UpArrow d h T = (flifts (basic d h) T).
