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

include "basic_2/notation/relations/predtysnstar_4.ma".
include "basic_2/relocation/lex.ma".
include "basic_2/rt_computation/cpxs.ma".

(* UNCOUNTED PARALLEL RT-COMPUTATION FOR LOCAL ENVIRONMENTS *****************)

definition lpxs: ∀h. relation3 genv lenv lenv ≝
                 λh,G. lex (cpxs h G).

interpretation
   "uncounted parallel rt-computation (local environment)"
   'PRedTySnStar h G L1 L2 = (lpxs h G L1 L2).
