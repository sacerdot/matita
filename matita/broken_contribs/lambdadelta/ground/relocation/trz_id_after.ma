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

include "ground/relocation/trz_id.ma".
include "ground/relocation/trz_after.ma".

(* IDENTITY ELEMENT FOR TOTAL RELOCATION MAPS WITH INTEGERS *****************)

(* Constructions with trz_after *********************************************)

lemma trz_after_id_dx (f):
      f ≐ f•𝐢.
// qed.

lemma trz_after_id_sn (f):
      f ≐ 𝐢•f.
// qed.
