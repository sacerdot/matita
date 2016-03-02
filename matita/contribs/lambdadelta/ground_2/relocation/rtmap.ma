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

include "ground_2/relocation/nstream.ma".

(* RELOCATION MAP ***********************************************************)

lemma pn_split: ∀f. (∃g. ↑g = f) ∨ (∃g. ⫯g = f).
@case_prop /3 width=2 by or_introl, or_intror, ex_intro/
qed-.
