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



include "metric_lattice.ma".
include "sequence.ma".
include "constructive_connectives.ma".

(* Section 3.2 *)

(* 3.21 *)


(* 3.17 *)


(* 3.20 *)
lemma uniq_sup: ∀O:ogroup.∀s:sequence O.∀x,y:O. is_sup ? s x → is_sup ? s y → x ≈ y.
intros; 