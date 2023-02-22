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

include "ground/relocation/nstream_basic.ma".
include "apps_2/functional/flifts.ma".
include "apps_2/notation/functional/uparrow_3.ma".

(* BASIC FUNCTIONAL RELOCATION **********************************************)

interpretation "basic functional relocation (term)"
   'UpArrow d h T = (flifts (basic d h) T).

(* Basic properties *********************************************************)

lemma flifts_basic_lref_ge (i) (d) (h): d ≤ i → ↑[d,h](#i) = #(h+i).
#i #d #h #Hdi
/4 width=1 by apply_basic_ge, (* 2x *) eq_f/
qed-.

lemma flifts_basic_bind (p) (I) (V) (T) (d) (h): ↑[d,h](ⓑ[p,I]V.T) = ⓑ[p,I](↑[d,h]V).(↑[↑d,h]T).
// qed.
