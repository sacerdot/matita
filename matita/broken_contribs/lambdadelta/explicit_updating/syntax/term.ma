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

(* A SYSTEM OF λ-CALCULUS WITH EXPLICIT UPDATING DERIVED FROM AUT 55 (1978)
 * Initial invocation: - Patience on me to gain peace and perfection! -
 *)

include "ground/relocation/fb/fbr_map.ma".
include "explicit_updating/notation/functions/category_t_0.ma".
include "explicit_updating/notation/functions/xi_0.ma".
include "explicit_updating/notation/functions/lamda_2.ma".
include "explicit_updating/notation/functions/at_2.ma".
include "explicit_updating/notation/functions/phi_2.ma".

(* TERM *********************************************************************)

inductive term: Type[0] ≝
| unit: term
| abst: bool → term → term
| appl: term → term → term
| lift: 𝔽𝔹 → term → term
.

interpretation
  "term ()"
  'CategoryT = (term).

interpretation
  "reference to first variable by depth (term)"
  'Xi = (unit).

interpretation
  "marked name-free functional abstraction (term)"
  'Lamda b t = (abst b t).

interpretation
  "application (term)"
  'At u t = (appl u t).

interpretation
  "finite lift (term)"
  'Phi f t = (lift f t).
