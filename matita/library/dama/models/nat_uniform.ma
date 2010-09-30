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

include "dama/nat_ordered_set.ma".
include "dama/models/discrete_uniformity.ma".

definition nat_uniform_space: uniform_space.
apply (discrete_uniform_space_of_bishop_set ℕ);
qed.

interpretation "Uniform space N" 'N = nat_uniform_space.
