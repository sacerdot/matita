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

(* A SYSTEM OF λ-CALCULUS WITH DELAYED UPDATING 
 * Initial invocation: - Patience on me to gain peace and perfection! -
 *)

include "delayed_updating/notation/functions/nodelabel_d_1.ma".
include "delayed_updating/notation/functions/nodelabel_m_0.ma".
include "delayed_updating/notation/functions/edgelabel_l_0.ma".
include "delayed_updating/notation/functions/edgelabel_a_0.ma".
include "delayed_updating/notation/functions/edgelabel_s_0.ma".
include "ground/arith/nat.ma".

(* LABEL ********************************************************************)

inductive label: Type[0] ≝
(* Note: label_d (𝟎) denotes a deactivated inner variable *)
| label_d: ℕ → label
| label_m: label
| label_L: label
| label_A: label
| label_S: label
.

interpretation
  "variable reference by depth (label)"
  'NodeLabelD k = (label_d k).

interpretation
  "mark (label)"
  'NodeLabelM = (label_m).

interpretation
  "name-free functional abstruction (label)"
  'EdgeLabelL = (label_L).

interpretation
  "application (label)"
  'EdgeLabelA = (label_A).

interpretation
  "side branch (label)"
  'EdgeLabelS = (label_S).
