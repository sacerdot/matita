(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

(* A THEORY OF CONVERGENCE
   Initial invocation: - Patience on me to gain peace and perfection! -
*)

include "convergence/subsets/subset_sigma.ma".
include "convergence/classes/class.ma".
include "convergence/notation/functions/category_d_s_1.ma".
include "convergence/notation/functions/set_idx_2.ma".
include "convergence/notation/functions/at_3.ma".
include "convergence/notation/functions/element_i_2.ma".
include "convergence/notation/functions/element_d_3.ma".
include "convergence/notation/functions/asterisk_4.ma".

(* DIRECTION ****************************************************************)

(* Structure ****************************************************************)

record direction_structure (X:ℂ𝟬𝗌): Type[1] ≝
{ dir_I: (ℂ𝟬)
; dir_D: dir_I → 𝒫❨X❩
; dir_i: dir_I
; dir_d: ∀i:dir_I. 𝝨X.(dir_D i)
; dir_a: dir_I → dir_I → dir_I
}.

interpretation
  "structure (direction)"
  'CategoryD_s X = (direction_structure X).

interpretation
  "index set (direction structure)"
  'SetIDX X D = (dir_I X D).

interpretation
  "superset member (direction structure)"
  'At X D i = (dir_D X D i).

interpretation
  "inhabitant (direction structure)"
  'ElementI X D = (dir_i X D).

interpretation
  "member inhabitant (direction structure)"
  'ElementD X D i = (dir_d X D i).

interpretation
  "intersection (direction structure)"
  'Asterisk X D i1 i2 = (dir_a X D i1 i2).
