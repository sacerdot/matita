(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

(* A THEORY OF CONVERGENCE
   Initial invocation: - Patience on me to gain peace and perfection! -
*)

include "convergence/domains/domain.ma".
include "convergence/notation/functions/category_d_s_1.ma".
include "convergence/notation/functions/set_idx_2.ma".
include "convergence/notation/functions/at_s_3.ma".
include "convergence/notation/functions/element_i_2.ma".
include "convergence/notation/functions/element_d_3.ma".
include "convergence/notation/functions/asterisk_4.ma".

(* DIRECTION ****************************************************************)

(* Structure ****************************************************************)

record direction_structure (S:𝔻𝟬): Type[1] ≝
{ dir_I: (𝔻𝟬)
; dir_D: dir_I → 𝒫❨S❩
; dir_i: dir_I
; dir_d: dir_I → S
; dir_a: dir_I → dir_I → dir_I
}.

interpretation
  "structure (direction)"
  'CategoryD_s S = (direction_structure S).

interpretation
  "index set (direction structure)"
  'SetIDX S D = (dir_I S D).

interpretation
  "superset member (direction structure)"
  'At_s S D i = (dir_D S D i).

interpretation
  "inhabitant (direction structure)"
  'ElementI S D = (dir_i S D).

interpretation
  "member inhabitant (direction structure)"
  'ElementD S D i = (dir_d S D i).

interpretation
  "intersection (direction structure)"
  'Asterisk S D i1 i2 = (dir_a S D i1 i2).
