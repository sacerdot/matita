(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/domains/function_posts.ma".
include "convergence/notation/functions/right_double_arrow_2.ma".

(* ABSTRACT FUNCTION ********************************************************)

(* Object *******************************************************************)

record function (D:𝔻𝟬) (C:𝔻𝟬): Type[0] ≝
{ fun_S:1> D → C
; fun_P:> fun_S 𝛆 D ⇒𝗽 C
}.

interpretation
  "function (category)"
  'RightDoubleArrow D C = (function D C).

(* Note: notation for extesional equality: ≗ 2257 RingEqual *)
