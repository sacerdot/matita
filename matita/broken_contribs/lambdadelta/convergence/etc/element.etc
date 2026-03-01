(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/domains/domain.ma".
include "convergence/notation/functions/set_ext_1.ma".

(* ABSTRACT ELEMENT *********************************************************)

record element (X:𝔻𝟬): Type[0] ≝
{ elt_S:> X
; elt_P:> elt_S ϵ X
}.

interpretation
  "element (domain)"
  'SetEXT X = (element X).
