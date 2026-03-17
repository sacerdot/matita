(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset.ma".
include "convergence/notation/functions/category_c0_s_0.ma".
include "convergence/notation/functions/set_car_1.ma".
include "convergence/notation/relations/equivalent_3.ma".
include "convergence/notation/relations/not_equivalent_3.ma".
include "convergence/notation/relations/neg_equivalent_3.ma".

(* CLASS ********************************************************************)

(* Structure ****************************************************************)

record cls_S: Type[1] ≝
{ cls_sc:> Type[0]
; cls_se:  relation2 cls_sc cls_sc
}.

interpretation
  "structure (class)"
  'CategoryC0_s = (cls_S).

interpretation
  "carrier (class structure)"
  'SetCAR X = (cls_sc X).

interpretation
  "equivalence (class structure)"
  'Equivalent X x1 x2 = (cls_se X x1 x2).

interpretation
  "negated equivalence (class structure)"
  'NotEquivalent X x1 x2 = (negation (cls_se X x1 x2)).

interpretation
  "negated equivalence alternative (class structure)"
  'NegEquivalent X x1 x2 = (negation (cls_se X x1 x2)).
