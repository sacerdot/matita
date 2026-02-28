(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset.ma".
include "convergence/notation/functions/category_d0_s_0.ma".
include "convergence/notation/functions/set_car_1.ma".
include "convergence/notation/functions/set_dom_1.ma".
include "convergence/notation/relations/equivalent_s_3.ma".
include "convergence/notation/relations/not_equivalent_s_3.ma".
include "convergence/notation/relations/neg_equivalent_s_3.ma".

(* ABSTRACT DOMAIN **********************************************************)

(* Structure ****************************************************************)

record domain_structure: Type[1] ≝
{ dom_C:> Type[0]
; dom_D:> (𝒫❨dom_C❩)
; dom_E:  relation2 dom_C dom_C
}.

interpretation
  "structure (domain)"
  'CategoryD0_s = (domain_structure).

interpretation
  "carrier (domain structure)"
  'SetCAR X = (dom_C X).

interpretation
  "domain (domain structure)"
  'SetDOM X = (dom_D X).

interpretation
  "equivalence (domain structure)"
  'Equivalent_s X x1 x2 = (dom_E X x1 x2).

interpretation
  "negated equivalence (domain structure)"
  'NotEquivalent_s X x1 x2 = (negation (dom_E X x1 x2)).

interpretation
  "negated equivalence alternative (domain structure)"
  'NegEquivalent_s X x1 x2 = (negation (dom_E X x1 x2)).
