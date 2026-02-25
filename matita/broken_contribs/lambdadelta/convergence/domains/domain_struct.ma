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
include "convergence/notation/relations/neg_element_2.ma".

(* ABSTRACT DOMAIN **********************************************************)

(* Structure ****************************************************************)

record domain_structure: Type[1] ≝
{ dom_C: Type[0]
; dom_D: (𝒫❨dom_C❩)
; dom_E: relation2 dom_C dom_C
}.

interpretation
  "domain structure (category)"
  'CategoryD0_s = (domain_structure).

interpretation
  "carrier (domain structure)"
  'SetCAR D = (dom_C D).

interpretation
  "domain (domain structure)"
  'SetDOM D = (dom_D D).

interpretation
  "equivalence (domain structure)"
  'Equivalent_s D d1 d2 = (dom_E D d1 d2).

interpretation
  "negated equivalence (domain structure)"
  'NotEquivalent_s D d1 d2 = (negation (dom_E D d1 d2)).

interpretation
  "negated equivalence alternative (domain structure)"
  'NegEquivalent_s D d1 d2 = (negation (dom_E D d1 d2)).

coercion dom_C.

definition in_dom_D (D): predicate … ≝
           λd. d ϵ 𝗗𝗼𝗺❨D❩.

interpretation
  "membership (domain structure)"
  'mem d D = (in_dom_D D d).

interpretation
  "negated membership (domain structure)"
  'notmem d D = (negation (in_dom_D D d)).

interpretation
  "negated membership alternative (domain structure)"
  'NegElement d D = (negation (in_dom_D D d)).
