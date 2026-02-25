(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/domains/domain_posts.ma".
include "convergence/notation/functions/category_d0_0.ma".

(* ABSTRACT DOMAIN **********************************************************)

(* Object *******************************************************************)

record domain: Type[1] ≝
{ dom_S: 𝔻𝟬𝗌
; dom_P: 𝔻𝟬𝗽❨dom_S❩
}.

interpretation
  "domain (category)"
  'CategoryD0 = (domain).

coercion dom_S.

coercion dom_P.
