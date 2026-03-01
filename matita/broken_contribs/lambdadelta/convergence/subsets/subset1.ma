(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/lib/relations.ma".
include "convergence/notation/relations/epsilon_sup_1_3.ma".
include "convergence/notation/relations/neg_epsilon_sup_1_3.ma".

(* BIG SUBSETS **************************************************************)

definition predicate1 (A:Type[1]): Type[1] ≝ A → Prop.

definition subset1_in (A): predicate1 A → predicate1 A ≝
           λu.u.

interpretation
  "membership (big subset)"
  'EpsilonSup1 A a u = (subset1_in A u a).

interpretation
  "negated membership (big subset)"
  'NegEpsilonSup1 A a u = (negation (subset1_in A u a)).
