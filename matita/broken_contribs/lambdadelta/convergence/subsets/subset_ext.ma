(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_ext.ma".
include "convergence/notation/functions/at_4.ma".

(* EXTENSIONS FOR SUBSETS ***************************************************)

interpretation
  "applied extended function of one argument (subset)"
  'At X Y f u = (subset_ext_f1 X Y f u).
