(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/dir_ctr_s.ma".
include "convergence/nhoods/nhs.ma".
include "convergence/nhoods/nhs_dir_s.ma".

(* DIRECTION FOR NHOODS *****************************************************)

(* Constructions with dir_ctr ***********************************************)

lemma nhs_dir_ctr (X) (F:𝔽 X) (x:X):
      x ϵ 𝗖𝘁𝗿 𝝙𝗌[F]❨x❩.
/2 width=3 by nhs_pd/
qed.
