(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/classes/function_id_struct.ma".
include "convergence/directions/direction_struct_order.ma".
include "convergence/limits/limit_struct.ma".

(* LIMIT ********************************************************************)

(* Properties with the identity function ************************************)

lemma limit_id (X) (D:𝔻𝗌 X) (C:𝔻𝗌 X):
      C ⊑ D → 𝗹𝗶𝗺[D] 𝗜𝗌 ≘ C.
#X #D #C #H0
@mk_limit_alt #j
elim (H0 j) -H0 #i #Hij
@(ex_intro … (i))
#x #Hx <fun_id_s_appl
@Hij // (**) (* auto fails *)
qed.

lemma limit_inv_id (X) (D:𝔻𝗌 X) (C:𝔻𝗌 X):
      (𝗹𝗶𝗺[D] 𝗜𝗌 ≘ C) → C ⊑ D.
#X #D #C #H0 #j
elim (limit_inv_alt … H0 j) -H0 #i #H0
@(ex_intro … i) #x #Hx
>(fun_id_s_appl … X x)
/2 width=1 by/
qed-.
