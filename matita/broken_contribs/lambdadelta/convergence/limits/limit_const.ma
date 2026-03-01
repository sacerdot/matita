(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/classes/function_const_struct.ma".
include "convergence/directions/direction_center.ma".
include "convergence/limits/limit.ma".

(* LIMIT ********************************************************************)

(* Properties with the constant function ************************************)

lemma limit_const (X) (Y) (D:𝔻𝗌 X) (C:𝔻𝗌 Y) (c):
      c ϵ 𝗖𝘁𝗿 C → 𝗹𝗶𝗺[D] 𝗞𝗌 c ≘ C.
#X #Y #D #C #c #H0
@mk_limit_alt #j
@(ex_intro … (𝗶))
#x #_ <fun_const_s_appl
/2 width=1 by dir_ctr_le/
qed.

lemma limit_inv_const (X) (Y) (D:𝔻𝗌 X) (C:𝔻𝗌 Y) (c):
      (𝗹𝗶𝗺[D] 𝗞𝗌 c ≘ C) → c ϵ 𝗖𝘁𝗿 C.
#X #Y #D #C #c #H0
@dir_ctr_in #j
elim (limit_inv_alt … H0 j) -H0 #i #H0
>(fun_const_s_appl … (𝗱＠❨i❩) c)
/2 width=1 by subset_sigma_P/
qed-.
