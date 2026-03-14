(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/classes/function_const_struct.ma".
include "convergence/directions/direction_struct_center.ma".
include "convergence/directions/direction.ma".
include "convergence/limits/limit_struct.ma".

(* LIMIT ********************************************************************)

(* Properties with fun_const_s **********************************************)

lemma limit_const (X) (Y) (D:𝔻 X) (C:𝔻𝗌 Y) (c):
      c ϵ 𝗖𝘁𝗿 C → 𝗹𝗶𝗺[D] 𝗞𝗌 c ≘ C.
#X #Y #D #C #c #H0
@mk_limit_alt #v #Hv
elim (subsets_inh_inv_in … @ dir_i … D) #u #Hu
@(ex2_intro … Hu)
#x #_ <fun_const_s_appl
/2 width=1 by dir_ctr_le/
qed.

lemma limit_inv_const (X) (Y) (D:𝔻 X) (C:𝔻𝗌 Y) (c):
      (𝗹𝗶𝗺[D] 𝗞𝗌 c ≘ C) → c ϵ 𝗖𝘁𝗿 C.
#X #Y #D #C #c #H0
@dir_ctr_in #v #Hv
elim (limit_inv_alt … H0 … Hv) -H0 #u #Hu #H0
elim (subsets_inh_inv_in … @ dir_d … Hu) // #x #Hx
>(fun_const_s_appl … x c)
/2 width=1 by/
qed-.
