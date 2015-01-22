(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

(* This file was automatically generated: do not edit *********************)

include "Ground-1/plist/defs.ma".

theorem papp_ss:
 \forall (is1: PList).(\forall (is2: PList).(eq PList (papp (Ss is1) (Ss 
is2)) (Ss (papp is1 is2))))
\def
 \lambda (is1: PList).(PList_ind (\lambda (p: PList).(\forall (is2: 
PList).(eq PList (papp (Ss p) (Ss is2)) (Ss (papp p is2))))) (\lambda (is2: 
PList).(refl_equal PList (Ss is2))) (\lambda (n: nat).(\lambda (n0: 
nat).(\lambda (p: PList).(\lambda (H: ((\forall (is2: PList).(eq PList (papp 
(Ss p) (Ss is2)) (Ss (papp p is2)))))).(\lambda (is2: PList).(eq_ind_r PList 
(Ss (papp p is2)) (\lambda (p0: PList).(eq PList (PCons n (S n0) p0) (PCons n 
(S n0) (Ss (papp p is2))))) (refl_equal PList (PCons n (S n0) (Ss (papp p 
is2)))) (papp (Ss p) (Ss is2)) (H is2))))))) is1).
(* COMMENTS
Initial nodes: 151
END *)

