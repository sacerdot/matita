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

include "ground_1/plist/defs.ma".

theorem papp_ss:
 \forall (is1: PList).(\forall (is2: PList).(eq PList (papp (Ss is1) (Ss 
is2)) (Ss (papp is1 is2))))
\def
 \lambda (is1: PList).(let TMP_6 \def (\lambda (p: PList).(\forall (is2: 
PList).(let TMP_1 \def (Ss p) in (let TMP_2 \def (Ss is2) in (let TMP_3 \def 
(papp TMP_1 TMP_2) in (let TMP_4 \def (papp p is2) in (let TMP_5 \def (Ss 
TMP_4) in (eq PList TMP_3 TMP_5)))))))) in (let TMP_8 \def (\lambda (is2: 
PList).(let TMP_7 \def (Ss is2) in (refl_equal PList TMP_7))) in (let TMP_27 
\def (\lambda (n: nat).(\lambda (n0: nat).(\lambda (p: PList).(\lambda (H: 
((\forall (is2: PList).(eq PList (papp (Ss p) (Ss is2)) (Ss (papp p 
is2)))))).(\lambda (is2: PList).(let TMP_9 \def (papp p is2) in (let TMP_10 
\def (Ss TMP_9) in (let TMP_17 \def (\lambda (p0: PList).(let TMP_11 \def (S 
n0) in (let TMP_12 \def (PCons n TMP_11 p0) in (let TMP_13 \def (S n0) in 
(let TMP_14 \def (papp p is2) in (let TMP_15 \def (Ss TMP_14) in (let TMP_16 
\def (PCons n TMP_13 TMP_15) in (eq PList TMP_12 TMP_16)))))))) in (let 
TMP_18 \def (S n0) in (let TMP_19 \def (papp p is2) in (let TMP_20 \def (Ss 
TMP_19) in (let TMP_21 \def (PCons n TMP_18 TMP_20) in (let TMP_22 \def 
(refl_equal PList TMP_21) in (let TMP_23 \def (Ss p) in (let TMP_24 \def (Ss 
is2) in (let TMP_25 \def (papp TMP_23 TMP_24) in (let TMP_26 \def (H is2) in 
(eq_ind_r PList TMP_10 TMP_17 TMP_22 TMP_25 TMP_26)))))))))))))))))) in 
(PList_ind TMP_6 TMP_8 TMP_27 is1)))).

