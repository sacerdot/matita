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
 \lambda (is1: PList).(let TMP_885 \def (\lambda (p: PList).(\forall (is2: 
PList).(let TMP_883 \def (Ss p) in (let TMP_882 \def (Ss is2) in (let TMP_884 
\def (papp TMP_883 TMP_882) in (let TMP_880 \def (papp p is2) in (let TMP_881 
\def (Ss TMP_880) in (eq PList TMP_884 TMP_881)))))))) in (let TMP_879 \def 
(\lambda (is2: PList).(let TMP_878 \def (Ss is2) in (refl_equal PList 
TMP_878))) in (let TMP_877 \def (\lambda (n: nat).(\lambda (n0: nat).(\lambda 
(p: PList).(\lambda (H: ((\forall (is2: PList).(eq PList (papp (Ss p) (Ss 
is2)) (Ss (papp p is2)))))).(\lambda (is2: PList).(let TMP_875 \def (papp p 
is2) in (let TMP_876 \def (Ss TMP_875) in (let TMP_874 \def (\lambda (p0: 
PList).(let TMP_872 \def (S n0) in (let TMP_873 \def (PCons n TMP_872 p0) in 
(let TMP_870 \def (S n0) in (let TMP_868 \def (papp p is2) in (let TMP_869 
\def (Ss TMP_868) in (let TMP_871 \def (PCons n TMP_870 TMP_869) in (eq PList 
TMP_873 TMP_871)))))))) in (let TMP_865 \def (S n0) in (let TMP_863 \def 
(papp p is2) in (let TMP_864 \def (Ss TMP_863) in (let TMP_866 \def (PCons n 
TMP_865 TMP_864) in (let TMP_867 \def (refl_equal PList TMP_866) in (let 
TMP_861 \def (Ss p) in (let TMP_860 \def (Ss is2) in (let TMP_862 \def (papp 
TMP_861 TMP_860) in (let TMP_859 \def (H is2) in (eq_ind_r PList TMP_876 
TMP_874 TMP_867 TMP_862 TMP_859)))))))))))))))))) in (PList_ind TMP_885 
TMP_879 TMP_877 is1)))).

