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

include "basic_1/sn3/defs.ma".

include "basic_1/arity/defs.ma".

include "basic_1/drop1/defs.ma".

let rec sc3 (g: G) (a: A) on a: C \to (T \to Prop) \def \lambda (c: 
C).(\lambda (t: T).(match a with [(ASort h n) \Rightarrow (let TMP_7 \def 
(ASort h n) in (let TMP_8 \def (arity g c t TMP_7) in (let TMP_9 \def (sn3 c 
t) in (land TMP_8 TMP_9)))) | (AHead a1 a2) \Rightarrow (let TMP_1 \def 
(AHead a1 a2) in (let TMP_2 \def (arity g c t TMP_1) in (let TMP_6 \def 
(\forall (d: C).(\forall (w: T).((sc3 g a1 d w) \to (\forall (is: 
PList).((drop1 is d c) \to (let TMP_3 \def (Flat Appl) in (let TMP_4 \def 
(lift1 is t) in (let TMP_5 \def (THead TMP_3 w TMP_4) in (sc3 g a2 d 
TMP_5))))))))) in (land TMP_2 TMP_6))))])).

