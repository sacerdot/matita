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

include "basic_1A/sn3/defs.ma".

include "basic_1A/arity/defs.ma".

include "basic_1A/drop1/defs.ma".

rec definition sc3 (g: G) (a: A) on a: C \to (T \to Prop) \def \lambda (c: 
C).(\lambda (t: T).(match a with [(ASort h n) \Rightarrow (land (arity g c t 
(ASort h n)) (sn3 c t)) | (AHead a1 a2) \Rightarrow (land (arity g c t (AHead 
a1 a2)) (\forall (d: C).(\forall (w: T).((sc3 g a1 d w) \to (\forall (is: 
PList).((drop1 is d c) \to (sc3 g a2 d (THead (Flat Appl) w (lift1 is 
t)))))))))])).

