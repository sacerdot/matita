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

include "basic_1/csubv/defs.ma".

let rec csubv_ind (P: (C \to (C \to Prop))) (f: (\forall (n: nat).(P (CSort 
n) (CSort n)))) (f0: (\forall (c1: C).(\forall (c2: C).((csubv c1 c2) \to ((P 
c1 c2) \to (\forall (v1: T).(\forall (v2: T).(P (CHead c1 (Bind Void) v1) 
(CHead c2 (Bind Void) v2))))))))) (f1: (\forall (c1: C).(\forall (c2: 
C).((csubv c1 c2) \to ((P c1 c2) \to (\forall (b1: B).((not (eq B b1 Void)) 
\to (\forall (b2: B).(\forall (v1: T).(\forall (v2: T).(P (CHead c1 (Bind b1) 
v1) (CHead c2 (Bind b2) v2)))))))))))) (f2: (\forall (c1: C).(\forall (c2: 
C).((csubv c1 c2) \to ((P c1 c2) \to (\forall (f2: F).(\forall (f3: 
F).(\forall (v1: T).(\forall (v2: T).(P (CHead c1 (Flat f2) v1) (CHead c2 
(Flat f3) v2))))))))))) (c: C) (c0: C) (c1: csubv c c0) on c1: P c c0 \def 
match c1 with [(csubv_sort n) \Rightarrow (f n) | (csubv_void c2 c3 c4 v1 v2) 
\Rightarrow (let TMP_3 \def ((csubv_ind P f f0 f1 f2) c2 c3 c4) in (f0 c2 c3 
c4 TMP_3 v1 v2)) | (csubv_bind c2 c3 c4 b1 n b2 v1 v2) \Rightarrow (let TMP_2 
\def ((csubv_ind P f f0 f1 f2) c2 c3 c4) in (f1 c2 c3 c4 TMP_2 b1 n b2 v1 
v2)) | (csubv_flat c2 c3 c4 f3 f4 v1 v2) \Rightarrow (let TMP_1 \def 
((csubv_ind P f f0 f1 f2) c2 c3 c4) in (f2 c2 c3 c4 TMP_1 f3 f4 v1 v2))].

