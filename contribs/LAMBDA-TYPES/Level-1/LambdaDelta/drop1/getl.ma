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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/drop1/getl".

include "drop1/defs.ma".

include "getl/defs.ma".

axiom drop1_getl_trans:
 \forall (hds: PList).(\forall (c1: C).(\forall (c2: C).((drop1 hds c2 c1) 
\to (\forall (b: B).(\forall (e1: C).(\forall (v: T).(\forall (i: nat).((getl 
i c1 (CHead e1 (Bind b) v)) \to (ex C (\lambda (e2: C).(getl (trans hds i) c2 
(CHead e2 (Bind b) (ctrans hds i v)))))))))))))
.

