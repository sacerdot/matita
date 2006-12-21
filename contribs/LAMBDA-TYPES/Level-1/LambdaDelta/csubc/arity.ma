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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/csubc/arity".

include "csubc/csuba.ma".

include "arity/defs.ma".

include "csuba/arity.ma".

theorem csubc_arity_conf:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((csubc g c1 c2) \to 
(\forall (t: T).(\forall (a: A).((arity g c1 t a) \to (arity g c2 t a)))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubc g c1 
c2)).(\lambda (t: T).(\lambda (a: A).(\lambda (H0: (arity g c1 t 
a)).(csuba_arity g c1 t a H0 c2 (csubc_csuba g c1 c2 H)))))))).

theorem csubc_arity_trans:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((csubc g c1 c2) \to 
(\forall (t: T).(\forall (a: A).((arity g c2 t a) \to (arity g c1 t a)))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubc g c1 
c2)).(\lambda (t: T).(\lambda (a: A).(\lambda (H0: (arity g c2 t 
a)).(csuba_arity_rev g c2 t a H0 c1 (csubc_csuba g c1 c2 H)))))))).

