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

include "Basic-1/csubc/csuba.ma".

theorem csubc_arity_conf:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((csubc g c1 c2) \to 
(\forall (t: T).(\forall (a: A).((arity g c1 t a) \to (arity g c2 t a)))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubc g c1 
c2)).(\lambda (t: T).(\lambda (a: A).(\lambda (H0: (arity g c1 t 
a)).(csuba_arity g c1 t a H0 c2 (csubc_csuba g c1 c2 H)))))))).
(* COMMENTS
Initial nodes: 51
END *)

theorem csubc_arity_trans:
 \forall (g: G).(\forall (c1: C).(\forall (c2: C).((csubc g c1 c2) \to 
((csubv c1 c2) \to (\forall (t: T).(\forall (a: A).((arity g c2 t a) \to 
(arity g c1 t a))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(\lambda (H: (csubc g c1 
c2)).(\lambda (H0: (csubv c1 c2)).(\lambda (t: T).(\lambda (a: A).(\lambda 
(H1: (arity g c2 t a)).(csuba_arity_rev g c2 t a H1 c1 (csubc_csuba g c1 c2 
H) H0)))))))).
(* COMMENTS
Initial nodes: 59
END *)

