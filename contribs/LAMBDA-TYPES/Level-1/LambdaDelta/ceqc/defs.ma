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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/ceqc/defs".

include "sc3/defs.ma".

inductive csubc (g:G): C \to (C \to Prop) \def
| csubc_sort: \forall (n: nat).(csubc g (CSort n) (CSort n))
| csubc_head: \forall (c1: C).(\forall (c2: C).((csubc g c1 c2) \to (\forall 
(k: K).(\forall (v: T).(csubc g (CHead c1 k v) (CHead c2 k v))))))
| csubc_abst: \forall (c1: C).(\forall (c2: C).((csubc g c1 c2) \to (\forall 
(v: T).(\forall (a: A).((sc3 g (asucc g a) c1 v) \to (\forall (w: T).((sc3 g 
a c2 w) \to (csubc g (CHead c1 (Bind Abst) v) (CHead c2 (Bind Abbr) 
w))))))))).

definition ceqc:
 G \to (C \to (C \to Prop))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (c2: C).(or (csubc g c1 c2) (csubc 
g c2 c1)))).

