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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/csubt/fwd".

include "csubt/defs.ma".

axiom csubt_gen_abbr:
 \forall (g: G).(\forall (e1: C).(\forall (c2: C).(\forall (v: T).((csubt g 
(CHead e1 (Bind Abbr) v) c2) \to (ex2 C (\lambda (e2: C).(eq C c2 (CHead e2 
(Bind Abbr) v))) (\lambda (e2: C).(csubt g e1 e2)))))))
.

axiom csubt_gen_abst:
 \forall (g: G).(\forall (e1: C).(\forall (c2: C).(\forall (v1: T).((csubt g 
(CHead e1 (Bind Abst) v1) c2) \to (or (ex2 C (\lambda (e2: C).(eq C c2 (CHead 
e2 (Bind Abst) v1))) (\lambda (e2: C).(csubt g e1 e2))) (ex3_2 C T (\lambda 
(e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csubt g e1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g 
e2 v2 v1)))))))))
.

axiom csubt_gen_bind:
 \forall (g: G).(\forall (b1: B).(\forall (e1: C).(\forall (c2: C).(\forall 
(v1: T).((csubt g (CHead e1 (Bind b1) v1) c2) \to (ex2_3 B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C c2 (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csubt g e1 e2))))))))))
.

