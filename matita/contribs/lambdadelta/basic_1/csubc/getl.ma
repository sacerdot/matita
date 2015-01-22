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

include "Basic-1/csubc/drop.ma".

include "Basic-1/csubc/clear.ma".

theorem csubc_getl_conf:
 \forall (g: G).(\forall (c1: C).(\forall (e1: C).(\forall (i: nat).((getl i 
c1 e1) \to (\forall (c2: C).((csubc g c1 c2) \to (ex2 C (\lambda (e2: 
C).(getl i c2 e2)) (\lambda (e2: C).(csubc g e1 e2)))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (e1: C).(\lambda (i: nat).(\lambda 
(H: (getl i c1 e1)).(\lambda (c2: C).(\lambda (H0: (csubc g c1 c2)).(let H1 
\def (getl_gen_all c1 e1 i H) in (ex2_ind C (\lambda (e: C).(drop i O c1 e)) 
(\lambda (e: C).(clear e e1)) (ex2 C (\lambda (e2: C).(getl i c2 e2)) 
(\lambda (e2: C).(csubc g e1 e2))) (\lambda (x: C).(\lambda (H2: (drop i O c1 
x)).(\lambda (H3: (clear x e1)).(let H_x \def (csubc_drop_conf_O g c1 x i H2 
c2 H0) in (let H4 \def H_x in (ex2_ind C (\lambda (e2: C).(drop i O c2 e2)) 
(\lambda (e2: C).(csubc g x e2)) (ex2 C (\lambda (e2: C).(getl i c2 e2)) 
(\lambda (e2: C).(csubc g e1 e2))) (\lambda (x0: C).(\lambda (H5: (drop i O 
c2 x0)).(\lambda (H6: (csubc g x x0)).(let H_x0 \def (csubc_clear_conf g x e1 
H3 x0 H6) in (let H7 \def H_x0 in (ex2_ind C (\lambda (e2: C).(clear x0 e2)) 
(\lambda (e2: C).(csubc g e1 e2)) (ex2 C (\lambda (e2: C).(getl i c2 e2)) 
(\lambda (e2: C).(csubc g e1 e2))) (\lambda (x1: C).(\lambda (H8: (clear x0 
x1)).(\lambda (H9: (csubc g e1 x1)).(ex_intro2 C (\lambda (e2: C).(getl i c2 
e2)) (\lambda (e2: C).(csubc g e1 e2)) x1 (getl_intro i c2 x1 x0 H5 H8) 
H9)))) H7)))))) H4)))))) H1)))))))).
(* COMMENTS
Initial nodes: 315
END *)

