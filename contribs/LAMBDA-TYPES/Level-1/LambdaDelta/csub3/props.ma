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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/csub3/props".

include "csub3/defs.ma".

theorem csub3_refl:
 \forall (g: G).(\forall (c: C).(csub3 g c c))
\def
 \lambda (g: G).(\lambda (c: C).(C_ind (\lambda (c0: C).(csub3 g c0 c0)) 
(\lambda (n: nat).(csub3_sort g n)) (\lambda (c0: C).(\lambda (H: (csub3 g c0 
c0)).(\lambda (k: K).(\lambda (t: T).(csub3_head g c0 c0 H k t))))) c)).

