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

include "basic_1/csubt/defs.ma".

include "basic_1/C/fwd.ma".

theorem csubt_refl:
 \forall (g: G).(\forall (c: C).(csubt g c c))
\def
 \lambda (g: G).(\lambda (c: C).(let TMP_1 \def (\lambda (c0: C).(csubt g c0 
c0)) in (let TMP_2 \def (\lambda (n: nat).(csubt_sort g n)) in (let TMP_3 
\def (\lambda (c0: C).(\lambda (H: (csubt g c0 c0)).(\lambda (k: K).(\lambda 
(t: T).(csubt_head g c0 c0 H k t))))) in (C_ind TMP_1 TMP_2 TMP_3 c))))).

