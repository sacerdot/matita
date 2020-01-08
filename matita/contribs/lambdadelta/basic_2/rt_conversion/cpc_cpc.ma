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

include "basic_2/rt_conversion/cpc.ma".

(* CONTEXT-SENSITIVE PARALLEL R-CONVERSION FOR TERMS ************************)

(* Main properties **********************************************************)

theorem cpc_conf: ∀h,G,L,T0,T1,T2. ❪G,L❫ ⊢ T0 ⬌[h] T1 → ❪G,L❫ ⊢ T0 ⬌[h] T2 →
                  ∃∃T. ❪G,L❫ ⊢ T1 ⬌[h] T & ❪G,L❫ ⊢ T2 ⬌[h] T.
/3 width=3 by cpc_sym, ex2_intro/ qed-.
