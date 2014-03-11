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

include "basic_2/reduction/cpx_leq.ma".
include "basic_2/computation/cpxs.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL COMPUTATION ON TERMS *****************)

(* Properties on equivalence for local environments *************************)

lemma leq_cpxs_trans: ∀h,g,G. lsub_trans … (cpxs h g G) (leq 0 (∞)).
/3 width=5 by leq_cpx_trans, LTC_lsub_trans/
qed-.
