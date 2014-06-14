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

include "basic_2/static/aaa_ssta.ma".
include "basic_2/unfold/lsstas.ma".

(* NAT-ITERATED STATIC TYPE ASSIGNMENT FOR TERMS ****************************)

(* Properties on atomic arity assignment for terms **************************)

lemma aaa_lsstas_conf: ∀h,g,G,L,l. Conf3 … (aaa G L) (lsstas h g G L l).
/3 width=6 by aaa_ssta_conf, lstar_Conf3/ qed-.
