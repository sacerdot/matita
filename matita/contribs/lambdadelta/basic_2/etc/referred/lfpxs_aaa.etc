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

include "basic_2/rt_transition/lfpx_aaa.ma".
include "basic_2/rt_computation/lfpxs.ma".

(* UNBOUND PARALLEL RT-COMPUTATION FOR LOCAL ENV.S ON REFERRED ENTRIES ******)

(* Properties with atomic arity assignment on terms *************************)

(* Basic_2A1: uses: lpxs_aaa_conf *) 
lemma lfpxs_aaa_conf: ∀h,G,T. Conf3 … (λL. aaa G L T) (lfpxs h G T).
#h #G #T @TC_Conf3 @lfpx_aaa_conf (**) (* auto fails *)
qed-.
