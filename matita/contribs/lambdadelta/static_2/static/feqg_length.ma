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

include "static_2/static/reqg_length.ma".
include "static_2/static/feqg.ma".

(* GENERIC EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES *********************)

(* Forward lemmas with length for local environments ************************)

lemma feqg_fwd_length (S) (G1) (G2) (L1) (L2) (T1) (T2):
      ❪G1,L1,T1❫ ≛[S] ❪G2,L2,T2❫ → |L1| = |L2|.
/3 width=6 by feqg_fwd_reqg_sn, reqg_fwd_length/ qed-.
