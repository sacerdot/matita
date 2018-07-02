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

include "static_2/relocation/drops_lex.ma".
include "basic_2/rt_transition/cpx_drops.ma".
include "basic_2/rt_transition/lpx.ma".

(* UNBOUND PARALLEL RT-TRANSITION FOR FULL LOCAL ENVIRONMENTS ***************)

(* Properties with generic slicing for local environments *******************)

(* Basic_2A1: was: drop_lpx_trans *)
lemma drops_lpx_trans (h) (G): dedropable_sn (cpx h G).
/3 width=6 by lex_liftable_dedropable_sn, cpx_lifts_sn/ qed-.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_2A1: was: lpx_drop_conf *)
lemma lpx_drops_conf (h) (G): dropable_sn (cpx h G).
/2 width=3 by lex_dropable_sn/ qed-.

(* Basic_2A1: was: lpx_drop_trans_O1 *)
lemma lpx_drops_trans (h) (G): dropable_dx (cpx h G).
/2 width=3 by lex_dropable_dx/ qed-.
