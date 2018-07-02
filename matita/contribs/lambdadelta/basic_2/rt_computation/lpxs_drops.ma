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
include "basic_2/rt_computation/cpxs_drops.ma".

(* UNBOUND PARALLEL RT-COMPUTATION FOR FULL LOCAL ENVIRONMENTS **************)

(* Properties with generic slicing for local environments *******************)

(* Basic_2A1: was: drop_lpxs_trans *)
lemma drops_lpxs_trans (h) (G): dedropable_sn (cpxs h G).
/3 width=6 by lex_liftable_dedropable_sn, cpxs_lifts_sn/ qed-.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_2A1: was: lpxs_drop_conf *)
lemma lpxs_drops_conf (h) (G): dropable_sn (cpxs h G).
/2 width=3 by lex_dropable_sn/ qed-.

(* Basic_2A1: was: lpxs_drop_trans_O1 *)
lemma lpxs_drops_trans (h) (G): dropable_dx (cpxs h G).
/2 width=3 by lex_dropable_dx/ qed-.
