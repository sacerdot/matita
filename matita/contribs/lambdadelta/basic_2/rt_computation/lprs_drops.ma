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

include "basic_2/relocation/drops_lex.ma".
include "basic_2/rt_computation/cpms_drops.ma".

(* PARALLEL R-COMPUTATION FOR FULL LOCAL ENVIRONMENTS ***********************)

(* Properties with generic slicing for local environments *******************)

(* Basic_2A1: was: drop_lprs_trans *)
lemma drops_lprs_trans (h) (G): dedropable_sn (λL.cpms h G L 0).
/3 width=6 by lex_liftable_dedropable_sn, cpms_lifts_sn/ qed-.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_2A1: was: lprs_drop_conf *)
lemma lprs_drops_conf (h) (G): dropable_sn (λL.cpms h G L 0).
/2 width=3 by lex_dropable_sn/ qed-.

(* Basic_2A1: was: lprs_drop_trans_O1 *)
lemma lprs_drops_trans (h) (G): dropable_dx (λL.cpms h G L 0).
/2 width=3 by lex_dropable_dx/ qed-.
