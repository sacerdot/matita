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
include "basic_2/rt_transition/cpm_drops.ma".
include "basic_2/rt_transition/lpr.ma".

(* PARALLEL R-TRANSITION FOR FULL LOCAL ENVIRONMENTS ************************)

(* Properties with generic slicing for local environments *******************)

(* Basic_2A1: was: drop_lpr_trans *)
lemma drops_lpr_trans (h) (G): dedropable_sn (λL. cpm h G L 0).
/3 width=6 by lex_liftable_dedropable_sn, cpm_lifts_sn/ qed-.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_1: includes: wcpr0_drop *)
(* Basic_2A1: was: lpr_drop_conf *)
lemma lpr_drops_conf (h) (G): dropable_sn (λL. cpm h G L 0).
/2 width=3 by lex_dropable_sn/ qed-.

(* Basic_1: includes: wcpr0_drop_back *)
(* Basic_2A1: was: lpr_drop_trans_O1 *)
lemma lpr_drops_trans (h) (G): dropable_dx (λL. cpm h G L 0).
/2 width=3 by lex_dropable_dx/ qed-.
