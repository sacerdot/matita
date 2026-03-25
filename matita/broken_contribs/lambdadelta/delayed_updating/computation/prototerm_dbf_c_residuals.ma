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

include "delayed_updating/reduction/prototerm_dbf_residuals.ma".
include "delayed_updating/computation/trace.ma".

(* CUMULATED RESIDUALS OF A SUBSET OF DBF-REDEX POINTERS ********************)

(* Note: residuals of u with respect to a trace rs *)
rec definition term_dbfrs (rs) (u) on rs: 𝒫❨ℙ❩ ≝
match rs with
[ list_empty      ⇒ u
| list_lcons r rs ⇒ term_dbfrs rs (u /𝐝𝐛𝐟 r)
].

interpretation
  "cumulated residuals of a subset of dbf-redex pointers (subset of paths)"
  'SlashDBF u rs = (term_dbfrs rs u).

(* Basic constructions ******************************************************)

lemma term_dbfrs_empty (u):
      u = u /𝐝𝐛𝐟 ⓔ.
//
qed.

lemma term_dbfrs_lcons (u) (rs) (r):
      (u /𝐝𝐛𝐟 r) /𝐝𝐛𝐟 rs = u /𝐝𝐛𝐟 (r⨮rs).
//
qed.

lemma term_dbfrs_append (ss) (rs) (u):
      (u /𝐝𝐛𝐟 rs) /𝐝𝐛𝐟 ss = u /𝐝𝐛𝐟 (rs⨁ss).
#ss #rs elim rs -rs //
qed.

lemma term_dbfrs_rcons (u) (rs) (s):
      (u /𝐝𝐛𝐟 rs) /𝐝𝐛𝐟 s = u /𝐝𝐛𝐟 (rs⨭s).
//
qed.
