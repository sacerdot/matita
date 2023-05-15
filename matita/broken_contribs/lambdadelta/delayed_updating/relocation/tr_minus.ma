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

include "ground/arith/pnat_minus.ma".
include "ground/arith/nat_minus.ma".
include "ground/relocation/tr_map.ma".

(* RIGHT SUBTRACTION FOR TOTAL RELOCATION MAPS ******************************)

corec definition tr_minus: ℕ → tr_map → tr_map.
* [ #f @f ] #q * #p #f
@((p-q)⨮(tr_minus (ninj (↑q)-ninj p) f))
defined.

interpretation
  "right minus (total relocation maps)"
  'minus f n = (tr_minus n f).

(* Basic constructions ******************************************************)

lemma tr_minus_zero_dx (f):
      f = f - 𝟎 .
* #f #p <(stream_unfold … ((f⨮p)-𝟎)) //
qed.

lemma tr_minus_cons_inj (f) (p) (q):
      (p-q)⨮(f-(ninj (↑q)-ninj p)) = (p⨮f)-(ninj q).
#f #p #q <(stream_unfold … ((p⨮f)-(ninj q))) //
qed.
