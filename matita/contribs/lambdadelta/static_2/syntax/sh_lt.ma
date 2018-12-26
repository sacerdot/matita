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

include "static_2/syntax/sh_props.ma".

(* SORT HIERARCHY ***********************************************************)

(* strict monotonicity condition *)
record sh_lt (h): Prop ≝
{
  next_lt: ∀s. s < ⫯[h]s
}.

(* Basic properties *********************************************************)

lemma nexts_le (h): sh_lt h → ∀s,n. s ≤ (next h)^n s.
#h #Hh #s #n elim n -n [ // ] normalize #n #IH
lapply (next_lt … Hh ((next h)^n s)) #H
lapply (le_to_lt_to_lt … IH H) -IH -H /2 width=2 by lt_to_le/
qed.

lemma nexts_lt (h): sh_lt h → ∀s,n. s < (next h)^(↑n) s.
#h #Hh #s #n normalize
lapply (nexts_le … Hh s n) #H
@(le_to_lt_to_lt … H) /2 width=1 by next_lt/
qed.

axiom sh_lt_dec (h): sh_lt h → sh_decidable h.

axiom sh_lt_acyclic (h): sh_lt h → sh_acyclic h.