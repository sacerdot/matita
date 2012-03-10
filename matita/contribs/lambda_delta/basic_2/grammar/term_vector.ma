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

include "Ground_2/list.ma".
include "Basic_2/grammar/term.ma".

(* TERMS ********************************************************************)

let rec applv Vs T on Vs ≝
  match Vs with
  [ nil        ⇒ T
  | cons hd tl ⇒  ⓐhd. (applv tl T)
  ].

interpretation "application o vevtor (term)"
   'SnApplV Vs T = (applv Vs T).
