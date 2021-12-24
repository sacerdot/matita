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

include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/circled_times_1.ma".

(* STRUCTURE FOR PATH *******************************************************)

rec definition path_structure (p) on p ≝
match p with
[ list_empty     ⇒ 𝐞
| list_lcons l q ⇒
   match l with
   [ label_node_d n ⇒ path_structure q
   | label_edge_L   ⇒ 𝗟;path_structure q
   | label_edge_A   ⇒ 𝗔;path_structure q
   | label_edge_S   ⇒ 𝗦;path_structure q
   ]
].

interpretation
  "structure (path)"
  'CircledTimes p = (path_structure p).
