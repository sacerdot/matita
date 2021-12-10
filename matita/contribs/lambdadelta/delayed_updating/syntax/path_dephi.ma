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

include "ground/relocation/tr_pap.ma".
include "delayed_updating/syntax/path.ma".

(* DEPHI FOR PATH ***********************************************************)

rec definition path_dephi (f) (p) on p ≝
match p with
[ list_empty     ⇒ 𝐞
| list_lcons l q ⇒
   match l with
   [ label_node_d n ⇒ 𝗱❨f@❨n❩❩;path_dephi f q
   | label_edge_L   ⇒ 𝗟;path_dephi (𝟏⨮f) q
   | label_edge_A   ⇒ 𝗔;path_dephi f q
   | label_edge_S   ⇒ 𝗦;path_dephi f q
   ]
].
