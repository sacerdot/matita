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

include "ground/subsets/subset_ol.ma".
include "delayed_updating/syntax/prototerm_constructors.ma".
include "delayed_updating/syntax/prototerm_irefs.ma".

(* SUBSET OF INNER REFERENCES ***********************************************)

(* Constructions with prototerm_constructors ********************************)

lemma pirc_mk_iref (t) (p) (n):
      t ≬ 𝐏 → ⓪p ϵ 𝐈❨p●𝛕n.t❩.
#t #p #n * #q #H1q #H2q
/4 width=4 by in_comp_pirc, pt_append_in/
qed.
