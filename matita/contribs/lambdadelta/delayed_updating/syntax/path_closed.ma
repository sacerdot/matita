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
include "delayed_updating/notation/functions/class_c_1.ma".
include "ground/lib/subset.ma".

include "delayed_updating/syntax/path_depth.ma".
include "delayed_updating/syntax/path_height.ma".

(* CLOSED CONDITION FOR PATH ************************************************)

axiom pcc: relation2 nat path.

interpretation
  "closed condition (path)"
  'ClassC n = (pcc n).

(* Basic destructions *******************************************************)

axiom pcc_empty:
      (𝐞) ϵ 𝐂❨𝟎❩.

axiom pcc_d (p) (d) (n:pnat):
      p ϵ 𝐂❨d+n❩ → p◖𝗱n ϵ 𝐂❨d❩.

axiom pcc_L (p) (d):
      p ϵ 𝐂❨d❩ → p◖𝗟 ϵ 𝐂❨↑d❩.

axiom pcc_A (p) (d):
      p ϵ 𝐂❨d❩ → p◖𝗔 ϵ 𝐂❨d❩.

axiom pcc_S (p) (d):
      p ϵ 𝐂❨d❩ → p◖𝗦 ϵ 𝐂❨d❩.

axiom pcc_des_gen (p) (d):
      p ϵ 𝐂❨d❩ → d + ♯p = ❘p❘.
