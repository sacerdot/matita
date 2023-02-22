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

include "delayed_updating/unwind/unwind2_rmap.ma".
include "delayed_updating/syntax/path_guard.ma".
include "ground/relocation/nap.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Destructions with pgc ****************************************************)

lemma unwind2_rmap_push_guard (f) (p):
      p ϵ 𝐆 → ⫯⇂▶[⫯f]p = ▶[⫯f]p.
#f #p * //
qed-.

lemma nap_zero_unwind2_rmap_push_guard (f) (p):
      p ϵ 𝐆 → 𝟎 = ▶[⫯f]p＠§❨𝟎❩.
#f #p #Hp
<(unwind2_rmap_push_guard … Hp) -Hp //
qed-.
