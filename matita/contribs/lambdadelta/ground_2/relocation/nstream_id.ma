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

include "ground_2/notation/functions/identity_0.ma".
include "ground_2/relocation/rtmap_eq.ma".

(* RELOCATION N-STREAM ******************************************************)

corec definition id: rtmap ≝ ↑id.

interpretation "identity (nstream)"
   'Identity = (id).

(* Basic properties *********************************************************)

lemma id_rew: ↑𝐈𝐝 = 𝐈𝐝.
<(stream_rew … (𝐈𝐝)) in ⊢ (???%); normalize //
qed.

lemma id_eq_rew: ↑𝐈𝐝 ≗ 𝐈𝐝.
cases id_rew in ⊢ (??%); //
qed.
