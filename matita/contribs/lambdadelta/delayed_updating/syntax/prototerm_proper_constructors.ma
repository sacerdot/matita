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

include "delayed_updating/syntax/prototerm_proper.ma".
include "delayed_updating/syntax/prototerm_constructors.ma".

(* PROPER CONDITION FOR PROTOTERM *******************************************)

(* Constructions with prototerm constructors ********************************)

lemma ppc_iref (t) (n):
      (𝛕n.t) ϵ 𝐏.
#t #n #p * #q #Hq #H0 destruct //
qed.
