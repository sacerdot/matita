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

include "delayed_updating/syntax/path_clear.ma".
include "delayed_updating/syntax/path_beta.ma".

(* PRE REDEX ****************************************************************)

(* Constructions with path_clear ********************************************)

lemma path_clear_beta (p) (b) (q) (n):
      (𝐫❨⓪p,⓪b,⓪q,𝟎❩) = ⓪𝐫❨p,b,q,n❩.
#p #b #q #n
<path_clear_d_dx <path_clear_append
<path_clear_L_dx <path_clear_append
<path_clear_A_dx //
qed.

lemma path_clear_pbeta (p) (b) (q):
      (𝐫❨⓪p,⓪b,⓪q❩) = ⓪𝐫❨p,b,q❩.
#p #b #q
<path_clear_append
<path_clear_L_dx <path_clear_append
<path_clear_A_dx //
qed.

lemma path_clear_beta_b (p) (b) (q) (n1) (n2):
      (⓪𝐫❨p,b,q,n1❩) = ⓪𝐫❨p,⓪b,q,n2❩.
//
qed.
