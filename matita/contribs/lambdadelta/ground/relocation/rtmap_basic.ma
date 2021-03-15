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

include "ground/notation/functions/basic_2.ma".
include "ground/relocation/rtmap_uni.ma".

(* RELOCATION MAP ***********************************************************)

definition basic: nat → nat → rtmap ≝ λm,n. ⫯*[m] 𝐔❨n❩.

interpretation "basic relocation (rtmap)"
   'Basic m n = (basic m n).

(* Basic properties *********************************************************)

lemma at_basic_succ_sn (m) (n): ⫯𝐁❨m,n❩ = 𝐁❨↑m,n❩.
#m #n >pushs_S //
qed.

lemma at_basic_zero_succ (n): ↑𝐁❨𝟎,n❩ = 𝐁❨𝟎,↑n❩.
#n >nexts_S //
qed.
