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

include "ground_2/notation/functions/basic_2.ma".
include "ground_2/relocation/rtmap_at.ma".

(* RELOCATION MAP ***********************************************************)

definition basic: nat → nat → rtmap ≝ λm,n. ⫯*[m] 𝐔❨n❩.

interpretation "basic relocation (rtmap)"
   'Basic m n = (basic m n).

(* Prioerties with application **********************************************)

lemma at_basic_lt: ∀m,n,i. i < m → @❪i, 𝐁❨m,n❩❫ ≘ i.
#m elim m -m [ #n #i #H elim (lt_zero_false … H) ]
#m #IH #n * [ /2 width=2 by refl, at_refl/ ]
#i #H lapply (lt_S_S_to_lt … H) -H /3 width=7 by refl, at_push/
qed.

lemma at_basic_ge: ∀m,n,i. m ≤ i → @❪i, 𝐁❨m,n❩❫ ≘ n+i.
#m elim m -m //
#m #IH #n #j #H
elim (le_inv_S1 … H) -H #i #Hmi #H destruct
/3 width=7 by refl, at_push/
qed.

(* Inversion lemmas with application ****************************************)

lemma at_basic_inv_lt: ∀m,n,i,j. i < m → @❪i, 𝐁❨m,n❩❫ ≘ j → i = j.
/3 width=4 by at_basic_lt, at_mono/ qed-.

lemma at_basic_inv_ge: ∀m,n,i,j. m ≤ i → @❪i, 𝐁❨m,n❩❫ ≘ j → n+i = j.
/3 width=4 by at_basic_ge, at_mono/ qed-.
