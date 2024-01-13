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

include "ground/xoa/sig_1_1_props.ma".
include "ground/arith/pnat_le.ma".
include "ground/relocation/fb/fbr_dapp.ma".

(* INVERSE OF FINITE RELOCATION MAPS WITH BOOLEANS **************************)

record ibfr_type: Type[0] ≝
  { imap: ℕ⁺ → ℕ⁺
  ; dmap: 𝔽𝔹
  }
.

record ibfr_posts (z): Prop ≝
  { ibfr_post_id (p): p = imap z ((dmap z)＠⧣❨p❩)
  ; ibfr_post_di (p): p ≤ (dmap z)＠⧣❨imap z p❩
  }
.

definition ifbr_map: Type[0] ≝
           Σz.(ibfr_posts z).

definition ifbr_map_id (g) ≝
           ibfr_post_id (sig_a ? ? g) (sig_d ? ? g).

definition ifbr_map_di (g) ≝
           ibfr_post_di (sig_a ? ? g) (sig_d ? ? g).
