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

include "ground/subsets/subset_ol_le.ma".
include "delayed_updating/reduction/preterm_xfocus_reducible.ma".
include "delayed_updating/reduction/prototerm_delayed_xfocus.ma".

(* BALANCED REDUCTION DELAYED SUBREDUCT *************************************)

(* Destructions with brxf and xprc and preterm ******************************)

lemma ol_des_clear_brxf_brd_xprc (t) (t0) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t ϵ 𝐓 → r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      ⓪𝐅❨p1,b1,q1❩ ≬ ⓪𝐃❨t0,p2,b2,q2,n2❩ → r1 = r2.
#t #t0 #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #Ht #Hr1 #Hr2 #H0
lapply (subset_ol_le_repl … H0 ????) -H0
[ @brd_brxf | skip | @subset_le_refl | skip ] #H0
/2 width=13 by ol_des_clear_brxf_xprc_bi/
qed-.

(* Inversions with brxf and xprc and preterm ********************************)

lemma neq_inv_xprc_bi_brxf_brd (t) (t0) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t ϵ 𝐓 → r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      r1 ⧸= r2 → (𝐅❨p1,b1,q1❩ ⧸≬ 𝐃❨t0,p2,b2,q2,n2❩).
/4 width=14 by ol_des_clear_brxf_brd_xprc, clear_ol/
qed-.
