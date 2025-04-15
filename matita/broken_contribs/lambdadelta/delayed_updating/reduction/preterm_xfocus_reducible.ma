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

include "delayed_updating/reduction/preterm_reducible.ma".
include "delayed_updating/reduction/prototerm_xfocus_reducible.ma".

(* BALANCED REDUCTION FOCUS *************************************************)

(* Destructions with xprc and preterm ***************************************)

lemma ol_des_clear_brxf_xprc_bi (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t ϵ 𝐓 → r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      ⓪𝐅❨p1,b1,q1❩ ≬ ⓪𝐅❨p2,b2,q2❩ → r1 = r2.
#t #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #Ht #Hr1 #Hr2 #H0
elim (ol_des_clear_brxf_xprc_bi_le … Hr1 Hr2 H0) -H0 #Hr
/3 width=12 by path_le_des_xprc_bi, sym_eq/
qed-.

(* Inversions with xprc and preterm *****************************************)

lemma neq_inv_xprc_bi_brxf (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t ϵ 𝐓 → r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      r1 ⧸= r2 → (𝐅❨p1,b1,q1❩ ⧸≬ 𝐅❨p2,b2,q2❩).
/4 width=13 by ol_des_clear_brxf_xprc_bi, ol_clear_bi/
qed-.
