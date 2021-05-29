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

include "ground/relocation/gr_ist_isi.ma".
include "ground/relocation/gr_after_ist.ma".

(* RELATIONAL COMPOSITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Forward lemmas on istot and isid **************************************************)

(*** after_fwd_isid_sn *)
lemma gr_after_des_ist_eq_sn:
      ∀f2,f1,f. 𝐓❪f❫ → f2 ⊚ f1 ≘ f → f1 ≡ f → 𝐈❪f2❫.
#f2 #f1 #f #H #Hf elim (gr_after_inv_ist … Hf H) -H
#Hf2 #Hf1 #H @gr_isi_pat_total // -Hf2
#i2 #i #Hf2 elim (Hf1 i2) -Hf1
#i0 #Hf1 lapply (gr_pat_increasing … Hf1)
#Hi20 lapply (gr_after_des_pat_sn … i0 … Hf1 … Hf) -Hf
/3 width=7 by gr_pat_eq_repl_back, gr_pat_mono, gr_pat_id_le/
qed-.

(*** after_fwd_isid_dx *)
lemma gr_after_des_ist_eq_dx:
      ∀f2,f1,f.  𝐓❪f❫ → f2 ⊚ f1 ≘ f → f2 ≡ f → 𝐈❪f1❫.
#f2 #f1 #f #H #Hf elim (gr_after_inv_ist … Hf H) -H
#Hf2 #Hf1 #H2 @gr_isi_pat_total // -Hf1
#i1 #i2 #Hi12 elim (gr_after_des_ist_pat … Hi12 … Hf) -f1
/3 width=8 by gr_pat_inj, gr_pat_eq_repl_back/
qed-.
