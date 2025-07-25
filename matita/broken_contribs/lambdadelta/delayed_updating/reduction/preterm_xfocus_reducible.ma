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

include "delayed_updating/unwind/preterm_balanced_structure.ma".
include "delayed_updating/reduction/preterm_reducible.ma".
include "delayed_updating/reduction/prototerm_xfocus_eq.ma".
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
/4 width=13 by ol_des_clear_brxf_xprc_bi, term_ol_clear_bi/
qed-.

(* Constructions with xprc and preterm **************************************)

(* Note: this uses term_root_L_post *)
lemma le_grafted_full_bi_brxf_dx (t) (r) (p) (b1) (b2) (q) (n1) (n2):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b1,q,n1❩ → ⊗b2 ϵ 𝐁 →
      (⋔[p●𝗔◗b2●𝗟◗q◖𝗱n2]t) ⊆ ⋔[p●𝗔◗b2●𝗟◗q◖𝗱n2]𝐅❨p,b1,q❩.
#t #r #p #b1 #b2 #q #n1 #n2 #Ht #Hr #Hb2 #y #Hy
lapply (xprc_des_b … Hr) #Hb1
lapply (xprc_des_n … Hr) -r #Hn1
lapply (term_grafted_inv_gen … Hy) -Hy #Hy
lapply (term_in_comp_structure_pbc_L_inj … Ht Hb1 Hb2 ??)
[ @(subset_in_eq_repl ??? Hy) // | @(subset_in_eq_repl ??? Hn1) // |3,4,5: skip ]
-Hb1 -Hb2 #H0 destruct
lapply (term_root_d_post … Ht … (𝗱n2) (⁤↑n1) ??)
[ /2 width=2 by term_in_comp_root/
| /2 width=2 by term_in_root/
| skip
] #H0 destruct
lapply (term_complete_post … Ht … Hy Hn1 ?) -t [ // ] #H0
<(eq_inv_list_append_dx_dx_refl … (sym_eq … H0)) -y
<path_append_pAbLq_15 >list_append_lcons_empty_sn
@(subset_in_eq_repl_fwd ????? (term_grafted_append …))
@(subset_in_eq_repl_fwd ????? (term_grafted_eq_repl …))
[2: @grafted_brxf_full |3: skip ]
/2 width=2 by pt_append_slice/
qed-.
