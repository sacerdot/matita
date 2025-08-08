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
      ⓪𝐅❨p1,b1,q1,n1❩ ≬ ⓪𝐅❨p2,b2,q2,n2❩ → r1 = r2.
#t #r1 #r2 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #Ht #Hr1 #Hr2 #H0
elim (ol_des_clear_brxf_xprc_bi_le … Hr1 Hr2 H0) -H0 #Hr
/3 width=12 by path_le_des_xprc_bi, sym_eq/
qed-.

(* Inversions with xprc and preterm *****************************************)

lemma neq_inv_xprc_bi_brxf (t) (r1) (r2) (p1) (p2) (b1) (b2) (q1) (q2) (n1) (n2):
      t ϵ 𝐓 → r1 ϵ 𝐑❨t,p1,b1,q1,n1❩ → r2 ϵ 𝐑❨t,p2,b2,q2,n2❩ →
      r1 ⧸= r2 → (𝐅❨p1,b1,q1,n1❩ ⧸≬ 𝐅❨p2,b2,q2,n2❩).
/4 width=13 by ol_des_clear_brxf_xprc_bi, term_ol_clear_bi/
qed-.

lemma preterm_nol_brxf (t1) (t2) (r) (x) (p1) (p2) (b1) (b2) (q1) (q2) (l) (n1) (n2):
      t1 ϵ 𝐓 →
      r ϵ 𝐑❨t1, p1, b1, q1, n1❩ →
      r●(x◖l) ϵ 𝐑❨t2, p2, b2, q2, n2❩ →
      t1 ⧸≬ 𝐅❨p2, b2, q2, n2❩.
#t1 #t2 #r #x #p1 #p2 #b1 #b2 #q1 #q2 #l #n1 #n2 #Ht1 #Hr #Hx
* #y #H1y #H2y
elim (term_in_slice_inv_gen … H2y) -H2y #z #H0 destruct
lapply (xprc_des_r … Hr) #H0 destruct
lapply (xprc_des_n … Hr) -Hr #Hr
lapply (xprc_des_r … Hx) -t2 #Hx
lapply (preterm_clear … Ht1) -Ht1 #Ht1
lapply (in_comp_term_clear … Hr) -Hr #Hr
lapply (in_comp_term_clear … H1y) -H1y
<path_clear_append >Hx <list_append_assoc #Hy -p2 -b2 -q2 -n2
lapply (term_complete_append … Ht1 Hr Hy) -t1 -p1 -b1 -q1 -n1 #H0
elim (eq_inv_list_empty_append … H0) -H0 #_ #H0 -z destruct
qed-.

(* Constructions with xprc and preterm **************************************)

(* Note: this uses term_root_L_post *)
lemma le_grafted_full_bi_brxf_dx (t) (r) (p) (b1) (b2) (q) (n1) (n2):
      t ϵ 𝐓 → r ϵ 𝐑❨t,p,b1,q,n1❩ → ⊗b2 ϵ 𝐁 →
      (⋔[𝐫❨p,b2,q,n2❩]t) ⊆ ⋔[𝐫❨p,b2,q,n2❩]𝐅❨p,b1,q,n1❩.
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
lapply (term_complete_append … Ht Hn1 Hy) -t #H0 destruct
@(subset_in_eq_repl_fwd ????? (grafted_brxf_full …)) -p -b2 -q -n1 //
qed-.
