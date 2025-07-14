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

include "delayed_updating/syntax/preterm_clear.ma".
include "delayed_updating/reduction/prototerm_reducibles.ma".
include "delayed_updating/reduction/ibf_step.ma".

(* IMMEDIATE BALANCED FOCUSED REDUCTION *************************************)

(* Constructions with prc ***************************************************)

lemma ibfs_reducible (t1) (r):
      r ϵ 𝐑❨t1❩ → ∃t2. t1 ➡𝐢𝐛𝐟[r] t2.
#t1 #r * #p #b #q #n #Hr
lapply (xprc_des_n … Hr) #Hn
@ex_intro [| @(ibfs_mk … Hr) @subset_eq_refl ]
qed-.

(* Inversions with prc ******************************************************)

lemma ibfs_inv_reducuble (t1) (t2) (r):
      t1 ➡𝐢𝐛𝐟[r] t2 → r ϵ 𝐑❨t1❩.
#t1 #t2 #r * #p #b #q #n #Hr #_
/2 width=5 by prc_mk/
qed-.

(* Destructions with prc ****************************************************)

(* UPDATE *)

lemma ibfs_des_reducuble_neq (t1) (t2) (r) (s):
      t1 ϵ 𝐓 → t1 ➡𝐢𝐛𝐟[r] t2 →
      s ⧸= r → s ϵ 𝐑❨t1❩ → s ϵ 𝐑❨t2❩.
#t1 #t2 #r #s #Ht1 #Ht #Hr * #p #b #q #n * #H0 #Hb #Hq #Hn destruct
elim (ibfs_inv_reducuble … Ht) #p0 #b0 #q0 #n0 * #H0 #_ #_ #Hn0 destruct
@(prc_mk_old … Hq) [| // ] - Hb -Hq
@(ibfs_des_in_comp_neq … Ht) // -t2 #H0
lapply (term_slice_des_clear_bi … (𝐞) … Ht1 … H0) -H0
[ /2 width=2 by term_in_root_rcons/
| /2 width=1 by term_in_comp_root/
]
* #s #_ #Hs >Hs in Hn; #Hn
lapply (term_comp_append … Ht1 Hn0 Hn) -t1 #H0 destruct
<(list_append_lcons_sn) in Hs; <list_append_empty_sn #H0
elim (eq_inv_list_lcons_bi ????? H0) -H0 #_ #Hs -n -n0
/2 width=1 by/
qed-.
