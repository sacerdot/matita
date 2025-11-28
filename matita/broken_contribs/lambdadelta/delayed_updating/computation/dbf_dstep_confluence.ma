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

include "ground/xoa/ex_2_3.ma".
include "delayed_updating/computation/dbf_dsteps_le.ma".
include "delayed_updating/computation/dbf_step_confluence.ma".

(* DELAYED BALANCED FOCUSED REDUCTION IN A DEVELOPMENT **********************)

(* Main destructions with dbfdss ********************************************)

theorem dbf_dstep_conf (t0) (t1) (t2) (u0) (v0) (r1) (r2):
        t0 ϵ 𝐓 →
        t0 Ꟈ➡𝐝𝐛𝐟[u0, u0 /𝐝𝐛𝐟{t0} r1] t1 → t0 Ꟈ➡𝐝𝐛𝐟[v0, v0 /𝐝𝐛𝐟{t0} r2] t2 →
        ∃∃t,u,v. t1 Ꟈ➡*𝐝𝐛𝐟[v0 /𝐝𝐛𝐟{t0} r1, v] t & t2 Ꟈ➡*𝐝𝐛𝐟[u0 /𝐝𝐛𝐟{t0} r2, u] t.
#t0 #t1 #t2 #u0 #v0 #r1 #r2 #Ht0 #H01 #H02
elim (dbfds_inv_dbfr_dx … H01) -H01 #Hr1 #H01
elim (dbfds_inv_dbfr_dx … H02) -H02 #Hr2 #H02
elim (dbf_step_conf … Ht0 H01 H02) -Ht0 -H01 -H02 #tx #H1x #H2x
elim (dbfdss_subset_le_sx_conf … H1x (v0 /𝐝𝐛𝐟{t0} r1)) -H1x
[| /2 width=3 by term_dbfr_mk/ ] #v #H1x #_
elim (dbfdss_subset_le_sx_conf … H2x (u0 /𝐝𝐛𝐟{t0} r2)) -H2x
[| /2 width=3 by term_dbfr_mk/ ] #u #H2x #_
/2 width=5 by ex2_3_intro/
qed-.
