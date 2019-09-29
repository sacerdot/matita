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

include "static_2/s_computation/fqus_fqup.ma".
include "basic_2/dynamic/cnv_drops.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Properties with supclosure ***********************************************)

(* Basic_2A1: uses: snv_fqu_conf *)
lemma cnv_fqu_conf (h) (a):
      ∀G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂ ⦃G2,L2,T2⦄ →
      ⦃G1,L1⦄ ⊢ T1 ![h,a] → ⦃G2,L2⦄ ⊢ T2 ![h,a].
#h #a #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I1 #G1 #L1 #V1 #H
  elim (cnv_inv_zero … H) -H #I2 #L2 #V2 #HV2 #H destruct //
| * [ #p #I1 | * ] #G1 #L1 #V1 #T1 #H
  [ elim (cnv_inv_bind … H) -H //
  | elim (cnv_inv_appl … H) -H //
  | elim (cnv_inv_cast … H) -H //
  ]
| #p #I1 #G1 #L1 #V1 #T1 #_ #H
  elim (cnv_inv_bind … H) -H //
| #p #I1 #G1 #L1 #V1 #T1 #H destruct
| * #G1 #L1 #V1 #T1 #H
  [ elim (cnv_inv_appl … H) -H //
  | elim (cnv_inv_cast … H) -H //
  ]
| #I1 #G1 #L1 #T1 #U1 #HTU1 #HU 
  /4 width=7 by cnv_inv_lifts, drops_refl, drops_drop/
]
qed-.

(* Basic_2A1: uses: snv_fquq_conf *)
lemma cnv_fquq_conf (h) (a):
      ∀G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂⸮ ⦃G2,L2,T2⦄ →
      ⦃G1,L1⦄ ⊢ T1 ![h,a] → ⦃G2,L2⦄ ⊢ T2 ![h,a].
#h #a #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -H [|*]
/2 width=5 by cnv_fqu_conf/
qed-.

(* Basic_2A1: uses: snv_fqup_conf *)
lemma cnv_fqup_conf (h) (a):
      ∀G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂+ ⦃G2,L2,T2⦄ →
      ⦃G1,L1⦄ ⊢ T1 ![h,a] → ⦃G2,L2⦄ ⊢ T2 ![h,a].
#h #a #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
/3 width=5 by fqup_strap1, cnv_fqu_conf/
qed-.

(* Basic_2A1: uses: snv_fqus_conf *)
lemma cnv_fqus_conf (h) (a):
      ∀G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂* ⦃G2,L2,T2⦄ →
      ⦃G1,L1⦄ ⊢ T1 ![h,a] → ⦃G2,L2⦄ ⊢ T2 ![h,a].
#h #a #G1 #G2 #L1 #L2 #T1 #T2 #H elim (fqus_inv_fqup … H) -H [|*]
/2 width=5 by cnv_fqup_conf/
qed-.
