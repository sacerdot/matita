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

include "static_2/notation/relations/stareqsn_4.ma".
include "static_2/syntax/teqg_ext.ma".
include "static_2/static/rex.ma".

(* GENERIC EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ***********)

definition reqg (S): relation3 âŠ â
           rex (ceqg S).

interpretation
  "generic equivalence on selected entries (local environment)"
  'StarEqSn S f L1 L2 = (sex (ceqg_ext S) cfull f L1 L2).

interpretation
  "generic equivalence on referred entries (local environment)"
  'StarEqSn S T L1 L2 = (reqg S T L1 L2).

(* Basic properties ***********************************************************)

lemma frees_teqg_conf_seqg (S):
      âf,L1,T1. L1 âą đ+âšT1â© â f â âT2. T1 â[S] T2 â
      âL2. L1 â[S,f] L2 â L2 âą đ+âšT2â© â f.
#S #f #L1 #T1 #H elim H -f -L1 -T1
[ #f #L1 #s1 #Hf #X #H1 #L2 #_
  elim (teqg_inv_sort1 âŠ H1) -H1 #s2 #_ #H destruct
  /2 width=3 by frees_sort/
| #f #i #Hf #X #H1
  >(teqg_inv_lref1 âŠ H1) -X #Y #H2
  >(sex_inv_atom1 âŠ H2) -Y
  /2 width=1 by frees_atom/
| #f #I #L1 #V1 #_ #IH #X #H1
  >(teqg_inv_lref1 âŠ H1) -X #Y #H2
  elim (sex_inv_next1 âŠ H2) -H2 #Z #L2 #HL12 #HZ #H destruct
  elim (ext2_inv_pair_sn âŠ HZ) -HZ #V2 #HV12 #H destruct
  /3 width=1 by frees_pair/
| #f #I #L1 #Hf #X #H1
  >(teqg_inv_lref1 âŠ H1) -X #Y #H2
  elim (sex_inv_next1 âŠ H2) -H2 #Z #L2 #_ #HZ #H destruct
  >(ext2_inv_unit_sn âŠ HZ) -Z /2 width=1 by frees_unit/
| #f #I #L1 #i #_ #IH #X #H1
  >(teqg_inv_lref1 âŠ H1) -X #Y #H2
  elim (sex_inv_push1 âŠ H2) -H2 #J #L2 #HL12 #_ #H destruct
  /3 width=1 by frees_lref/
| #f #L1 #l #Hf #X #H1 #L2 #_
  >(teqg_inv_gref1 âŠ H1) -X /2 width=1 by frees_gref/
| #f1V #f1T #f1 #p #I #L1 #V1 #T1 #_ #_ #Hf1 #IHV #IHT #X #H1
  elim (teqg_inv_pair1 âŠ H1) -H1 #V2 #T2 #HV12 #HT12 #H1 #L2 #HL12 destruct
  /6 width=5 by frees_bind, sex_inv_tl, ext2_pair, sle_sex_trans, pr_sor_inv_sle_dx, pr_sor_inv_sle_sn/
| #f1V #f1T #f1 #I #L1 #V1 #T1 #_ #_ #Hf1 #IHV #IHT #X #H1
  elim (teqg_inv_pair1 âŠ H1) -H1 #V2 #T2 #HV12 #HT12 #H1 #L2 #HL12 destruct
  /5 width=5 by frees_flat, sle_sex_trans, pr_sor_inv_sle_dx, pr_sor_inv_sle_sn/
]
qed-.

lemma frees_teqg_conf (S):
      reflexive âŠ S â
      âf,L,T1. L âą đ+âšT1â© â f â
      âT2. T1 â[S] T2 â L âą đ+âšT2â© â f.
/5 width=6 by frees_teqg_conf_seqg, sex_refl, teqg_refl, ext2_refl/ qed-.

lemma frees_seqg_conf (S):
      reflexive âŠ S â
      âf,L1,T. L1 âą đ+âšTâ© â f â
      âL2. L1 â[S,f] L2 â L2 âą đ+âšTâ© â f.
/3 width=6 by frees_teqg_conf_seqg, teqg_refl/ qed-.

lemma teqg_rex_conf_sn (S) (R):
      reflexive âŠ S â
      s_r_confluent1 âŠ (ceqg S) (rex R).
#S #R #HS #L1 #T1 #T2 #HT12 #L2 *
/3 width=5 by frees_teqg_conf, ex2_intro/
qed-.

lemma teqg_rex_div (S) (R):
      reflexive âŠ S â symmetric âŠ S â
      âT1,T2. T1 â[S] T2 â
      âL1,L2. L1 âȘ€[R,T2] L2 â L1 âȘ€[R,T1] L2.
/3 width=5 by teqg_rex_conf_sn, teqg_sym/ qed-.

lemma teqg_reqg_conf_sn (S1) (S2):
      reflexive âŠ S1 â
      s_r_confluent1 âŠ (ceqg S1) (reqg S2).
/2 width=5 by teqg_rex_conf_sn/ qed-.

lemma teqg_reqg_div (S1) (S2):
      reflexive âŠ S1 â symmetric âŠ S1 â
      âT1,T2. T1 â[S1] T2 â
      âL1,L2. L1 â[S2,T2] L2 â L1 â[S2,T1] L2.
/2 width=6 by teqg_rex_div/ qed-.

lemma reqg_atom (S):
      âI. â â[S,âȘ[I]] â.
/2 width=1 by rex_atom/ qed.

lemma reqg_sort (S):
      âI1,I2,L1,L2,s.
      L1 â[S,âs] L2 â L1.â[I1] â[S,âs] L2.â[I2].
/2 width=1 by rex_sort/ qed.

lemma reqg_pair (S):
      âI,L1,L2,V1,V2.
      L1 â[S,V1] L2 â V1 â[S] V2 â L1.â[I]V1 â[S,#0] L2.â[I]V2.
/2 width=1 by rex_pair/ qed.

lemma reqg_unit (S):
      âf,I,L1,L2. đâšfâ© â L1 â[S,f] L2 â
      L1.â€[I] â[S,#0] L2.â€[I].
/2 width=3 by rex_unit/ qed.

lemma reqg_lref (S):
      âI1,I2,L1,L2,i.
      L1 â[S,#i] L2 â L1.â[I1] â[S,#âi] L2.â[I2].
/2 width=1 by rex_lref/ qed.

lemma reqg_gref (S):
      âI1,I2,L1,L2,l.
      L1 â[S,Â§l] L2 â L1.â[I1] â[S,Â§l] L2.â[I2].
/2 width=1 by rex_gref/ qed.

lemma reqg_bind_repl_dx (S):
      âI,I1,L1,L2.âT:term. L1.â[I] â[S,T] L2.â[I1] â
      âI2. I â[S] I2 â L1.â[I] â[S,T] L2.â[I2].
/2 width=2 by rex_bind_repl_dx/ qed-.

lemma reqg_co (S1) (S2):
      S1 â S2 â
      âT:term. âL1,L2. L1 â[S1,T] L2 â L1 â[S2,T] L2.
/3 width=3 by rex_co, teqg_co/ qed-.

(* Basic inversion lemmas ***************************************************)

lemma reqg_inv_atom_sn (S):
      âY2. âT:term. â â[S,T] Y2 â Y2 = â.
/2 width=3 by rex_inv_atom_sn/ qed-.

lemma reqg_inv_atom_dx (S):
      âY1. âT:term. Y1 â[S,T] â â Y1 = â.
/2 width=3 by rex_inv_atom_dx/ qed-.

lemma reqg_inv_zero (S):
      âY1,Y2. Y1 â[S,#0] Y2 â
      âšâš â§â§ Y1 = â & Y2 = â
       | ââI,L1,L2,V1,V2. L1 â[S,V1] L2 & V1 â[S] V2 & Y1 = L1.â[I]V1 & Y2 = L2.â[I]V2
       | ââf,I,L1,L2. đâšfâ© & L1 â[S,f] L2 & Y1 = L1.â€[I] & Y2 = L2.â€[I].
#S #Y1 #Y2 #H elim (rex_inv_zero âŠ H) -H *
/3 width=9 by or3_intro0, or3_intro1, or3_intro2, ex4_5_intro, ex4_4_intro, conj/
qed-.

lemma reqg_inv_lref (S):
      âY1,Y2,i. Y1 â[S,#âi] Y2 â
      âšâš â§â§ Y1 = â & Y2 = â
       | ââI1,I2,L1,L2. L1 â[S,#i] L2 & Y1 = L1.â[I1] & Y2 = L2.â[I2].
/2 width=1 by rex_inv_lref/ qed-.

(* Basic_2A1: uses: lleq_inv_bind lleq_inv_bind_O *)
lemma reqg_inv_bind_refl (S):
      reflexive âŠ S â
      âp,I,L1,L2,V,T. L1 â[S,â[p,I]V.T] L2 â
      â§â§ L1 â[S,V] L2 & L1.â[I]V â[S,T] L2.â[I]V.
/3 width=2 by rex_inv_bind, teqg_refl/ qed-.

(* Basic_2A1: uses: lleq_inv_flat *)
lemma reqg_inv_flat (S):
      âI,L1,L2,V,T. L1 â[S,â[I]V.T] L2 â
      â§â§ L1 â[S,V] L2 & L1 â[S,T] L2.
/2 width=2 by rex_inv_flat/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma reqg_inv_zero_pair_sn (S):
      âI,Y2,L1,V1. L1.â[I]V1 â[S,#0] Y2 â
      ââL2,V2. L1 â[S,V1] L2 & V1 â[S] V2 & Y2 = L2.â[I]V2.
/2 width=1 by rex_inv_zero_pair_sn/ qed-.

lemma reqg_inv_zero_pair_dx (S):
      âI,Y1,L2,V2. Y1 â[S,#0] L2.â[I]V2 â
      ââL1,V1. L1 â[S,V1] L2 & V1 â[S] V2 & Y1 = L1.â[I]V1.
/2 width=1 by rex_inv_zero_pair_dx/ qed-.

lemma reqg_inv_lref_bind_sn (S):
      âI1,Y2,L1,i. L1.â[I1] â[S,#âi] Y2 â
      ââI2,L2. L1 â[S,#i] L2 & Y2 = L2.â[I2].
/2 width=2 by rex_inv_lref_bind_sn/ qed-.

lemma reqg_inv_lref_bind_dx (S):
      âI2,Y1,L2,i. Y1 â[S,#âi] L2.â[I2] â
      ââI1,L1. L1 â[S,#i] L2 & Y1 = L1.â[I1].
/2 width=2 by rex_inv_lref_bind_dx/ qed-.

(* Basic forward lemmas *****************************************************)

lemma reqg_fwd_zero_pair (S):
      âI,K1,K2,V1,V2.
      K1.â[I]V1 â[S,#0] K2.â[I]V2 â K1 â[S,V1] K2.
/2 width=3 by rex_fwd_zero_pair/ qed-.

(* Basic_2A1: uses: lleq_fwd_bind_sn lleq_fwd_flat_sn *)
lemma reqg_fwd_pair_sn (S):
      âI,L1,L2,V,T. L1 â[S,âĄ[I]V.T] L2 â L1 â[S,V] L2.
/2 width=3 by rex_fwd_pair_sn/ qed-.

(* Basic_2A1: uses: lleq_fwd_bind_dx lleq_fwd_bind_O_dx *)
lemma reqg_fwd_bind_dx (S):
      reflexive âŠ S â
      âp,I,L1,L2,V,T.
      L1 â[S,â[p,I]V.T] L2 â L1.â[I]V â[S,T] L2.â[I]V.
/3 width=2 by rex_fwd_bind_dx, teqg_refl/ qed-.

(* Basic_2A1: uses: lleq_fwd_flat_dx *)
lemma reqg_fwd_flat_dx (S):
      âI,L1,L2,V,T. L1 â[S,â[I]V.T] L2 â L1 â[S,T] L2.
/2 width=3 by rex_fwd_flat_dx/ qed-.

lemma reqg_fwd_dx (S):
      âI2,L1,K2. âT:term. L1 â[S,T] K2.â[I2] â
      ââI1,K1. L1 = K1.â[I1].
/2 width=5 by rex_fwd_dx/ qed-.
