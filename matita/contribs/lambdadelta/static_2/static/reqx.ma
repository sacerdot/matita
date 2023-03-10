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

include "static_2/notation/relations/approxeqsn_3.ma".
include "static_2/syntax/teqx_ext.ma".
include "static_2/static/reqg.ma".

(* SORT-IRRELEVANT EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES ***)
(*
definition reqx: relation3 âŠ â
           reqg sfull.
*)
interpretation
  "sort-irrelevant equivalence on referred entries (local environment)"
  'ApproxEqSn T L1 L2 = (reqg sfull T L1 L2).

interpretation
  "sort-irrelevant ranged equivalence (local environment)"
  'StarEqSn f L1 L2 = (sex ceqx_ext cfull f L1 L2).

(* Basic properties ***********************************************************)
(*
lemma frees_teqx_conf_reqx:
      âf,L1,T1. L1 âą đ+âšT1â© â f â âT2. T1 â T2 â
      âL2. L1 â[f] L2 â L2 âą đ+âšT2â© â f.
#f #L1 #T1 #H elim H -f -L1 -T1
[ #f #L1 #s1 #Hf #X #H1 #L2 #_
  elim (teqx_inv_sort1 âŠ H1) -H1 #s2 #H destruct
  /2 width=3 by frees_sort/
| #f #i #Hf #X #H1
  >(teqx_inv_lref1 âŠ H1) -X #Y #H2
  >(sex_inv_atom1 âŠ H2) -Y
  /2 width=1 by frees_atom/
| #f #I #L1 #V1 #_ #IH #X #H1
  >(teqx_inv_lref1 âŠ H1) -X #Y #H2
  elim (sex_inv_next1 âŠ H2) -H2 #Z #L2 #HL12 #HZ #H destruct
  elim (ext2_inv_pair_sn âŠ HZ) -HZ #V2 #HV12 #H destruct
  /3 width=1 by frees_pair/
| #f #I #L1 #Hf #X #H1
  >(teqx_inv_lref1 âŠ H1) -X #Y #H2
  elim (sex_inv_next1 âŠ H2) -H2 #Z #L2 #_ #HZ #H destruct
  >(ext2_inv_unit_sn âŠ HZ) -Z /2 width=1 by frees_unit/
| #f #I #L1 #i #_ #IH #X #H1
  >(teqx_inv_lref1 âŠ H1) -X #Y #H2
  elim (sex_inv_push1 âŠ H2) -H2 #J #L2 #HL12 #_ #H destruct
  /3 width=1 by frees_lref/
| #f #L1 #l #Hf #X #H1 #L2 #_
  >(teqx_inv_gref1 âŠ H1) -X /2 width=1 by frees_gref/
| #f1V #f1T #f1 #p #I #L1 #V1 #T1 #_ #_ #Hf1 #IHV #IHT #X #H1
  elim (teqx_inv_pair1 âŠ H1) -H1 #V2 #T2 #HV12 #HT12 #H1 #L2 #HL12 destruct
  /6 width=5 by frees_bind, sex_inv_tl, ext2_pair, sle_sex_trans, sor_inv_sle_dx, sor_inv_sle_sn/
| #f1V #f1T #f1 #I #L1 #V1 #T1 #_ #_ #Hf1 #IHV #IHT #X #H1
  elim (teqx_inv_pair1 âŠ H1) -H1 #V2 #T2 #HV12 #HT12 #H1 #L2 #HL12 destruct
  /5 width=5 by frees_flat, sle_sex_trans, sor_inv_sle_dx, sor_inv_sle_sn/
]
qed-.

lemma frees_teqx_conf:
      âf,L,T1. L âą đ+âšT1â© â f â
      âT2. T1 â T2 â L âą đ+âšT2â© â f.
/4 width=7 by frees_teqx_conf_reqx, sex_refl, ext2_refl/ qed-.

lemma frees_reqx_conf:
      âf,L1,T. L1 âą đ+âšTâ© â f â
      âL2. L1 â[f] L2 â L2 âą đ+âšTâ© â f.
/2 width=7 by frees_teqx_conf_reqx, teqx_refl/ qed-.

lemma teqx_rex_conf_sn (R):
      s_r_confluent1 âŠ cdeq (rex R).
#R #L1 #T1 #T2 #HT12 #L2 *
/3 width=5 by frees_teqx_conf, ex2_intro/
qed-.

lemma teqx_rex_div (R):
      âT1,T2. T1 â T2 â
      âL1,L2. L1 âȘ€[R,T2] L2 â L1 âȘ€[R,T1] L2.
/3 width=5 by teqx_rex_conf_sn, teqx_sym/ qed-.

lemma teqx_reqx_conf_sn:
      s_r_confluent1 âŠ cdeq reqx.
/2 width=5 by teqx_rex_conf_sn/ qed-.

lemma teqx_reqx_div:
      âT1,T2. T1 â T2 â
      âL1,L2. L1 â[T2] L2 â L1 â[T1] L2.
/2 width=5 by teqx_rex_div/ qed-.

lemma reqx_atom: âI. â â[âȘ[I]] â.
/2 width=1 by rex_atom/ qed.

lemma reqx_sort:
      âI1,I2,L1,L2,s.
      L1 â[âs] L2 â L1.â[I1] â[âs] L2.â[I2].
/2 width=1 by rex_sort/ qed.

lemma reqx_pair:
      âI,L1,L2,V1,V2.
      L1 â[V1] L2 â V1 â V2 â L1.â[I]V1 â[#0] L2.â[I]V2.
/2 width=1 by rex_pair/ qed.

lemma reqx_unit:
      âf,I,L1,L2. đâšfâ© â L1 â[f] L2 â
      L1.â€[I] â[#0] L2.â€[I].
/2 width=3 by rex_unit/ qed.

lemma reqx_lref:
      âI1,I2,L1,L2,i.
      L1 â[#i] L2 â L1.â[I1] â[#âi] L2.â[I2].
/2 width=1 by rex_lref/ qed.

lemma reqx_gref:
      âI1,I2,L1,L2,l.
      L1 â[Â§l] L2 â L1.â[I1] â[Â§l] L2.â[I2].
/2 width=1 by rex_gref/ qed.

lemma reqx_bind_repl_dx:
      âI,I1,L1,L2.âT:term. L1.â[I] â[T] L2.â[I1] â
      âI2. I â I2 â L1.â[I] â[T] L2.â[I2].
/2 width=2 by rex_bind_repl_dx/ qed-.
*)
lemma reqg_reqx (S) (T):
      âL1,L2. L1 â[S,T] L2 â L1 â[T] L2.
/2 width=3 by reqg_co/ qed.
(*
(* Basic inversion lemmas ***************************************************)

lemma reqx_inv_atom_sn:
      âY2. âT:term. â â[T] Y2 â Y2 = â.
/2 width=3 by rex_inv_atom_sn/ qed-.

lemma reqx_inv_atom_dx:
      âY1. âT:term. Y1 â[T] â â Y1 = â.
/2 width=3 by rex_inv_atom_dx/ qed-.

lemma reqx_inv_zero:
      âY1,Y2. Y1 â[#0] Y2 â
      âšâš â§â§ Y1 = â & Y2 = â
       | ââI,L1,L2,V1,V2. L1 â[V1] L2 & V1 â V2 & Y1 = L1.â[I]V1 & Y2 = L2.â[I]V2
       | ââf,I,L1,L2. đâšfâ© & L1 â[f] L2 & Y1 = L1.â€[I] & Y2 = L2.â€[I].
#Y1 #Y2 #H elim (rex_inv_zero âŠ H) -H *
/3 width=9 by or3_intro0, or3_intro1, or3_intro2, ex4_5_intro, ex4_4_intro, conj/
qed-.

lemma reqx_inv_lref:
      âY1,Y2,i. Y1 â[#âi] Y2 â
      âšâš â§â§ Y1 = â & Y2 = â
       | ââI1,I2,L1,L2. L1 â[#i] L2 & Y1 = L1.â[I1] & Y2 = L2.â[I2].
/2 width=1 by rex_inv_lref/ qed-.

(* Basic_2A1: uses: lleq_inv_bind lleq_inv_bind_O *)
lemma reqx_inv_bind:
      âp,I,L1,L2,V,T. L1 â[â[p,I]V.T] L2 â
      â§â§ L1 â[V] L2 & L1.â[I]V â[T] L2.â[I]V.
/2 width=2 by rex_inv_bind/ qed-.

(* Basic_2A1: uses: lleq_inv_flat *)
lemma reqx_inv_flat:
      âI,L1,L2,V,T. L1 â[â[I]V.T] L2 â
      â§â§ L1 â[V] L2 & L1 â[T] L2.
/2 width=2 by rex_inv_flat/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma reqx_inv_zero_pair_sn:
      âI,Y2,L1,V1. L1.â[I]V1 â[#0] Y2 â
      ââL2,V2. L1 â[V1] L2 & V1 â V2 & Y2 = L2.â[I]V2.
/2 width=1 by rex_inv_zero_pair_sn/ qed-.

lemma reqx_inv_zero_pair_dx:
      âI,Y1,L2,V2. Y1 â[#0] L2.â[I]V2 â
      ââL1,V1. L1 â[V1] L2 & V1 â V2 & Y1 = L1.â[I]V1.
/2 width=1 by rex_inv_zero_pair_dx/ qed-.

lemma reqx_inv_lref_bind_sn:
      âI1,Y2,L1,i. L1.â[I1] â[#âi] Y2 â
      ââI2,L2. L1 â[#i] L2 & Y2 = L2.â[I2].
/2 width=2 by rex_inv_lref_bind_sn/ qed-.

lemma reqx_inv_lref_bind_dx:
      âI2,Y1,L2,i. Y1 â[#âi] L2.â[I2] â
      ââI1,L1. L1 â[#i] L2 & Y1 = L1.â[I1].
/2 width=2 by rex_inv_lref_bind_dx/ qed-.

(* Basic forward lemmas *****************************************************)

lemma reqx_fwd_zero_pair:
      âI,K1,K2,V1,V2.
      K1.â[I]V1 â[#0] K2.â[I]V2 â K1 â[V1] K2.
/2 width=3 by rex_fwd_zero_pair/ qed-.

(* Basic_2A1: uses: lleq_fwd_bind_sn lleq_fwd_flat_sn *)
lemma reqx_fwd_pair_sn:
      âI,L1,L2,V,T. L1 â[âĄ[I]V.T] L2 â L1 â[V] L2.
/2 width=3 by rex_fwd_pair_sn/ qed-.

(* Basic_2A1: uses: lleq_fwd_bind_dx lleq_fwd_bind_O_dx *)
lemma reqx_fwd_bind_dx:
      âp,I,L1,L2,V,T.
      L1 â[â[p,I]V.T] L2 â L1.â[I]V â[T] L2.â[I]V.
/2 width=2 by rex_fwd_bind_dx/ qed-.

(* Basic_2A1: uses: lleq_fwd_flat_dx *)
lemma reqx_fwd_flat_dx:
      âI,L1,L2,V,T. L1 â[â[I]V.T] L2 â L1 â[T] L2.
/2 width=3 by rex_fwd_flat_dx/ qed-.

lemma reqx_fwd_dx:
      âI2,L1,K2. âT:term. L1 â[T] K2.â[I2] â
      ââI1,K1. L1 = K1.â[I1].
/2 width=5 by rex_fwd_dx/ qed-.
*)
