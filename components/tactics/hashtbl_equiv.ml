(* Copyright (C) 2000-2002, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://cs.unibo.it/helm/.
 *)

(*********************************************************************)
(*                                                                   *)
(*                           PROJECT HELM                            *)
(*                                                                   *)
(*                          Andrea Asperti                           *)
(*                            8/09/2004                              *)
(*                                                                   *)
(*                                                                   *)
(*********************************************************************)

(* $Id$ *)

(* the file contains an hash table of objects of the library
   equivalent to some object in the standard subset; it is
   mostly used to filter useless cases in auto *)


let equivalent_objects =
(* finte costanti; i.e. costanti senza corpo *)
[UriManager.uri_of_string "cic:/Rocq/DEMOS/Demo_AutoRewrite/Ack0.con"(*,"finte costanti"*);
 UriManager.uri_of_string "cic:/Rocq/DEMOS/Demo_AutoRewrite/Ac10.con"(*,"finte costanti"*);
 UriManager.uri_of_string "cic:/Rocq/DEMOS/Demo_AutoRewrite/Ack2.con"(*,"finte costanti"*)
 ]@
(* inutili mostri *)
[UriManager.uri_of_string "cic:/Rocq/DEMOS/Demo_AutoRewrite/Resg0.con"(*,"useless monster"*);
 UriManager.uri_of_string "cic:/Rocq/DEMOS/Demo_AutoRewrite/Resg1.con"(*,"useless monster"*);
 UriManager.uri_of_string "cic:/Rocq/DEMOS/Demo_AutoRewrite/ResAck0.con"(*,"useless monster"*)
 ]@
(* istanze *)
   (UriManager.uri_of_string "cic:/Coq/Init/Peano/eq_S.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Logic/f_equal.con"*))::
[
UriManager.uri_of_string "cic:/Paris/ZF/src/useful/lem_iff_sym.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Logic/iff_sym.con"*);
UriManager.uri_of_string "cic:/Lyon/AUTOMATA/Ensf_types/False_imp_P.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Logic/False_ind.con"*);
UriManager.uri_of_string "cic:/Rocq/TreeAutomata/bases/plus_O_r.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Plus/plus_0_r.con"*);
UriManager.uri_of_string "cic:/Coq/Reals/Rfunctions/sum_f_R0_triangle.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/PartSum/Rabs_triang_gen.con"*);
UriManager.uri_of_string "cic:/Sophia-Antipolis/Bertrand/Misc/eq_plus.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Plus/plus_reg_l.con"*);
UriManager.uri_of_string "cic:/Suresnes/BDD/rauzy/algorithme1/Prelude_BDT/deMorgan_not_and.con"(*,UriManager.uri_of_string "cic:/Coq/Logic/Classical_Prop/or_not_and.con"*);
UriManager.uri_of_string "cic:/Rocq/DEMOS/Sorting/diff_true_false.con"(*,UriManager.uri_of_string "cic:/Coq/Bool/Bool/diff_true_false.con"*);
UriManager.uri_of_string "cic:/CoRN/metrics/CMetricSpaces/nz.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Max/le_max_l.con"*);
UriManager.uri_of_string "cic:/Coq/Logic/Decidable/not_or.con"(*,UriManager.uri_of_string "cic:/Coq/Logic/Classical_Prop/not_or_and.con"*);
UriManager.uri_of_string "cic:/Coq/Init/Logic/sym_not_equal.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Logic/sym_not_eq.con"*);
UriManager.uri_of_string "cic:/Coq/Reals/R_sqrt/sqrt_sqrt.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/R_sqrt/sqrt_def.con"*);
UriManager.uri_of_string "cic:/Coq/Reals/Rlimit/eps2_Rgt_R0_subproof.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/Rlimit/eps2_Rgt_R0.con"*);
UriManager.uri_of_string "cic:/Coq/Logic/Eqdep_dec/eqT2eq.con"(*,UriManager.uri_of_string "cic:/Coq/Logic/Eqdep_dec/eq2eqT.con"*);
UriManager.uri_of_string "cic:/Coq/Reals/R_sqr/Rsqr_eq_0.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/RIneq/Rsqr_0_uniq.con"*);
UriManager.uri_of_string "cic:/Rocq/THREE_GAP/Nat_compl/en_plus.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Plus/plus_0_r.con"*);
UriManager.uri_of_string "cic:/Nijmegen/QArith/Zaux/Zabs_10.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/Zabs/Zabs_pos.con"*);
UriManager.uri_of_string "cic:/Coq/Reals/Rlimit/Rlt_eps4_eps_subproof0.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/Rlimit/Rlt_eps2_eps_subproof.con"*);
UriManager.uri_of_string "cic:/Coq/Arith/Le/le_refl.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Peano/le.ind#xpointer(1/1/1)"*); 
UriManager.uri_of_string "cic:/Rocq/TreeAutomata/bases/le_n_n.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Le/le_refl.con"*);
UriManager.uri_of_string "cic:/Coq/ZArith/auxiliary/Zred_factor1.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/BinInt/Zplus_diag_eq_mult_2.con"*);
UriManager.uri_of_string "cic:/Coq/Relations/Newman/caseRxy.con"(*,UriManager.uri_of_string "cic:/Coq/Relations/Newman/Ind_proof.con"*);
UriManager.uri_of_string "cic:/Rocq/TreeAutomata/bases/S_plus_r.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Peano/plus_n_Sm.con"*);
UriManager.uri_of_string "cic:/Eindhoven/POCKLINGTON/lemmas/Zmult_ab0a0b0.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/BinInt/Zmult_integral.con"*);
UriManager.uri_of_string "cic:/Sophia-Antipolis/Algebra/Z_group/ax8.con"(*,UriManager.uri_of_string "cic:/Coq/NArith/BinPos/ZC2.con"*);
UriManager.uri_of_string "cic:/Sophia-Antipolis/Algebra/Z_group/Zlt_reg_l.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/Zorder/Zplus_lt_compat_l.con"*);
UriManager.uri_of_string "cic:/Sophia-Antipolis/MATHS/Z/Nat_complements/mult_neutr.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Mult/mult_1_l.con"*);
UriManager.uri_of_string "cic:/Coq/fourier/Fourier_util/Rlt_zero_1.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/RIneq/Rlt_0_1.con"*);
UriManager.uri_of_string "cic:/Suresnes/BDD/rauzy/algorithme1/Prelude_BDT/Classic.con"(*,UriManager.uri_of_string "cic:/Coq/Logic/Classical_Prop/NNPP.con"*);
UriManager.uri_of_string "cic:/Coq/Reals/R_sqr/Rsqr_pos_lt.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/RIneq/Rlt_0_sqr.con"*);
UriManager.uri_of_string "cic:/Rocq/THREE_GAP/Nat_compl/lt_minus2.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/ArithProp/lt_minus_O_lt.con"*);
UriManager.uri_of_string "cic:/Coq/Reals/Rtrigo_def/sin_antisym.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/Rtrigo/sin_neg.con"*);
UriManager.uri_of_string "cic:/Sophia-Antipolis/Functions_in_ZFC/Functions_in_ZFC/false_implies_everything.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Logic/False_ind.con"*);
UriManager.uri_of_string "cic:/Coq/ring/Setoid_ring_normalize/index_eq_prop.con"(*,UriManager.uri_of_string "cic:/Coq/ring/Ring_normalize/index_eq_prop.con"*);
UriManager.uri_of_string "cic:/CoRN/algebra/Basics/le_pred.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Le/le_pred.con"*);
UriManager.uri_of_string "cic:/Lannion/continuations/FOUnify_cps/nat_complements/le_S_eqP.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Compare/le_le_S_eq.con"*);
UriManager.uri_of_string "cic:/Coq/Sorting/Permutation/permut_right.con"(*,UriManager.uri_of_string "cic:/Coq/Sorting/Permutation/permut_cons.con"*);
UriManager.uri_of_string "cic:/Eindhoven/POCKLINGTON/lemmas/Zlt_mult_l.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/Zorder/Zmult_lt_compat_l.con"*);
UriManager.uri_of_string "cic:/Coq/Reals/RIneq/Rplus_lt_0_compat.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/DiscrR/Rplus_lt_pos.con"*);
UriManager.uri_of_string "cic:/Nijmegen/QArith/Zaux/Zpower_1_subproof.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/BinInt/Zmult_1_r.con"*);
UriManager.uri_of_string "cic:/CoRN/fta/KeyLemma/lem_1c.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Minus/le_minus.con"*);
UriManager.uri_of_string "cic:/Coq/omega/OmegaLemmas/OMEGA20.con"(*,UriManager.uri_of_string "cic:/Coq/omega/OmegaLemmas/OMEGA17.con"*);
UriManager.uri_of_string "cic:/Nijmegen/QArith/Zaux/pair_2.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Datatypes/injective_projections.con"*);
UriManager.uri_of_string "cic:/Coq/Reals/Rlimit/Rlt_eps4_eps_subproof.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/Rlimit/Rlt_eps2_eps_subproof.con"*);
UriManager.uri_of_string "cic:/CoRN/algebra/Basics/le_mult_right.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Mult/mult_le_compat_r.con"*);
UriManager.uri_of_string "cic:/Nijmegen/QArith/Zaux/Zle_lt_plus_plus.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/Zorder/Zplus_le_lt_compat.con"*);
UriManager.uri_of_string "cic:/Rocq/ARITH/Chinese/Nat_complements/lt_minus2.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/ArithProp/lt_minus_O_lt.con"*);
UriManager.uri_of_string "cic:/Rocq/THREE_GAP/Nat_compl/not_gt_le.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Compare_dec/not_gt.con"*);
UriManager.uri_of_string "cic:/Rocq/ARITH/Chinese/Nat_complements/mult_commut.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Mult/mult_comm.con"*);
UriManager.uri_of_string "cic:/CoRN/algebra/Basics/lt_mult_right.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Mult/mult_lt_compat_r.con"*);
UriManager.uri_of_string "cic:/Rocq/ARITH/Chinese/Nat_complements/mult_neutr.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Mult/mult_1_l.con"*);
UriManager.uri_of_string "cic:/Nijmegen/QArith/Zaux/Zabs_neg.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/Zabs/Zabs_non_eq.con"*);
UriManager.uri_of_string "cic:/Lyon/FIRING-SQUAD/bib/plus_S.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Peano/plus_Sn_m.con"*);
UriManager.uri_of_string "cic:/Nijmegen/QArith/Qhomographic_Qpositive_to_Qpositive/one_non_negative.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/Zorder/Zle_0_1.con"*);
UriManager.uri_of_string "cic:/Coq/fourier/Fourier_util/Rle_zero_1.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/RIneq/Rle_0_1.con"*);
UriManager.uri_of_string "cic:/Coq/Logic/Diaconescu/proof_irrel.con"(*,UriManager.uri_of_string "cic:/Coq/Logic/Classical_Prop/proof_irrelevance.con"*);
UriManager.uri_of_string "cic:/Coq/Init/Logic/sym_equal.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Logic/sym_eq.con"*);
UriManager.uri_of_string "cic:/Coq/IntMap/Mapiter/pair_sp.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Datatypes/surjective_pairing.con"*);
UriManager.uri_of_string "cic:/Coq/Logic/ProofIrrelevance/proof_irrelevance_cci.con"(*,UriManager.uri_of_string "cic:/Coq/Logic/Classical_Prop/proof_irrelevance.con"*);
UriManager.uri_of_string "cic:/Suresnes/BDD/rauzy/algorithme1/Prelude_BDT/deMorgan_or_not.con"(*,UriManager.uri_of_string "cic:/Coq/Logic/Classical_Prop/not_and_or.con"*);
UriManager.uri_of_string "cic:/CoRN/model/structures/Zsec/Zplus_wd0.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/BinInt/Zplus_eq_compat.con"*);
UriManager.uri_of_string "cic:/Coq/ZArith/auxiliary/Zred_factor6.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/BinInt/Zplus_0_r_reverse.con"*);
UriManager.uri_of_string "cic:/Eindhoven/POCKLINGTON/lemmas/S_inj.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Peano/eq_add_S.con"*);
UriManager.uri_of_string "cic:/Coq/ZArith/Wf_Z/Z_of_nat_complete.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/RIneq/IZN.con"*);
UriManager.uri_of_string "cic:/Suresnes/BDD/rauzy/algorithme1/Prelude_BDT/Commutative_orb.con"(*,UriManager.uri_of_string "cic:/Coq/Bool/Bool/orb_comm.con"*);
UriManager.uri_of_string "cic:/Coq/Reals/PartSum/plus_sum.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/Cauchy_prod/sum_plus.con"*);
UriManager.uri_of_string "cic:/Nijmegen/QArith/Qpositive/minus_le.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Minus/le_minus.con"*);
UriManager.uri_of_string "cic:/Lyon/FIRING-SQUAD/bib/plus_zero.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Plus/plus_0_r.con"*);
UriManager.uri_of_string "cic:/Sophia-Antipolis/Cours-de-Coq/ex1_auto/not_not_converse.con"(*,UriManager.uri_of_string "cic:/Coq/Logic/Classical_Prop/NNPP.con"*);
UriManager.uri_of_string "cic:/Suresnes/BDD/rauzy/algorithme1/Prelude_BDT/deMorgan_and_not.con"(*,UriManager.uri_of_string "cic:/Coq/Logic/Classical_Prop/not_or_and.con"*);
UriManager.uri_of_string "cic:/Suresnes/BDD/rauzy/algorithme1/Prelude_BDT/Commutative_andb.con"(*,UriManager.uri_of_string "cic:/Coq/Bool/Bool/andb_comm.con"*);
UriManager.uri_of_string "cic:/Sophia-Antipolis/MATHS/Z/Nat_complements/lt_minus2.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/ArithProp/lt_minus_O_lt.con"*);
UriManager.uri_of_string "cic:/Suresnes/BDD/canonicite/Prelude0/Morgan_and_not.con"(*,UriManager.uri_of_string "cic:/Coq/Logic/Classical_Prop/not_or_and.con"*);
UriManager.uri_of_string "cic:/Coq/Logic/ClassicalFacts/TrueP.con"(*,UriManager.uri_of_string "cic:/Coq/Logic/ClassicalFacts/FalseP.con"*);
UriManager.uri_of_string "cic:/Nijmegen/QArith/Zaux/Zminus_eq.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/BinInt/Zminus_eq.con"*);
UriManager.uri_of_string "cic:/Sophia-Antipolis/Cours-de-Coq/ex1/not_not_converse.con"(*,UriManager.uri_of_string "cic:/Coq/Logic/Classical_Prop/NNPP.con"*);
UriManager.uri_of_string "cic:/Nijmegen/QArith/Zaux/pair_1.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Datatypes/surjective_pairing.con"*);
UriManager.uri_of_string "cic:/Orsay/Maths/divide/Zabs_ind.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/Zabs/Zabs_ind.con"*);
UriManager.uri_of_string "cic:/CoRN/algebra/Basics/Zmult_minus_distr_r.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/BinInt/Zmult_minus_distr_l.con"*);
UriManager.uri_of_string "cic:/Coq/fourier/Fourier_util/Rfourier_eqLR_to_le.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/RIneq/Req_le.con"*);
UriManager.uri_of_string "cic:/Rocq/TreeAutomata/bases/Sn_eq_Sm_n_eq_m.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Peano/eq_add_S.con"*);
UriManager.uri_of_string "cic:/Coq/Init/Logic/trans_equal.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Logic/trans_eq.con"*);
UriManager.uri_of_string "cic:/Coq/omega/OmegaLemmas/OMEGA2.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/Zorder/Zplus_le_0_compat.con"*);
UriManager.uri_of_string "cic:/Sophia-Antipolis/Bertrand/Raux/P_Rmin.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/Rpower/P_Rmin.con"*);
UriManager.uri_of_string "cic:/Sophia-Antipolis/MATHS/Z/Nat_complements/mult_commut.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Mult/mult_comm.con"*);
UriManager.uri_of_string "cic:/Sophia-Antipolis/Huffman/Aux/le_minus.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Minus/le_minus.con"*);
UriManager.uri_of_string "cic:/Coq/Init/Peano/plus_O_n.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Plus/plus_0_l.con"*);
UriManager.uri_of_string "cic:/Coq/Logic/Berardi/inv2.con"(*,UriManager.uri_of_string "cic:/Coq/Logic/Berardi/AC.con"*);
UriManager.uri_of_string "cic:/Coq/Reals/SeqProp/not_Rlt.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/RIneq/Rnot_lt_ge.con"*);
UriManager.uri_of_string "cic:/Nancy/FOUnify/nat_complements/le_S_eqP.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Compare/le_le_S_eq.con"*);
UriManager.uri_of_string "cic:/Rocq/TreeAutomata/bases/le_mult_l.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Mult/mult_le_compat_r.con"*);
UriManager.uri_of_string "cic:/Eindhoven/POCKLINGTON/natZ/isnat_mult.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/Zorder/Zmult_le_0_compat.con"*);
UriManager.uri_of_string "cic:/Coq/fourier/Fourier_util/Rfourier_eqRL_to_le.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/RIneq/Req_le_sym.con"*);
UriManager.uri_of_string "cic:/Nijmegen/QArith/Zaux/Zabs_mult.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/Zabs/Zabs_Zmult.con"*);
UriManager.uri_of_string "cic:/Rocq/TreeAutomata/bases/plus_n_O.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Plus/plus_0_r.con"*);
UriManager.uri_of_string "cic:/Suresnes/BDD/rauzy/algorithme1/Prelude_BDT/excluded_middle.con"(*,UriManager.uri_of_string "cic:/Coq/Logic/Classical_Prop/classic.con"*);
UriManager.uri_of_string "cic:/Rocq/TreeAutomata/bases/le_mult_mult.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Mult/mult_le_compat.con"*);
UriManager.uri_of_string "cic:/Coq/Bool/Bool/Is_true_eq_true2.con"(*,UriManager.uri_of_string "cic:/Coq/Bool/Bool/Is_true_eq_left.con"*);
UriManager.uri_of_string "cic:/Eindhoven/POCKLINGTON/natZ/isnat_plus.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/Zorder/Zplus_le_0_compat.con"*);
UriManager.uri_of_string "cic:/Eindhoven/POCKLINGTON/lemmas/lt_plus_plus.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Plus/plus_lt_compat.con"*);
UriManager.uri_of_string "cic:/Rocq/TreeAutomata/bases/le_mult_r.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Mult/mult_le_compat_l.con"*);
UriManager.uri_of_string "cic:/Sophia-Antipolis/Functions_in_ZFC/Functions_in_ZFC/excluded_middle.con"(*,UriManager.uri_of_string "cic:/Coq/Logic/Classical_Prop/NNPP.con"*);
UriManager.uri_of_string "cic:/Sophia-Antipolis/Algebra/Z_group/ax3.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/Zorder/Zgt_pos_0.con"*);
UriManager.uri_of_string "cic:/Nijmegen/QArith/Zaux/Zabs_plus.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/Zabs/Zabs_triangle.con"*);
UriManager.uri_of_string "cic:/Sophia-Antipolis/Buchberger/Buch/Sdep.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Datatypes/prod_ind.con"*);
UriManager.uri_of_string "cic:/Coq/Reals/PartSum/Rsum_abs.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/PartSum/Rabs_triang_gen.con"*);
UriManager.uri_of_string "cic:/Cachan/SMC/mu/minus_n_m_le_n.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Minus/le_minus.con"*);
UriManager.uri_of_string "cic:/Marseille/GC/lib_arith/lib_S_pred/eqnm_eqSnSm.con"(*,UriManager.uri_of_string "cic:/Coq/Init/Peano/eq_S.con"*);
UriManager.uri_of_string "cic:/Nijmegen/QArith/Zaux/Zpower_1_subproof_subproof.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/BinInt/Zmult_1_r.con"*);
UriManager.uri_of_string "cic:/Eindhoven/POCKLINGTON/lemmas/predminus1.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Minus/pred_of_minus.con"*);
UriManager.uri_of_string "cic:/Sophia-Antipolis/Bertrand/Raux/Rpower_pow.con"(*,UriManager.uri_of_string "cic:/Coq/Reals/Rpower/Rpower_pow.con"*);
UriManager.uri_of_string "cic:/Lyon/FIRING-SQUAD/bib/lt_plus_plus.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Plus/plus_lt_compat.con"*);
UriManager.uri_of_string "cic:/Eindhoven/POCKLINGTON/lemmas/Zlt_neq.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/Zorder/Zlt_not_eq.con"*);
UriManager.uri_of_string "cic:/Coq/Arith/Lt/nat_total_order.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Compare_dec/not_eq.con"*);
UriManager.uri_of_string "cic:/Rocq/TreeAutomata/bases/plus_O_l.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Plus/plus_0_r.con"*);
UriManager.uri_of_string "cic:/Coq/Logic/ClassicalFacts/boolP.ind#xpointer(1/1/2)"(*,UriManager.uri_of_string "cic:/Coq/Logic/ClassicalFacts/boolP.ind#xpointer(1/1/1)"*);
UriManager.uri_of_string "cic:/Nijmegen/QArith/Zaux/Zmult_pos_pos.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/Zorder/Zmult_lt_O_compat.con"*);
UriManager.uri_of_string "cic:/Nijmegen/QArith/Zaux/Zlt_plus_plus.con"(*,UriManager.uri_of_string "cic:/Coq/ZArith/Zorder/Zplus_lt_compat.con"*);
UriManager.uri_of_string "cic:/Coq/Logic/Diaconescu/pred_ext_and_rel_choice_imp_EM.con"(*,UriManager.uri_of_string "cic:/Coq/Logic/Classical_Prop/classic.con"*);
UriManager.uri_of_string "cic:/Sophia-Antipolis/Rsa/MiscRsa/eq_plus.con"(*,UriManager.uri_of_string "cic:/Coq/Arith/Plus/plus_reg_l.con"*)
]
;;

let equiv_table = Hashtbl.create 503
;;

let _ = List.iter (fun a -> Hashtbl.add equiv_table a "") equivalent_objects
;; 

let not_a_duplicate u =
  try
    ignore(Hashtbl.find equiv_table u); false
  with
    Not_found -> true
;;
