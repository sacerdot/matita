(* Copyright (C) 2005, HELM Team.
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

(* $Id$ *)

(** {2 Auxiliary functions} *)

let uri = UriManager.uri_of_string

let const ?(subst = []) uri = Cic.Const (uri, subst)
let var ?(subst = []) uri = Cic.Var (uri, subst)
let mutconstruct ?(subst = []) uri typeno consno =
  Cic.MutConstruct (uri, typeno, consno, subst)
let mutind ?(subst = []) uri typeno = Cic.MutInd (uri, typeno, subst)

let indtyuri_of_uri uri =
  let index_sharp =  String.index uri '#' in
  let index_num = index_sharp + 3 in
  (UriManager.uri_of_string (String.sub uri 0 index_sharp),
   int_of_string(String.sub uri index_num (String.length uri - index_num)) - 1)

let indconuri_of_uri uri =
  let index_sharp =  String.index uri '#' in
  let index_div = String.rindex uri '/' in
  let index_con = index_div + 1 in
    (UriManager.uri_of_string (String.sub uri 0 index_sharp),
    int_of_string
      (String.sub uri (index_sharp + 3) (index_div - index_sharp - 3)) - 1,
    int_of_string
      (String.sub uri index_con (String.length uri - index_con)))

(** {2 Helm's objects shorthands} *)

module Logic =
  struct
    let eq_SURI = "cic:/Coq/Init/Logic/eq.ind"
    let eq_URI = uri eq_SURI
    let eq_XURI = eq_SURI ^ "#xpointer(1/1)"
    let eq_ind_URI = uri "cic:/Coq/Init/Logic/eq_ind.con"
    let eq_ind_r_URI = uri "cic:/Coq/Init/Logic/eq_ind_r.con"
    let true_URI = uri "cic:/Coq/Init/Logic/True.ind"
    let false_URI = uri "cic:/Coq/Init/Logic/False.ind"
    let false_ind_URI = uri "cic:/Coq/Init/Logic/False_ind.con"
    let ex_SURI = "cic:/Coq/Init/Logic/ex.ind"
    let ex_URI = uri ex_SURI
    let ex_XURI = ex_SURI ^ "#xpointer(1/1)"
    let ex_ind_URI = uri "cic:/Coq/Init/Logic/ex_ind.con"
    let and_SURI = "cic:/Coq/Init/Logic/and.ind"
    let and_URI = uri and_SURI
    let and_XURI = and_SURI ^ "#xpointer(1/1)"
    let and_ind_URI = uri "cic:/Coq/Init/Logic/and_ind.con"
    let or_SURI = "cic:/Coq/Init/Logic/or.ind"
    let or_URI = uri or_SURI
    let or_XURI = or_SURI ^ "#xpointer(1/1)"
    let not_SURI = "cic:/Coq/Init/Logic/not.con"
    let not_URI = uri not_SURI
    let iff_SURI = "cic:/Coq/Init/Logic/iff.con"
    let iff_URI = uri "cic:/Coq/Init/Logic/iff.con"
    let sym_eq_URI = uri "cic:/Coq/Init/Logic/sym_eq.con"
    let trans_eq_URI = uri "cic:/Coq/Init/Logic/trans_eq.con"
    let absurd_URI = uri "cic:/Coq/Init/Logic/absurd.con"
  end

module Datatypes =
  struct
    let bool_URI = uri "cic:/Coq/Init/Datatypes/bool.ind"
    let nat_URI = uri "cic:/Coq/Init/Datatypes/nat.ind"

    let trueb = mutconstruct bool_URI 0 1
    let falseb = mutconstruct bool_URI 0 2
    let zero = mutconstruct nat_URI 0 1
    let succ = mutconstruct nat_URI 0 2
  end

module Reals =
  struct
    let r_URI = uri "cic:/Coq/Reals/Rdefinitions/R.con"
    let rplus_SURI = "cic:/Coq/Reals/Rdefinitions/Rplus.con"
    let rplus_URI = uri rplus_SURI
    let rminus_SURI = "cic:/Coq/Reals/Rdefinitions/Rminus.con"
    let rminus_URI = uri rminus_SURI
    let rmult_SURI = "cic:/Coq/Reals/Rdefinitions/Rmult.con"
    let rmult_URI = uri rmult_SURI
    let rdiv_SURI = "cic:/Coq/Reals/Rdefinitions/Rdiv.con"
    let rdiv_URI = uri rdiv_SURI
    let ropp_SURI = "cic:/Coq/Reals/Rdefinitions/Ropp.con"
    let ropp_URI = uri ropp_SURI
    let rinv_SURI = "cic:/Coq/Reals/Rdefinitions/Rinv.con"
    let rinv_URI = uri rinv_SURI
    let r0_SURI = "cic:/Coq/Reals/Rdefinitions/R0.con"
    let r0_URI = uri r0_SURI
    let r1_SURI = "cic:/Coq/Reals/Rdefinitions/R1.con"
    let r1_URI = uri r1_SURI
    let rle_SURI = "cic:/Coq/Reals/Rdefinitions/Rle.con"
    let rle_URI = uri rle_SURI
    let rge_SURI = "cic:/Coq/Reals/Rdefinitions/Rge.con"
    let rge_URI = uri rge_SURI
    let rlt_SURI = "cic:/Coq/Reals/Rdefinitions/Rlt.con"
    let rlt_URI = uri rlt_SURI
    let rgt_SURI = "cic:/Coq/Reals/Rdefinitions/Rgt.con"
    let rgt_URI = uri rgt_SURI
    let rtheory_URI = uri "cic:/Coq/Reals/RIneq/RTheory.con"
    let rinv_r1_URI = uri "cic:/Coq/Reals/RIneq/Rinv_1.con"
    let pow_URI = uri "cic:/Coq/Reals/Rfunctions/pow.con"

    let r = const r_URI
    let rplus = const rplus_URI
    let rmult = const rmult_URI
    let ropp = const ropp_URI
    let r0 = const r0_URI
    let r1 = const r1_URI
    let rtheory = const rtheory_URI
  end

module Peano =
  struct
    let plus_SURI = "cic:/Coq/Init/Peano/plus.con"
    let plus_URI = uri plus_SURI
    let minus_SURI = "cic:/Coq/Init/Peano/minus.con"
    let minus_URI = uri minus_SURI
    let mult_SURI = "cic:/Coq/Init/Peano/mult.con"
    let mult_URI = uri mult_SURI
    let pred_URI = uri "cic:/Coq/Init/Peano/pred.con"
    let le_SURI = "cic:/Coq/Init/Peano/le.ind"
    let le_URI = uri le_SURI
    let le_XURI = le_SURI ^ "#xpointer(1/1)"
    let ge_SURI = "cic:/Coq/Init/Peano/ge.con"
    let ge_URI = uri ge_SURI
    let lt_SURI = "cic:/Coq/Init/Peano/lt.con"
    let lt_URI = uri lt_SURI
    let gt_SURI = "cic:/Coq/Init/Peano/gt.con"
    let gt_URI = uri gt_SURI

    let plus = const plus_URI
    let mult = const mult_URI
    let pred = const pred_URI
  end

module BinPos =
  struct
    let positive_SURI = "cic:/Coq/NArith/BinPos/positive.ind"
    let positive_URI = uri positive_SURI
    let xI = mutconstruct positive_URI 0 1
    let xO = mutconstruct positive_URI 0 2
    let xH = mutconstruct positive_URI 0 3
    let pplus_SURI = "cic:/Coq/NArith/BinPos/Pplus.con"
    let pplus_URI = uri pplus_SURI
    let pplus = const pplus_URI
    let pminus_SURI = "cic:/Coq/NArith/BinPos/Pminus.con"
    let pminus_URI = uri pminus_SURI
    let pminus = const pminus_URI
    let pmult_SURI = "cic:/Coq/NArith/BinPos/Pmult.con"
    let pmult_URI = uri pmult_SURI
    let pmult = const pmult_URI
  end

module BinInt =
  struct
    let zmult_URI = uri "cic:/Coq/ZArith/BinInt/Zmult.con"
    let zmult = const zmult_URI
    let zplus_SURI = "cic:/Coq/ZArith/BinInt/Zplus.con"
    let zplus_URI = uri zplus_SURI
    let zplus = const zplus_URI
    let zminus_SURI = "cic:/Coq/ZArith/BinInt/Zminus.con"
    let zminus_URI = uri zminus_SURI
    let zminus = const zminus_URI
    let z_SURI = "cic:/Coq/ZArith/BinInt/Z.ind"
    let z_URI = uri z_SURI
    let z0 = mutconstruct z_URI 0 1
    let zpos = mutconstruct z_URI 0 2
    let zneg = mutconstruct z_URI 0 3
    let zopp_SURI = "cic:/Coq/ZArith/BinInt/Zopp.con"
    let zopp_URI = uri zopp_SURI
    let zopp = const zopp_URI
    let zpower_URI = uri "cic:/Coq/ZArith/Zpower/Zpower.con"
  end

(** {2 Helpers for creating common terms}
 *  (e.g. numbers)} *)

exception NegativeInteger

let build_nat n =
  if n < 0 then raise NegativeInteger;
  let rec aux = function
    | 0 -> Datatypes.zero
    | n -> Cic.Appl [ Datatypes.succ; (aux (n - 1)) ]
  in
  aux n

let build_real n =
  if n < 0 then raise NegativeInteger;
  let rec aux = function
    | 0 -> Reals.r0
    | 1 -> Reals.r1 (* to avoid trailing "+ 0" *)
    | n -> Cic.Appl [ Reals.rplus; Reals.r1; (aux (n - 1)) ]
  in
  aux n

let build_bin_pos n =
  if n < 1 then raise NegativeInteger;
  let rec aux = function
    | 1 -> BinPos.xH
    | n when n mod 2 = 0 -> Cic.Appl [ BinPos.xO; aux (n / 2) ]
    | n -> Cic.Appl [ BinPos.xI; aux (n / 2) ]
  in
  aux n

