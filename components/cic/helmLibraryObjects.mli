(* Copyright (C) 2004, HELM Team.
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
 * http://helm.cs.unibo.it/
 *)

module Logic :
  sig
    val absurd_URI :    UriManager.uri
    val and_ind_URI :   UriManager.uri
    val and_URI :       UriManager.uri
    val eq_ind_r_URI :  UriManager.uri
    val eq_ind_URI :    UriManager.uri
    val eq_URI :        UriManager.uri
    val ex_ind_URI :    UriManager.uri
    val ex_URI :        UriManager.uri
    val false_ind_URI : UriManager.uri
    val false_URI :     UriManager.uri
    val iff_URI :       UriManager.uri
    val not_URI :       UriManager.uri
    val or_URI :        UriManager.uri
    val sym_eq_URI :    UriManager.uri
    val trans_eq_URI :  UriManager.uri
    val true_URI :      UriManager.uri

    val and_SURI :      string
    val eq_SURI :       string
    val ex_SURI :       string
    val iff_SURI :      string
    val not_SURI :      string
    val or_SURI :       string

    val and_XURI :      string
    val eq_XURI :       string
    val ex_XURI :       string
    val or_XURI :       string
  end

module Datatypes :
  sig
    val bool_URI :      UriManager.uri
    val nat_URI :       UriManager.uri

    val trueb :         Cic.term
    val falseb :        Cic.term
    val zero :          Cic.term
    val succ :          Cic.term
  end

module Reals :
  sig
    val pow_URI :       UriManager.uri
    val r0_URI :        UriManager.uri
    val r1_URI :        UriManager.uri
    val rdiv_URI :      UriManager.uri
    val rge_URI :       UriManager.uri
    val rgt_URI :       UriManager.uri
    val rinv_r1_URI :   UriManager.uri
    val rinv_URI :      UriManager.uri
    val rle_URI :       UriManager.uri
    val rlt_URI :       UriManager.uri
    val rminus_URI :    UriManager.uri
    val rmult_URI :     UriManager.uri
    val ropp_URI :      UriManager.uri
    val rplus_URI :     UriManager.uri
    val rtheory_URI :   UriManager.uri
    val r_URI :         UriManager.uri

    val r0_SURI :       string
    val r1_SURI :       string
    val rdiv_SURI :     string
    val rge_SURI :      string
    val rgt_SURI :      string
    val rinv_SURI :     string
    val rle_SURI :      string
    val rlt_SURI :      string
    val rminus_SURI :   string
    val rmult_SURI :    string
    val ropp_SURI :     string
    val rplus_SURI :    string

    val r0 :            Cic.term
    val r1 :            Cic.term
    val r :             Cic.term
    val rmult :         Cic.term
    val ropp :          Cic.term
    val rplus :         Cic.term
    val rtheory :       Cic.term
  end

module Peano :
  sig
    val ge_URI :        UriManager.uri
    val gt_URI :        UriManager.uri
    val le_URI :        UriManager.uri
    val lt_URI :        UriManager.uri
    val minus_URI :     UriManager.uri
    val mult_URI :      UriManager.uri
    val plus_URI :      UriManager.uri
    val pred_URI :      UriManager.uri

    val ge_SURI :       string
    val gt_SURI :       string
    val le_SURI :       string
    val lt_SURI :       string
    val minus_SURI :    string
    val mult_SURI :     string
    val plus_SURI :     string

    val le_XURI :       string

    val mult :          Cic.term
    val plus :          Cic.term
    val pred :          Cic.term
  end

module BinPos :
  sig
    val pminus_URI :    UriManager.uri
    val pmult_URI :     UriManager.uri
    val positive_URI :  UriManager.uri
    val pplus_URI :     UriManager.uri

    val pminus_SURI :   string
    val pmult_SURI :    string
    val positive_SURI : string
    val pplus_SURI :    string

    val pminus :        Cic.term
    val pmult :         Cic.term
    val pplus :         Cic.term
    val xH :            Cic.term
    val xI :            Cic.term
    val xO :            Cic.term
  end

module BinInt :
  sig
    val zminus_URI :    UriManager.uri
    val zmult_URI :     UriManager.uri
    val zopp_URI :      UriManager.uri
    val zplus_URI :     UriManager.uri
    val zpower_URI :    UriManager.uri
    val z_URI :         UriManager.uri

    val zminus_SURI :   string
    val zopp_SURI :     string
    val zplus_SURI :    string
    val z_SURI :        string

    val z0 :            Cic.term
    val zminus :        Cic.term
    val zmult :         Cic.term
    val zneg :          Cic.term
    val zopp :          Cic.term
    val zplus :         Cic.term
    val zpos :          Cic.term
  end

val build_bin_pos : int -> Cic.term
val build_nat :     int -> Cic.term
val build_real :    int -> Cic.term

