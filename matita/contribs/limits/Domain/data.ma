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

include "Domain/defs.ma".

(* QUANTIFICATION DOMAINS
   - Here we define some useful domains based on data types.
*)

definition DBool: Domain ≝
   mk_Domain (
      mk_Class bool (true_f ?) (eq ?) (true_fw ? ?) (true_bw ? ?)
   ).
(*
definition dbool_ixfam : \forall (C:Class). C \to C \to (DBool \to C) \def
   \lambda C,c0,c1,b.
   match b in bool with 
      [ false \Rightarrow c0
      | true \Rightarrow c1
      ].
*)
definition DVoid: Domain ≝
   mk_Domain (
      mk_Class void (true_f ?) (eq ?) (true_fw ? ?) (true_bw ? ?)
   ).
(*
definition dvoid_ixfam : \forall (C:Class). (DVoid \to C) \def
   \lambda C,v.
   match v in void with [].
*)
