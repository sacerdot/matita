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

(* STATO: NON COMPILA: dev'essere aggiornato *)

set "baseuri" "cic:/matita/PREDICATIVE-TOPOLOGY/subset_defs".

include "domain_defs.ma".

(* SUBSETS
   - We use predicative subsets coded as propositional functions
     according to G.Sambin and S.Valentini "Toolbox" 
*)

definition Subset \def \lambda (D:Domain). D \to Prop.

(* subset membership (epsilon) *)
definition sin : \forall D. Subset D \to D \to Prop \def
   \lambda (D:Domain). \lambda U,d. cin D d \and U d.

(* subset top (full subset) *)
definition stop \def \lambda (D:Domain). true_f D.

(* subset bottom (empty subset) *)
definition sbot \def \lambda (D:Domain). false_f D.

(* subset and (binary intersection) *)
definition sand: \forall D. Subset D \to Subset D \to Subset D \def 
   \lambda D,U1,U2,d. U1 d \land U2 d. 

(* subset or (binary union) *)
definition sor: \forall D. Subset D \to Subset D \to Subset D \def 
   \lambda D,U1,U2,d. U1 d \lor U2 d. 

(* subset less or equal (inclusion) *) 
definition sle: \forall D. Subset D \to Subset D \to Prop \def 
   \lambda D,U1,U2. \iforall d. U1 d \to U2 d. 

(* subset overlap *) 
definition sover: \forall D. Subset D \to Subset D \to Prop \def 
   \lambda D,U1,U2. \iexists d. U1 d \land U2 d. 

(* coercions **************************************************************)

(*
(* the class of the subsets of a domain (not an implicit coercion) *)
definition class_of_subsets_of \def
   \lambda D. mk_Class (Subset D) (true_f ?) (sle ?). 
*)

(* the domain built upon a subset (not an implicit coercion) *)
definition domain_of_subset: \forall D. Subset D \to Domain \def
   \lambda (D:Domain). \lambda U. 
   mk_Domain (mk_Class D (sin D U) (cle1 D)).

(* the full subset of a domain *)
coercion stop.
