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



include "NPlusList/defs.ma".
(*
axiom npluslist_gen_cons: \forall l,q,r. 
                            NPlusList (cons ? l q) r \to
                            \exists p. NPlusList l p \land NPlus p q r.
(* 
 intros. inversion H; clear H; intros;
 [ id
 | destruct.
*)

theorem npluslist_inj_2: \forall ns1,ns2,n. 
                         NPlusListEq (cons ? ns1 n) (cons ? ns2 n) \to
                         NPlusListEq ns1 ns2.
 unfold NPlusListEq. intros. decompose.
 lapply linear npluslist_gen_cons to H. decompose.
 lapply linear npluslist_gen_cons to H2. decompose.
*)