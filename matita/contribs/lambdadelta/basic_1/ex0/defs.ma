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

(* This file was automatically generated: do not edit *********************)

include "Basic-1/A/defs.ma".

include "Basic-1/G/defs.ma".

definition gz:
 G
\def
 mk_G S lt_n_Sn.

inductive leqz: A \to (A \to Prop) \def
| leqz_sort: \forall (h1: nat).(\forall (h2: nat).(\forall (n1: nat).(\forall 
(n2: nat).((eq nat (plus h1 n2) (plus h2 n1)) \to (leqz (ASort h1 n1) (ASort 
h2 n2))))))
| leqz_head: \forall (a1: A).(\forall (a2: A).((leqz a1 a2) \to (\forall (a3: 
A).(\forall (a4: A).((leqz a3 a4) \to (leqz (AHead a1 a3) (AHead a2 a4))))))).

