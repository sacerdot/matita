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

set "baseuri" "cic:/matita/PREDICATIVE-TOPOLOGY/class_eq".

include "class_defs.ma".

theorem ceq_trans: \forall C. \xforall c1,c2. ceq C c1 c2 \to 
                   \xforall c3. ceq ? c2 c3 \to ceq ? c1 c3.
intros.

(*
apply ceq_intro; apply cle_trans; [|auto new timeout=100|auto new timeout=100||auto new timeout=100|auto new timeout=100].
qed.

theorem ceq_sym: \forall C,c1,c2. ceq C c1 c2 \to ceq C c2 c1.
intros; elim H; clear H.; auto new timeout=100.
qed.
*)
