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

set "baseuri" "cic:/matita/tests/decompose".
include "../legacy/coq.ma".
alias symbol "and" (instance 0) = "Coq's logical and".
alias symbol "or" (instance 0) = "Coq's logical or".



theorem stupid: 
  \forall a,b,c:Prop.
  (a \land c \lor b \land c) \to (c \land (b \lor a)).
  intros.decompose H.split.assumption.right.assumption.
  split.assumption.left.assumption.qed.


