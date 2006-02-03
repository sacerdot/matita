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

set "baseuri" "cic:/matita/LAMBDA-TYPES/terms_defs".

include "legacy/coq.ma".

alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias id "S" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/2)".
alias id "O" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/1)".
alias id "plus" = "cic:/Coq/Init/Peano/plus.con".
alias id "lt" = "cic:/Coq/Init/Peano/lt.con".
alias id "le" = "cic:/Coq/Init/Peano/le.ind#xpointer(1/1)".

inductive B : Set \def 
   | Void: B
   | Abbr: B
   | Abst: B.

inductive F : Set \def 
   | Appl: F 
   | Cast: F.

inductive W : Set \def 
   | Bind: B \to W 
   | Flat: F \to W.

inductive T (A:Set) (N:Set) : Set \def
   | TSort: A \to nat \to (T A N) 
   | TLRef: A \to nat \to (T A N)
   | TWag : A \to W \to (T A N) \to (T A N) \to (T A N)
   | TGRef: A \to N \to (T A N).
   
record X (A:Set) (N:Set) : Type \def {
   get_gref: N \to B \to (T A N) \to Prop
}.
